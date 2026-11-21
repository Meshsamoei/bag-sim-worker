// ================================================================
//  IN-MEMORY BUFFERS
// ================================================================
const feedBuffer = [];
const FEED_MAX = 60;
let feedSeq = 0;

function pushFeed(entry) {
    feedBuffer.unshift(entry);
    while (feedBuffer.length > FEED_MAX) feedBuffer.pop();
}

// Live teller queues: teller_id -> { slips, total_pool, updated_at }
const liveQueues = new Map();

// ================================================================
//  ROUND TIMING CONSTANTS (shared)
// ================================================================
const COUNTDOWN_MS = 8000;
const CRASH_TAIL_MS = 5000;
const GROWTH_RATE = 0.038;

// Compute round timing anchors (epoch ms) for internal phase logic.
// roundEndsAt is computed server-side only and MUST NOT be returned to clients.
function computeRoundTiming(round) {
    const createdAt = new Date(
        round.created_at.includes('T') ? round.created_at : round.created_at.replace(' ', 'T') + 'Z'
    ).getTime();
    const timeToCrashMs = (Math.log(round.crash_multiplier) / GROWTH_RATE) * 1000;
    const climbStartAt = createdAt + COUNTDOWN_MS;
    const roundEndsAt = climbStartAt + timeToCrashMs;
    return { createdAt, climbStartAt, roundEndsAt, timeToCrashMs };
}

// Resolve win/bust for local round bets against the crash multiplier.
// A bet wins when exit_multiplier <= crash_multiplier (cashed out before crash).
function resolveLocalBets(round, bets) {
    const crash = Number(round.crash_multiplier) || 1.0;
    return (bets || []).map(b => {
        const exitMult = Number(b.multiplier) || 1.0;
        const isWin = exitMult <= crash;
        const payout = isWin ? Number(b.stake) * exitMult : 0;
        return {
            ...b,
            crash_multiplier: crash,
            resolved: true,
            won: isWin,
            payout: payout,
            status: b.status === 'settled' ? 'settled' : (isWin ? 'won' : 'busted')
        };
    });
}

// ================================================================
//  CRYPTO HELPERS
// ================================================================
function bufferToHex(buffer) {
    return Array.from(new Uint8Array(buffer))
        .map(b => b.toString(16).padStart(2, '0'))
        .join('');
}

function hexToBuffer(hex) {
    const bytes = new Uint8Array(hex.length / 2);
    for (let i = 0; i < bytes.length; i++) {
        bytes[i] = parseInt(hex.substr(i * 2, 2), 16);
    }
    return bytes;
}

async function sha256(message) {
    const msgBuffer = new TextEncoder().encode(message);
    const hashBuffer = await crypto.subtle.digest('SHA-256', msgBuffer);
    return bufferToHex(hashBuffer);
}

function generateServerSeed() {
    const array = new Uint8Array(32);
    crypto.getRandomValues(array);
    return bufferToHex(array);
}

function generateMultiplier() {
    const array = new Uint32Array(1);
    crypto.getRandomValues(array);
    const h = array[0] / 4294967296;
    let crashMultiplier = Math.floor((100 * 2.71828 - h) / (1 - h)) / 100;
    if (crashMultiplier < 1.0) crashMultiplier = 1.00;
    return Math.max(1.01, parseFloat(crashMultiplier.toFixed(2)));
}

// ================================================================
//  AUTH HELPERS
// ================================================================
async function hashPassword(password, saltHex) {
    const enc = new TextEncoder();
    const keyMaterial = await crypto.subtle.importKey(
        'raw',
        enc.encode(password),
        { name: 'PBKDF2' },
        false,
        ['deriveBits']
    );
    const bits = await crypto.subtle.deriveBits(
        {
            name: 'PBKDF2',
            salt: hexToBuffer(saltHex),
            iterations: 100000,
            hash: 'SHA-256'
        },
        keyMaterial,
        256
    );
    return bufferToHex(bits);
}

function generateSaltHex() {
    const arr = new Uint8Array(16);
    crypto.getRandomValues(arr);
    return bufferToHex(arr);
}

function generateToken() {
    const arr = new Uint8Array(32);
    crypto.getRandomValues(arr);
    return bufferToHex(arr);
}

// Normalize Kenyan phone numbers to +254XXXXXXXXX
// Accepts: 0712345678, 0112345678, +254712345678, 254712345678, 712345678
function normalizePhone(raw) {
    if (!raw) return null;
    const digits = String(raw).replace(/[^\d+]/g, '');
    let s = digits.replace(/^\+/, '');

    // 0712345678 / 0112345678 -> 254712345678
    if (/^0(7|1)\d{8}$/.test(s)) {
        s = '254' + s.substring(1);
    }
    // 712345678 (9 digits starting 7 or 1) -> 254712345678
    else if (/^(7|1)\d{8}$/.test(s)) {
        s = '254' + s;
    }
    // 254712345678 already good
    if (/^254(7|1)\d{8}$/.test(s)) {
        return '+' + s;
    }
    return null;
}

// Generate a procedural shop_id from phone + display name so no one ever gets 'default'
function generateShopId(phone, displayName) {
    const prefix = 'SHOP';
    const phoneDigits = (phone || '').replace(/\D/g, '').slice(-4);
    const nameBits = (displayName || 'player').toLowerCase().replace(/[^a-z0-9]/g, '').slice(0, 6);
    const randomBits = Math.floor(Math.random() * 65536).toString(16).padStart(4, '0');
    return `${prefix}-${nameBits}-${phoneDigits}-${randomBits}`;
}

function isValidPassword(pw) {
    return typeof pw === 'string' && pw.length >= 6 && pw.length <= 64;
}

async function createSession(db, userId) {
    const token = generateToken();
    const expiresAt = new Date(Date.now() + 30 * 24 * 60 * 60 * 1000).toISOString(); // 30 days
    await db.prepare(
        `INSERT INTO sessions (token, user_id, expires_at) VALUES (?, ?, ?)`
    ).bind(token, userId, expiresAt).run();
    return { token, expires_at: expiresAt };
}

async function getSessionUser(db, token) {
    if (!token) return null;
    const row = await db.prepare(
        `SELECT s.token, s.expires_at, u.id, u.phone, u.display_name, u.role, u.shop_id
         FROM sessions s JOIN users u ON u.id = s.user_id
         WHERE s.token = ?`
    ).bind(token).first();
    if (!row) return null;
    if (new Date(row.expires_at).getTime() < Date.now()) {
        await db.prepare(`DELETE FROM sessions WHERE token = ?`).bind(token).run();
        return null;
    }
    return row;
}

function extractToken(request) {
    const h = request.headers.get('Authorization') || '';
    const m = h.match(/^Bearer\s+(.+)$/i);
    return m ? m[1] : null;
}

function publicUser(u) {
    return {
        id: u.id,
        phone: u.phone,
        display_name: u.display_name,
        role: u.role,
        shop_id: u.shop_id || 'default'
    };
}

// ================================================================
//  ROUND DATA GENERATION
// ================================================================
async function generateRoundData(db, isGlobal = false, totalPool = 0, shopId = 'default') {
    const timestampTag = new Date().toISOString();
    const clientSeed = isGlobal ?
        `global_round_t_${timestampTag}` :
        `local_pool_${totalPool.toFixed(2)}_t_${timestampTag}`;

    const serverSeed = generateServerSeed();
    const serverSeedHash = await sha256(serverSeed);
    const crashMultiplier = generateMultiplier();

    if (isGlobal) {
        const stmt = db.prepare(
            `INSERT INTO global_rounds (crash_multiplier, server_seed, server_seed_hash, client_seed, created_at) VALUES (?, ?, ?, ?, datetime('now'))`
        ).bind(crashMultiplier, serverSeed, serverSeedHash, clientSeed);
        const res = await stmt.run();

        const row = await db.prepare(`SELECT id, crash_multiplier, server_seed, server_seed_hash, client_seed, created_at FROM global_rounds WHERE id = ?`).bind(res.meta.last_row_id).first();
        return row;
    } else {
        const stmt = db.prepare(
            `INSERT INTO local_rounds (crash_multiplier, total_pool, server_seed, server_seed_hash, client_seed, shop_id, is_demo, created_at) VALUES (?, ?, ?, ?, ?, ?, 0, datetime('now'))`
        ).bind(crashMultiplier, totalPool, serverSeed, serverSeedHash, clientSeed, shopId);
        const res = await stmt.run();

        const row = await db.prepare(`SELECT id, crash_multiplier, total_pool, server_seed, server_seed_hash, client_seed, shop_id, created_at FROM local_rounds WHERE id = ?`).bind(res.meta.last_row_id).first();
        return row;
    }
}

// Background cron check for autonomous global rounds
async function checkAndAdvanceGlobalRound(db) {
    const round = await db.prepare(`SELECT id, crash_multiplier, created_at FROM global_rounds ORDER BY id DESC LIMIT 1`).first();
    const now = Date.now();

    let shouldCreateNew = false;
    if (!round) {
        shouldCreateNew = true;
    } else {
        const { createdAt, roundEndsAt } = computeRoundTiming(round);
        const totalCycleMs = (roundEndsAt - createdAt) + CRASH_TAIL_MS;
        if ((now - createdAt) >= totalCycleMs) {
            shouldCreateNew = true;
        }
    }

    if (shouldCreateNew) {
        await generateRoundData(db, true, 0);
    }
}

// ================================================================
//  MAIN EXPORT
// ================================================================
export default {
    async fetch(request, env, ctx) {
        const url = new URL(request.url);
        const path = url.pathname;

        // CORS headers
        const corsHeaders = {
            'Access-Control-Allow-Origin': '*',
            'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
            'Access-Control-Allow-Headers': 'Content-Type, Authorization',
            'Cache-Control': 'no-store, no-cache, must-revalidate'
        };
        if (request.method === 'OPTIONS') {
            return new Response(null, { headers: corsHeaders });
        }

        try {
            if (path === '/' && request.method === 'GET') {
                return Response.json({ success: 'Bag-Sim Engine Active' }, { status: 200, headers: corsHeaders });
            }

            // ================================================================
            //  AUTH ROUTES
            // ================================================================

            // ROUTE: /api/auth/register
            if (path === '/api/auth/register' && request.method === 'POST') {
                const body = await request.json().catch(() => ({}));
                const phone = normalizePhone(body.phone);
                const password = body.password;
                const displayName = (body.display_name || '').toString().trim().substring(0, 40) || null;
                const role = ['teller', 'cashier', 'admin'].includes(body.role) ? body.role : 'cashier';
                const shopId = body.shop_id && String(body.shop_id).trim() && String(body.shop_id).trim() !== 'default'
                    ? String(body.shop_id).trim().substring(0, 64)
                    : generateShopId(phone, displayName);

                if (!phone) {
                    return Response.json(
                        { error: 'Invalid phone number. Use 07XX, 01XX, +254... or 254...' },
                        { status: 400, headers: corsHeaders }
                    );
                }
                if (!isValidPassword(password)) {
                    return Response.json(
                        { error: 'Password must be 6–64 characters.' },
                        { status: 400, headers: corsHeaders }
                    );
                }

                const existing = await env.DB.prepare(`SELECT id FROM users WHERE phone = ?`).bind(phone).first();
                if (existing) {
                    return Response.json(
                        { error: 'Phone number already registered.' },
                        { status: 409, headers: corsHeaders }
                    );
                }

                const salt = generateSaltHex();
                const hash = await hashPassword(password, salt);

                const res = await env.DB.prepare(
                    `INSERT INTO users (phone, password_hash, password_salt, display_name, role, shop_id) VALUES (?, ?, ?, ?, ?, ?)`
                ).bind(phone, hash, salt, displayName, role, shopId).run();

                const userId = res.meta.last_row_id;
                const session = await createSession(env.DB, userId);

                return Response.json({
                    success: true,
                    token: session.token,
                    expires_at: session.expires_at,
                    user: { id: userId, phone, display_name: displayName, role, shop_id: shopId }
                }, { headers: corsHeaders });
            }

            // ROUTE: /api/auth/login
            if (path === '/api/auth/login' && request.method === 'POST') {
                const body = await request.json().catch(() => ({}));
                const phone = normalizePhone(body.phone);
                const password = body.password;

                if (!phone || !password) {
                    return Response.json(
                        { error: 'Phone and password are required.' },
                        { status: 400, headers: corsHeaders }
                    );
                }

                const user = await env.DB.prepare(
                    `SELECT id, phone, password_hash, password_salt, display_name, role, shop_id FROM users WHERE phone = ?`
                ).bind(phone).first();

                if (!user) {
                    return Response.json(
                        { error: 'Invalid phone or password.' },
                        { status: 401, headers: corsHeaders }
                    );
                }

                const candidate = await hashPassword(password, user.password_salt);
                if (candidate !== user.password_hash) {
                    return Response.json(
                        { error: 'Invalid phone or password.' },
                        { status: 401, headers: corsHeaders }
                    );
                }

                const session = await createSession(env.DB, user.id);
                await env.DB.prepare(
                    `UPDATE users SET last_login_at = datetime('now') WHERE id = ?`
                ).bind(user.id).run();

                return Response.json({
                    success: true,
                    token: session.token,
                    expires_at: session.expires_at,
                    user: publicUser(user)
                }, { headers: corsHeaders });
            }

            // ROUTE: /api/auth/logout
            if (path === '/api/auth/logout' && request.method === 'POST') {
                const token = extractToken(request);
                if (token) {
                    await env.DB.prepare(`DELETE FROM sessions WHERE token = ?`).bind(token).run();
                }
                return Response.json({ success: true }, { headers: corsHeaders });
            }

            // ROUTE: /api/auth/me
            if (path === '/api/auth/me' && request.method === 'GET') {
                const token = extractToken(request);
                const user = await getSessionUser(env.DB, token);
                if (!user) {
                    return Response.json({ error: 'Not authenticated.' }, { status: 401, headers: corsHeaders });
                }
                return Response.json({
                    success: true,
                    user: publicUser(user)
                }, { headers: corsHeaders });
            }

            // ROUTE: /api/auth/change-password
            if (path === '/api/auth/change-password' && request.method === 'POST') {
                const token = extractToken(request);
                const sessionUser = await getSessionUser(env.DB, token);
                if (!sessionUser) {
                    return Response.json({ error: 'Not authenticated.' }, { status: 401, headers: corsHeaders });
                }

                const body = await request.json().catch(() => ({}));
                const oldPassword = body.old_password;
                const newPassword = body.new_password;

                if (!isValidPassword(newPassword)) {
                    return Response.json({ error: 'New password must be 6–64 characters.' }, { status: 400, headers: corsHeaders });
                }

                const row = await env.DB.prepare(
                    `SELECT password_hash, password_salt FROM users WHERE id = ?`
                ).bind(sessionUser.id).first();

                const candidate = await hashPassword(oldPassword, row.password_salt);
                if (candidate !== row.password_hash) {
                    return Response.json({ error: 'Current password is incorrect.' }, { status: 401, headers: corsHeaders });
                }

                const newSalt = generateSaltHex();
                const newHash = await hashPassword(newPassword, newSalt);
                await env.DB.prepare(
                    `UPDATE users SET password_hash = ?, password_salt = ? WHERE id = ?`
                ).bind(newHash, newSalt, sessionUser.id).run();

                // Invalidate all other sessions for this user
                await env.DB.prepare(
                    `DELETE FROM sessions WHERE user_id = ? AND token != ?`
                ).bind(sessionUser.id, token).run();

                return Response.json({ success: true }, { headers: corsHeaders });
            }

            // ROUTE: /api/auth/users  (admin only — list all users)
            if (path === '/api/auth/users' && request.method === 'GET') {
                const token = extractToken(request);
                const sessionUser = await getSessionUser(env.DB, token);
                if (!sessionUser) {
                    return Response.json({ error: 'Not authenticated.' }, { status: 401, headers: corsHeaders });
                }
                if (sessionUser.role !== 'admin') {
                    return Response.json({ error: 'Admin role required.' }, { status: 403, headers: corsHeaders });
                }

                const { results } = await env.DB.prepare(
                    `SELECT id, phone, display_name, role, shop_id, created_at, last_login_at FROM users ORDER BY id DESC`
                ).all();

                return Response.json({
                    success: true,
                    users: results || []
                }, { headers: corsHeaders });
            }

            // ROUTE: /api/auth/shop-profile  (lists workers in the caller's shop)
            if (path === '/api/auth/shop-profile' && request.method === 'GET') {
                const token = extractToken(request);
                const sessionUser = await getSessionUser(env.DB, token);
                if (!sessionUser) {
                    return Response.json({ error: 'Not authenticated.' }, { status: 401, headers: corsHeaders });
                }
                const shopId = sessionUser.shop_id || 'default';

                const { results } = await env.DB.prepare(
                    `SELECT id, phone, display_name, role, shop_id, created_at, last_login_at FROM users WHERE shop_id = ? ORDER BY role ASC, id DESC`
                ).bind(shopId).all();

                return Response.json({
                    success: true,
                    shop_id: shopId,
                    workers: results || []
                }, { headers: corsHeaders });
            }

            // ================================================================
            //  LAUNCH LOCAL ROUND  (teller/admin/cashier)
            // ================================================================
            if (path === '/api/launch' && request.method === 'POST') {
                const token = extractToken(request);
                const sessionUser = await getSessionUser(env.DB, token);
                if (!sessionUser) {
                    return Response.json({ error: 'Authentication required.' }, { status: 401, headers: corsHeaders });
                }
                if (sessionUser.role !== 'teller' && sessionUser.role !== 'admin' && sessionUser.role !== 'cashier') {
                    return Response.json({ error: 'Teller role required.' }, { status: 403, headers: corsHeaders });
                }

                const body = await request.json().catch(() => ({}));
                const totalPool = Number(body.total_pool) || 0.0;
                const isGlobal = body.is_global || false;
                const slips = body.slips || [];
                const shopId = String(body.shop_id || sessionUser.shop_id || 'default').substring(0, 64);

                // Non-admin must operate within their own shop
                if (sessionUser.role !== 'admin' && shopId !== sessionUser.shop_id) {
                    return Response.json({ error: 'Cannot launch rounds outside your shop.' }, { status: 403, headers: corsHeaders });
                }

                if (!isGlobal && (!Array.isArray(slips) || slips.length === 0)) {
                    return Response.json(
                        { error: 'Cannot launch local round: No slips registered in the queue.' },
                        { status: 400, headers: corsHeaders }
                    );
                }

                const round = await generateRoundData(env.DB, isGlobal, totalPool, shopId);
                const roundId = round.id;

                for (const slip of slips) {
                    const ticketCode = `TKT-${Math.floor(1000 + Math.random() * 9000)}`;
                    await env.DB.prepare(
                        `INSERT INTO local_bets (round_id, ticket_code, customer_name, stake, multiplier, status, created_by, shop_id) VALUES (?, ?, ?, ?, ?, 'pending', ?, ?)`
                    ).bind(
                        roundId,
                        ticketCode,
                        (slip.customer_name || slip.name || 'Walk-in Player').substring(0, 32),
                        Number(slip.stake),
                        Number(slip.multiplier || 1.00),
                        sessionUser.id,
                        shopId
                    ).run();
                }

                return Response.json({
                    success: true,
                    round_id: roundId,
                    shop_id: shopId,
                    server_seed_hash: round.server_seed_hash
                }, { headers: corsHeaders });
            }

            // ================================================================
            //  GLOBAL BET PLACE  (any player, global mode)
            // ================================================================
            if (path === '/api/bet/place' && request.method === 'POST') {
                const body = await request.json().catch(() => ({}));
                const { roundId, name, stake, exitMultiplier } = body;

                if (!roundId || !stake || !exitMultiplier) {
                    return Response.json({ error: 'Missing required bet parameters' }, { status: 400, headers: corsHeaders });
                }

                const round = await env.DB.prepare(`SELECT * FROM global_rounds WHERE id = ?`).bind(roundId).first();
                if (!round) {
                    return Response.json({ error: 'Global round not found' }, { status: 404, headers: corsHeaders });
                }

                // Only allow bets during countdown phase
                const timing = computeRoundTiming(round);
                const now = Date.now();
                if (now >= timing.climbStartAt) {
                    return Response.json({ error: 'Betting closed — round already in progress' }, { status: 403, headers: corsHeaders });
                }

                const ticketCode = `TKT-${Math.floor(1000 + Math.random() * 9000)}`;

                try {
                    const stmt = env.DB.prepare(
                        `INSERT INTO global_bets (round_id, ticket_code, customer_name, stake, exit_multiplier, status, created_at) VALUES (?, ?, ?, ?, ?, 'pending', datetime('now'))`
                    ).bind(
                        roundId,
                        ticketCode,
                        (name || 'Player').substring(0, 32),
                        Number(stake),
                        Number(exitMultiplier)
                    );
                    const res = await stmt.run();

                    return Response.json({
                        success: true,
                        ticket_id: ticketCode,
                        bet_db_id: res.meta.last_row_id,
                        round_id: roundId
                    }, { headers: corsHeaders });
                } catch (e) {
                    return Response.json({ error: 'Bet placement failed: ' + e.message }, { status: 500, headers: corsHeaders });
                }
            }

            // ================================================================
            //  STATE / HISTORY / GLOBAL FEED  (public read-only)
            // ================================================================
            if (path === '/api/state' && request.method === 'GET') {
                const mode = url.searchParams.get('mode') || 'local';
                const isGlobal = mode === 'global';
                const tableName = isGlobal ? 'global_rounds' : 'local_rounds';
                const shopId = url.searchParams.get('shop_id') || 'default';

                let query, params;
                if (isGlobal) {
                    query = `SELECT id, crash_multiplier, server_seed_hash, client_seed, created_at FROM ${tableName} ORDER BY id DESC LIMIT 1`;
                    params = [];
                } else {
                    query = `SELECT id, crash_multiplier, total_pool, server_seed_hash, client_seed, created_at FROM ${tableName} WHERE shop_id = ? ORDER BY id DESC LIMIT 1`;
                    params = [shopId];
                }

                let round = await env.DB.prepare(query).bind(...params).first();

                if (isGlobal) {
                    const now = Date.now();
                    let shouldCreateNew = false;

                    if (!round) {
                        shouldCreateNew = true;
                    } else {
                        const { createdAt, roundEndsAt } = computeRoundTiming(round);
                        const totalCycleMs = (roundEndsAt - createdAt) + CRASH_TAIL_MS;
                        if ((now - createdAt) >= totalCycleMs) {
                            shouldCreateNew = true;
                        }
                    }

                    if (shouldCreateNew) {
                        round = await generateRoundData(env.DB, true, 0);
                    }
                }

                let phase = 'idle';
                let climbStartAt = null;
                let crashRevealed = null;

                if (round) {
                    const timing = computeRoundTiming(round);
                    climbStartAt = timing.climbStartAt;
                    // roundEndsAt computed server-side only; never sent to client

                    const now = Date.now();

                    if (now < climbStartAt) {
                        phase = 'countdown';
                    } else if (now < timing.roundEndsAt) {
                        phase = 'climbing';
                    } else {
                        phase = 'crashed';
                        crashRevealed = round.crash_multiplier;
                    }
                }

                const publicRound = round ? {
                    id: round.id,
                    shop_id: round.shop_id || 'default',
                    total_pool: round.total_pool || 0,
                    server_seed_hash: round.server_seed_hash,
                    client_seed: round.client_seed,
                    created_at: round.created_at.includes('T') ? round.created_at : round.created_at.replace(' ', 'T') + 'Z',
                    crash_multiplier: crashRevealed
                } : null;

                return Response.json({
                    server_time: new Date().toISOString(),
                    phase,
                    climb_start_at: climbStartAt,
                    // round_ends_at intentionally omitted — prevents client-side crash-time exposure
                    countdown_ms: COUNTDOWN_MS,
                    tail_ms: CRASH_TAIL_MS,
                    round: publicRound,
                    live_bets: []
                }, { headers: corsHeaders });
            }

            if (path === '/api/history' && request.method === 'GET') {
                const mode = url.searchParams.get('mode') || 'local';
                const isGlobal = mode === 'global';
                const tableName = mode === 'global' ? 'global_rounds' : 'local_rounds';
                const shopId = url.searchParams.get('shop_id') || 'default';
                const selectColumns = mode === 'global' ?
                    'id, crash_multiplier, server_seed, server_seed_hash, client_seed, created_at' :
                    'id, crash_multiplier, total_pool, server_seed, server_seed_hash, client_seed, shop_id, created_at';

                let query, params;
                if (isGlobal) {
                    query = `SELECT ${selectColumns} FROM ${tableName} ORDER BY id DESC`;
                    params = [];
                } else {
                    query = `SELECT ${selectColumns} FROM ${tableName} WHERE shop_id = ? ORDER BY id DESC`;
                    params = [shopId];
                }

                const { results } = await env.DB.prepare(query).bind(...params).all();
                let filtered = results || [];

                // Hide latest round while still in-flight
                if (filtered.length > 0) {
                    const latest = filtered[0];
                    const { createdAt, roundEndsAt } = computeRoundTiming(latest);
                    const totalCycleMs = (roundEndsAt - createdAt) + CRASH_TAIL_MS;
                    if ((Date.now() - createdAt) < totalCycleMs) {
                        filtered = filtered.slice(1);
                    }
                }

                return Response.json(filtered.map(r => ({
                    ...r,
                    created_at: r.created_at.includes('T') ? r.created_at : r.created_at.replace(' ', 'T') + 'Z'
                })), { headers: corsHeaders });
            }

            if (path === '/api/global/next-start' && request.method === 'GET') {
                const round = await env.DB.prepare(`SELECT id, crash_multiplier, created_at FROM global_rounds ORDER BY id DESC LIMIT 1`).first();

                if (!round) {
                    return Response.json({
                        server_time: new Date().toISOString(),
                        next_start_ms: 0,
                        phase: 'idle',
                        current_round_id: null,
                        countdown_ms: COUNTDOWN_MS
                    }, { headers: corsHeaders });
                }

                const { climbStartAt, roundEndsAt } = computeRoundTiming(round);
                const now = Date.now();
                const nextStartsAt = roundEndsAt + CRASH_TAIL_MS;

                let phase, nextStartMs;
                if (now < climbStartAt) {
                    phase = 'countdown';
                    nextStartMs = 0;
                } else if (now < roundEndsAt) {
                    phase = 'climbing';
                    nextStartMs = Math.max(0, nextStartsAt - now);
                } else {
                    phase = 'crashed';
                    nextStartMs = Math.max(0, nextStartsAt - now);
                }

                return Response.json({
                    server_time: new Date().toISOString(),
                    next_start_ms: nextStartMs,
                    phase,
                    current_round_id: round.id,
                    countdown_ms: COUNTDOWN_MS
                }, { headers: corsHeaders });
            }

            // ================================================================
            //  FEED (in-memory)
            // ================================================================
            if (path === '/api/feed/push' && request.method === 'POST') {
                const body = await request.json().catch(() => ({}));
                const { name, stake, roundId } = body;
                if (!stake || stake <= 0) return Response.json({ error: 'invalid stake' }, { status: 400, headers: corsHeaders });

                const id = ++feedSeq;
                pushFeed({
                    id,
                    name: (name || 'You').substring(0, 24),
                    stake: Number(stake),
                    multiplier: null,
                    status: 'live',
                    roundId: roundId || null,
                    ts: Date.now()
                });
                return Response.json({ success: true, id }, { headers: corsHeaders });
            }

            if (path === '/api/feed/settle' && request.method === 'POST') {
                const body = await request.json().catch(() => ({}));
                const { id, status, multiplier } = body;
                if (!id || !['cashed', 'busted'].includes(status)) {
                    return Response.json({ error: 'invalid payload' }, { status: 400, headers: corsHeaders });
                }
                const e = feedBuffer.find(x => x.id === Number(id));
                if (e) {
                    e.status = status;
                    e.multiplier = Number(multiplier) || null;
                }
                return Response.json({ success: true }, { headers: corsHeaders });
            }

            if (path === '/api/feed/recent' && request.method === 'GET') {
                return Response.json({
                    server_time: new Date().toISOString(),
                    bets: feedBuffer.slice(0, 40)
                }, { headers: corsHeaders });
            }

            // ================================================================
            //  LIVE TELLER QUEUE BROADCAST
            // ================================================================
            if (path === '/api/queue/publish' && request.method === 'POST') {
                const body = await request.json().catch(() => ({}));
                const tellerId = String(body.teller_id || 'default').substring(0, 32);
                const slips = Array.isArray(body.slips) ? body.slips.slice(0, 50) : [];
                const totalPool = slips.reduce((s, x) => s + (Number(x.stake) || 0), 0);

                liveQueues.set(tellerId, {
                    slips: slips.map(s => ({
                        ticket_code: String(s.ticket_code || '').substring(0, 16),
                        stake: Number(s.stake) || 0,
                        multiplier: Number(s.multiplier) || 1.0
                    })),
                    total_pool: totalPool,
                    updated_at: Date.now()
                });

                return Response.json({ success: true, count: slips.length }, { headers: corsHeaders });
            }

            if (path === '/api/queue/live' && request.method === 'GET') {
                const STALE_MS = 15000;
                const now = Date.now();
                const tellers = [];

                for (const [tellerId, q] of liveQueues.entries()) {
                    if (now - q.updated_at > STALE_MS) {
                        liveQueues.delete(tellerId);
                        continue;
                    }
                    tellers.push({
                        teller_id: tellerId,
                        slips: q.slips,
                        total_pool: q.total_pool,
                        updated_at: q.updated_at
                    });
                }

                const grandTotal = tellers.reduce((s, t) => s + t.total_pool, 0);
                const grandSlips = tellers.reduce((s, t) => s + t.slips.length, 0);

                return Response.json({
                    server_time: new Date().toISOString(),
                    tellers,
                    grand_total_pool: grandTotal,
                    grand_total_slips: grandSlips
                }, { headers: corsHeaders });
            }

            // ================================================================
            //  ROUND DETAILS + BETS
            // ================================================================
            if (path === '/api/round' && request.method === 'GET') {
                const roundId = url.searchParams.get('id');
                const mode = url.searchParams.get('mode') || 'local';
                const shopId = url.searchParams.get('shop_id') || 'default';

                if (!roundId) {
                    return Response.json({ error: 'Missing round id' }, { status: 400, headers: corsHeaders });
                }

                if (mode === 'local') {
                    const round = await env.DB.prepare(`SELECT * FROM local_rounds WHERE id = ? AND shop_id = ?`).bind(roundId, shopId).first();
                    if (!round) return Response.json({ error: 'Round not found' }, { status: 404, headers: corsHeaders });

                    const { roundEndsAt } = computeRoundTiming(round);
                    const isCrashed = Date.now() >= roundEndsAt;

                    const { results: bets } = await env.DB.prepare(`SELECT * FROM local_bets WHERE round_id = ?`).bind(roundId).all();

                    const resolved = isCrashed ? resolveLocalBets(round, bets) : (bets || []).map(b => ({ ...b, resolved: false }));

                    return Response.json({
                        success: true,
                        round: {
                            ...round,
                            crash_multiplier: isCrashed ? round.crash_multiplier : null,
                            bets: resolved
                        }
                    }, { headers: corsHeaders });
                }

                if (mode === 'global') {
                    const round = await env.DB.prepare(`SELECT * FROM global_rounds WHERE id = ?`).bind(roundId).first();
                    if (!round) return Response.json({ error: 'Round not found' }, { status: 404, headers: corsHeaders });

                    const { roundEndsAt } = computeRoundTiming(round);
                    const isCrashed = Date.now() >= roundEndsAt;

                    const { results: bets } = await env.DB.prepare(`SELECT * FROM global_bets WHERE round_id = ?`).bind(roundId).all();

                    return Response.json({
                        success: true,
                        round: {
                            ...round,
                            crash_multiplier: isCrashed ? round.crash_multiplier : null,
                            bets: bets || []
                        }
                    }, { headers: corsHeaders });
                }

                return Response.json({ error: 'Invalid mode' }, { status: 400, headers: corsHeaders });
            }

            // ================================================================
            //  BET PLACE  (teller/admin — legacy local bet)
            // ================================================================
            if (path === '/api/bet/place-local' && request.method === 'POST') {
                const token = extractToken(request);
                const sessionUser = await getSessionUser(env.DB, token);
                if (!sessionUser) {
                    return Response.json({ error: 'Authentication required.' }, { status: 401, headers: corsHeaders });
                }
                if (sessionUser.role !== 'teller' && sessionUser.role !== 'cashier' && sessionUser.role !== 'admin') {
                    return Response.json({ error: 'Teller or cashier role required.' }, { status: 403, headers: corsHeaders });
                }

                const body = await request.json().catch(() => ({}));
                const { roundId, name, stake, multiplier, shop_id } = body;
                const effectiveShopId = String(shop_id || sessionUser.shop_id || 'default').substring(0, 64);

                // Non-admin must operate within their own shop
                if (sessionUser.role !== 'admin' && effectiveShopId !== sessionUser.shop_id) {
                    return Response.json({ error: 'Cannot place bets outside your shop.' }, { status: 403, headers: corsHeaders });
                }

                if (!roundId || !stake || !multiplier) {
                    return Response.json({ error: 'Missing required bet parameters' }, { status: 400, headers: corsHeaders });
                }

                const ticketCode = `TKT-${Math.floor(1000 + Math.random() * 9000)}`;
                const stmt = env.DB.prepare(
                    `INSERT INTO local_bets (round_id, ticket_code, customer_name, stake, multiplier, status, created_by, shop_id) VALUES (?, ?, ?, ?, ?, 'pending', ?, ?)`
                ).bind(roundId, ticketCode, name || 'Walk-in Player', Number(stake), Number(multiplier), sessionUser.id, effectiveShopId);

                const res = await stmt.run();

                return Response.json({
                    success: true,
                    ticket_id: ticketCode,
                    bet_db_id: res.meta.last_row_id,
                    shop_id: effectiveShopId
                }, { headers: corsHeaders });
            }

            // ================================================================
            //  TICKET SETTLE  (cashier/admin)
            // ================================================================
            if (path === '/api/ticket/settle' && request.method === 'POST') {
                const token = extractToken(request);
                const sessionUser = await getSessionUser(env.DB, token);
                if (!sessionUser) {
                    return Response.json({ error: 'Authentication required.' }, { status: 401, headers: corsHeaders });
                }
                if (sessionUser.role !== 'cashier' && sessionUser.role !== 'teller' && sessionUser.role !== 'admin') {
                    return Response.json({ error: 'Cashier or teller role required.' }, { status: 403, headers: corsHeaders });
                }

                const body = await request.json().catch(() => ({}));
                const { roundId, ticketId, settlement_method, shop_id } = body;
                const effectiveShopId = String(shop_id || sessionUser.shop_id || 'default').substring(0, 64);

                // Non-admin must operate within their own shop
                if (sessionUser.role !== 'admin' && effectiveShopId !== sessionUser.shop_id) {
                    return Response.json({ error: 'Cannot settle tickets outside your shop.' }, { status: 403, headers: corsHeaders });
                }

                if (!roundId || !ticketId) {
                    return Response.json({ error: 'Missing settlement parameters' }, { status: 400, headers: corsHeaders });
                }

                // Verify the bet belongs to the user's shop before settling
                const betCheck = await env.DB.prepare(
                    `SELECT id, shop_id FROM local_bets WHERE (round_id = ? AND (ticket_code = ? OR id = ?)) LIMIT 1`
                ).bind(roundId, ticketId, ticketId).first();
                if (!betCheck) {
                    return Response.json({ error: 'Bet not found.' }, { status: 404, headers: corsHeaders });
                }
                if (sessionUser.role !== 'admin' && betCheck.shop_id !== sessionUser.shop_id) {
                    return Response.json({ error: 'Cannot settle bets from another shop.' }, { status: 403, headers: corsHeaders });
                }

                const method = ['cash', 'mpesa'].includes(settlement_method) ? settlement_method : 'cash';

                await env.DB.prepare(
                    `UPDATE local_bets SET status = 'settled', settlement_method = ?, settled_by = ?, settled_at = datetime('now') WHERE round_id = ? AND (ticket_code = ? OR id = ?) AND shop_id = ?`
                ).bind(method, sessionUser.id, roundId, ticketId, ticketId, effectiveShopId).run();

                return Response.json({ success: true }, { headers: corsHeaders });
            }

            return Response.json({ error: 'Not Found' }, { status: 404, headers: corsHeaders });
        } catch (err) {
            return Response.json({ error: err.message }, { status: 500, headers: corsHeaders });
        }
    },

    async scheduled(event, env, ctx) {
        ctx.waitUntil(checkAndAdvanceGlobalRound(env.DB));
    }
};
