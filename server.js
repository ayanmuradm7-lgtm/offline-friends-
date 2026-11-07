/**
 * Offline Friends - Minecraft Relay Server (Protocol v1)
 *
 * Single-file standalone server for cracked/offline Minecraft mod clients.
 * Zero external dependencies other than 'ws'.
 * Exposes /ws (WebSocket relay) and /health (HTTP health check).
 */

const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

// Configuration
const PORT = parseInt(process.env.PORT || '3000', 10);
const DATA_FILE = process.env.DATA_FILE || path.join(__dirname, 'data.json');
const PROTOCOL_VERSION = 1;
const SEVEN_DAYS_MS = 7 * 24 * 60 * 60 * 1000;
const MAX_QUEUED_PER_FRIEND = 50;
const MAX_DM_LENGTH = 256;
const RATE_LIMIT_COUNT = 20;
const RATE_LIMIT_WINDOW_MS = 30 * 1000;
const CLIENT_TIMEOUT_MS = 75 * 1000;

// In-Memory State
const users = new Map(); // lowercase -> { username, tokenHash, createdAt }
const friendships = new Set(); // "userA:userB" (alphabetically sorted)
const pendingRequests = new Set(); // "from:to"
let queuedDms = []; // [{ id, from, to, text, ts, expiresAt }]

// Active Connections
const activeClients = new Map(); // sessionId -> session
const usernameToSessionId = new Map(); // lowercase -> sessionId

// Helpers
function isValidUsername(name) {
  if (typeof name !== 'string') return false;
  return /^[a-zA-Z0-9_]{3,16}$/.test(name);
}

function hashToken(token, existingSalt) {
  const salt = existingSalt || crypto.randomBytes(16).toString('hex');
  const hash = crypto.createHash('sha256').update(`${salt}:${token}`).digest('hex');
  return `${salt}:${hash}`;
}

function verifyToken(token, storedHash) {
  if (!storedHash || !storedHash.includes(':')) return false;
  const [salt, originalHash] = storedHash.split(':');
  const computedHash = crypto.createHash('sha256').update(`${salt}:${token}`).digest('hex');
  try {
    return crypto.timingSafeEqual(Buffer.from(computedHash, 'utf8'), Buffer.from(originalHash, 'utf8'));
  } catch {
    return false;
  }
}

function makeFriendKey(u1, u2) {
  const a = u1.toLowerCase();
  const b = u2.toLowerCase();
  return a < b ? `${a}:${b}` : `${b}:${a}`;
}

function getCanonicalUsername(lowerName) {
  const record = users.get(lowerName.toLowerCase());
  return record ? record.username : lowerName;
}

function areFriends(userA, userB) {
  return friendships.has(makeFriendKey(userA, userB));
}

function getFriendsOf(username) {
  const lower = username.toLowerCase();
  const result = [];
  for (const key of friendships) {
    const [u1, u2] = key.split(':');
    if (u1 === lower) {
      result.push(getCanonicalUsername(u2));
    } else if (u2 === lower) {
      result.push(getCanonicalUsername(u1));
    }
  }
  return result;
}

function getPendingRequestsFor(username) {
  const lower = username.toLowerCase();
  const result = [];
  for (const req of pendingRequests) {
    const [from, to] = req.split(':');
    if (to === lower) {
      result.push(getCanonicalUsername(from));
    }
  }
  return result;
}

// Storage Management
function loadStorage() {
  try {
    if (fs.existsSync(DATA_FILE)) {
      const content = fs.readFileSync(DATA_FILE, 'utf8');
      const data = JSON.parse(content);
      if (data.users) {
        for (const [k, v] of Object.entries(data.users)) {
          users.set(k.toLowerCase(), v);
        }
      }
      if (Array.isArray(data.friendships)) {
        for (const f of data.friendships) friendships.add(f);
      }
      if (Array.isArray(data.pendingRequests)) {
        for (const p of data.pendingRequests) pendingRequests.add(p);
      }
      if (Array.isArray(data.queuedDms)) {
        const now = Date.now();
        queuedDms = data.queuedDms.filter((dm) => dm.expiresAt > now);
      }
      console.log(`[Storage] Loaded ${users.size} users, ${friendships.size} friendships, ${queuedDms.length} queued DMs.`);
    }
  } catch (err) {
    console.error('[Storage] Error reading database file:', err.message);
  }
}

let saveTimeout = null;
function scheduleSave() {
  if (saveTimeout) clearTimeout(saveTimeout);
  saveTimeout = setTimeout(() => {
    try {
      const data = {
        users: Object.fromEntries(users.entries()),
        friendships: Array.from(friendships),
        pendingRequests: Array.from(pendingRequests),
        queuedDms,
      };
      const tmpPath = `${DATA_FILE}.tmp`;
      fs.writeFileSync(tmpPath, JSON.stringify(data, null, 2), 'utf8');
      fs.renameSync(tmpPath, DATA_FILE);
    } catch (err) {
      console.error('[Storage] Error saving database file:', err.message);
    }
  }, 200);
}

function pruneExpiredDms() {
  const now = Date.now();
  const initialLength = queuedDms.length;
  queuedDms = queuedDms.filter((dm) => dm.expiresAt > now);
  if (queuedDms.length !== initialLength) {
    scheduleSave();
  }
}

// Client Session Helper
function getSessionByUsername(username) {
  const sessionId = usernameToSessionId.get(username.toLowerCase());
  if (!sessionId) return undefined;
  return activeClients.get(sessionId);
}

function broadcastFriendUpdate(fromUsername, online, server) {
  const friends = getFriendsOf(fromUsername);
  const msg = JSON.stringify({
    type: 'friend_update',
    username: fromUsername,
    online,
    server,
  });

  for (const friendName of friends) {
    const friendSession = getSessionByUsername(friendName);
    if (friendSession && friendSession.ws.readyState === 1) {
      friendSession.ws.send(msg);
    }
  }
}

// HTTP Server
const server = http.createServer((req, res) => {
  const url = new URL(req.url, `http://${req.headers.host || 'localhost'}`);

  if (url.pathname === '/health') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('ok');
    return;
  }

  if (url.pathname === '/') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Offline Friends Relay Server is running. Connect via WebSocket at /ws');
    return;
  }

  res.writeHead(404, { 'Content-Type': 'text/plain' });
  res.end('Not Found');
});

// WebSocket Server
const wss = new WebSocketServer({ noServer: true });

server.on('upgrade', (request, socket, head) => {
  const url = new URL(request.url, `http://${request.headers.host || 'localhost'}`);
  if (url.pathname === '/ws') {
    wss.handleUpgrade(request, socket, head, (ws) => {
      wss.emit('connection', ws, request);
    });
  } else {
    socket.destroy();
  }
});

wss.on('connection', (ws) => {
  const sessionId = crypto.randomBytes(8).toString('hex');
  const session = {
    id: sessionId,
    ws,
    username: null,
    invisible: false,
    server: null,
    lastActive: Date.now(),
    messageTimestamps: [],
  };

  activeClients.set(sessionId, session);

  const send = (obj) => {
    if (ws.readyState === 1) {
      ws.send(JSON.stringify(obj));
    }
  };

  ws.on('message', (raw) => {
    session.lastActive = Date.now();
    const str = raw.toString();

    // Size limit
    if (str.length > 16384) {
      send({ type: 'error', code: 'invalid', message: 'Message frame exceeds 16KB limit' });
      return;
    }

    let msg;
    try {
      msg = JSON.parse(str);
    } catch {
      send({ type: 'error', code: 'invalid', message: 'Malformed JSON payload' });
      return;
    }

    if (!msg || typeof msg !== 'object' || Array.isArray(msg) || typeof msg.type !== 'string') {
      send({ type: 'error', code: 'invalid', message: 'Message must be a JSON object with a string "type"' });
      return;
    }

    const type = msg.type;

    // Ping
    if (type === 'ping') {
      send({ type: 'pong' });
      return;
    }

    // Hello
    if (type === 'hello') {
      if (msg.protocol !== PROTOCOL_VERSION) {
        send({ type: 'error', code: 'invalid', message: 'Unsupported protocol version (expected 1)' });
        return;
      }

      if (!isValidUsername(msg.username)) {
        send({
          type: 'error',
          code: 'invalid',
          message: 'Username must be 3-16 characters: letters, digits, and underscores only',
        });
        return;
      }

      if (typeof msg.token !== 'string' || msg.token.trim().length === 0) {
        send({ type: 'error', code: 'bad_token', message: 'Secret token is required' });
        return;
      }

      const canonicalName = msg.username.trim();
      const lowerName = canonicalName.toLowerCase();
      const invisible = Boolean(msg.invisible);
      const serverVal = typeof msg.server === 'string' ? msg.server : null;

      const existingUser = users.get(lowerName);

      if (!existingUser) {
        // First client binds the username
        users.set(lowerName, {
          username: canonicalName,
          tokenHash: hashToken(msg.token),
          createdAt: Date.now(),
        });
        scheduleSave();
      } else {
        // User exists, verify token
        const match = verifyToken(msg.token, existingUser.tokenHash);
        if (!match) {
          const isOnline = usernameToSessionId.has(lowerName);
          const code = isOnline ? 'name_taken' : 'bad_token';
          send({
            type: 'error',
            code,
            message: code === 'name_taken' ? 'Username is currently claimed by an active player' : 'Bad secret token',
          });
          return;
        }
      }

      // Close previous connection if same username was logged in elsewhere
      const prevSessionId = usernameToSessionId.get(lowerName);
      if (prevSessionId && prevSessionId !== session.id) {
        const prevSession = activeClients.get(prevSessionId);
        if (prevSession && prevSession.ws.readyState === 1) {
          prevSession.ws.close();
        }
      }

      session.username = existingUser ? existingUser.username : canonicalName;
      session.invisible = invisible;
      session.server = serverVal;
      usernameToSessionId.set(lowerName, session.id);

      // Friends list for welcome message
      const friendsList = [];
      const friendNames = getFriendsOf(session.username);
      for (const fName of friendNames) {
        const fSession = getSessionByUsername(fName);
        if (fSession && !fSession.invisible) {
          friendsList.push({ username: fName, online: true, server: fSession.server });
        } else {
          friendsList.push({ username: fName, online: false, server: null });
        }
      }

      // Pending incoming friend requests
      const pendingIn = getPendingRequestsFor(session.username);

      // Queued DMs for this user
      pruneExpiredDms();
      const queuedForUser = [];
      const remainingDms = [];
      for (const dm of queuedDms) {
        if (dm.to.toLowerCase() === lowerName) {
          queuedForUser.push({ id: dm.id, from: dm.from, text: dm.text, ts: dm.ts });
        } else {
          remainingDms.push(dm);
        }
      }

      if (queuedForUser.length > 0) {
        queuedDms = remainingDms;
        scheduleSave();
      }

      // Send welcome
      send({
        type: 'welcome',
        friends: friendsList,
        pending_in: pendingIn,
        queued_dms: queuedForUser,
      });

      // Broadcast presence if not invisible
      if (!session.invisible) {
        broadcastFriendUpdate(session.username, true, session.server);
      }
      return;
    }

    // All further messages require hello first
    if (!session.username) {
      send({ type: 'error', code: 'invalid', message: 'You must send hello before any other message' });
      return;
    }

    const currentName = session.username;

    // Presence
    if (type === 'presence') {
      if (typeof msg.invisible !== 'boolean') {
        send({ type: 'error', code: 'invalid', message: 'invisible must be a boolean' });
        return;
      }
      session.invisible = msg.invisible;
      session.server = typeof msg.server === 'string' ? msg.server : null;

      if (session.invisible) {
        broadcastFriendUpdate(currentName, false, null);
      } else {
        broadcastFriendUpdate(currentName, true, session.server);
      }
      return;
    }

    // Friend Request
    if (type === 'friend_request') {
      const to = typeof msg.to === 'string' ? msg.to.trim() : '';
      if (!isValidUsername(to)) {
        send({ type: 'error', code: 'invalid', message: 'Invalid recipient username' });
        return;
      }

      if (to.toLowerCase() === currentName.toLowerCase()) {
        send({ type: 'error', code: 'invalid', message: 'Cannot friend yourself' });
        return;
      }

      if (areFriends(currentName, to)) {
        return; // Already friends
      }

      // If other user already requested us, auto-accept mutual request
      const reverseReq = `${to.toLowerCase()}:${currentName.toLowerCase()}`;
      if (pendingRequests.has(reverseReq)) {
        pendingRequests.delete(reverseReq);
        friendships.add(makeFriendKey(currentName, to));
        scheduleSave();

        send({ type: 'friend_added', username: to });
        const toSession = getSessionByUsername(to);
        if (toSession && !toSession.invisible) {
          send({ type: 'friend_update', username: to, online: true, server: toSession.server });
        }

        if (toSession) {
          toSession.ws.send(JSON.stringify({ type: 'friend_added', username: currentName }));
          if (!session.invisible) {
            toSession.ws.send(
              JSON.stringify({ type: 'friend_update', username: currentName, online: true, server: session.server })
            );
          }
        }
        return;
      }

      // Record pending request
      const reqKey = `${currentName.toLowerCase()}:${to.toLowerCase()}`;
      pendingRequests.add(reqKey);
      scheduleSave();

      const toSession = getSessionByUsername(to);
      if (toSession && toSession.ws.readyState === 1) {
        toSession.ws.send(JSON.stringify({ type: 'friend_request_in', from: currentName }));
      }
      return;
    }

    // Friend Accept
    if (type === 'friend_accept') {
      const from = typeof msg.from === 'string' ? msg.from.trim() : '';
      if (!isValidUsername(from)) {
        send({ type: 'error', code: 'invalid', message: 'Invalid username' });
        return;
      }

      const reqKey = `${from.toLowerCase()}:${currentName.toLowerCase()}`;
      if (!pendingRequests.has(reqKey)) {
        return;
      }

      pendingRequests.delete(reqKey);
      friendships.add(makeFriendKey(currentName, from));
      scheduleSave();

      send({ type: 'friend_added', username: from });
      const fromSession = getSessionByUsername(from);
      if (fromSession && !fromSession.invisible) {
        send({ type: 'friend_update', username: from, online: true, server: fromSession.server });
      }

      if (fromSession) {
        fromSession.ws.send(JSON.stringify({ type: 'friend_added', username: currentName }));
        if (!session.invisible) {
          fromSession.ws.send(
            JSON.stringify({ type: 'friend_update', username: currentName, online: true, server: session.server })
          );
        }
      }
      return;
    }

    // Friend Decline
    if (type === 'friend_decline') {
      const from = typeof msg.from === 'string' ? msg.from.trim() : '';
      const reqKey = `${from.toLowerCase()}:${currentName.toLowerCase()}`;
      if (pendingRequests.has(reqKey)) {
        pendingRequests.delete(reqKey);
        scheduleSave();
      }
      return;
    }

    // Friend Remove
    if (type === 'friend_remove') {
      const target = typeof msg.username === 'string' ? msg.username.trim() : '';
      const key = makeFriendKey(currentName, target);

      if (friendships.has(key)) {
        friendships.delete(key);
        scheduleSave();

        send({ type: 'friend_removed', username: target });

        const targetSession = getSessionByUsername(target);
        if (targetSession) {
          targetSession.ws.send(JSON.stringify({ type: 'friend_removed', username: currentName }));
          targetSession.ws.send(
            JSON.stringify({ type: 'friend_update', username: currentName, online: false, server: null })
          );
        }
      }
      return;
    }

    // Direct Message (DM)
    if (type === 'dm') {
      const id = typeof msg.id === 'string' ? msg.id : '';
      const to = typeof msg.to === 'string' ? msg.to.trim() : '';
      const text = typeof msg.text === 'string' ? msg.text : '';

      if (!id || !to) {
        send({ type: 'error', code: 'invalid', message: 'Missing dm id or recipient' });
        if (id) send({ type: 'dm_ack', id, status: 'failed' });
        return;
      }

      // Rate limit check: 20 per 30 seconds
      const now = Date.now();
      session.messageTimestamps = session.messageTimestamps.filter((t) => now - t < RATE_LIMIT_WINDOW_MS);
      if (session.messageTimestamps.length >= RATE_LIMIT_COUNT) {
        send({ type: 'error', code: 'rate_limited', message: 'Rate limit exceeded (max 20 messages per 30s)' });
        send({ type: 'dm_ack', id, status: 'failed' });
        return;
      }
      session.messageTimestamps.push(now);

      // Must be friends
      if (!areFriends(currentName, to)) {
        send({ type: 'error', code: 'not_friends', message: 'Cannot DM: not accepted friends' });
        send({ type: 'dm_ack', id, status: 'failed' });
        return;
      }

      // Max 256 characters
      if (text.length === 0 || text.length > MAX_DM_LENGTH) {
        send({ type: 'error', code: 'invalid', message: `Message must be between 1 and ${MAX_DM_LENGTH} characters` });
        send({ type: 'dm_ack', id, status: 'failed' });
        return;
      }

      const toSession = getSessionByUsername(to);

      // Online delivery
      if (toSession && toSession.ws.readyState === 1) {
        toSession.ws.send(
          JSON.stringify({
            type: 'dm_in',
            id,
            from: currentName,
            text,
            ts: now,
          })
        );
        send({ type: 'dm_ack', id, status: 'delivered' });
        return;
      }

      // Offline queue
      pruneExpiredDms();
      const existingCount = queuedDms.filter(
        (dm) => dm.to.toLowerCase() === to.toLowerCase() && dm.from.toLowerCase() === currentName.toLowerCase()
      ).length;

      if (existingCount >= MAX_QUEUED_PER_FRIEND) {
        send({ type: 'dm_ack', id, status: 'failed' });
        return;
      }

      queuedDms.push({
        id,
        from: currentName,
        to,
        text,
        ts: now,
        expiresAt: now + SEVEN_DAYS_MS,
      });
      scheduleSave();

      send({ type: 'dm_ack', id, status: 'queued' });
      return;
    }

    // Tracking Consent
    if (type === 'track_request') {
      const to = typeof msg.to === 'string' ? msg.to.trim() : '';
      if (!areFriends(currentName, to)) {
        send({ type: 'error', code: 'not_friends', message: 'Tracking requires accepted friends' });
        return;
      }
      const target = getSessionByUsername(to);
      if (target && target.ws.readyState === 1) {
        target.ws.send(JSON.stringify({ type: 'track_request_in', from: currentName }));
      }
      return;
    }

    if (type === 'track_accept') {
      const from = typeof msg.from === 'string' ? msg.from.trim() : '';
      if (!areFriends(currentName, from)) {
        send({ type: 'error', code: 'not_friends', message: 'Not friends' });
        return;
      }
      const target = getSessionByUsername(from);
      if (target && target.ws.readyState === 1) {
        target.ws.send(JSON.stringify({ type: 'track_accepted', by: currentName }));
      }
      return;
    }

    if (type === 'track_decline') {
      const from = typeof msg.from === 'string' ? msg.from.trim() : '';
      if (!areFriends(currentName, from)) {
        send({ type: 'error', code: 'not_friends', message: 'Not friends' });
        return;
      }
      const target = getSessionByUsername(from);
      if (target && target.ws.readyState === 1) {
        target.ws.send(JSON.stringify({ type: 'track_declined', by: currentName }));
      }
      return;
    }

    if (type === 'track_stop') {
      const withUser = typeof msg.with === 'string' ? msg.with.trim() : '';
      if (!areFriends(currentName, withUser)) {
        send({ type: 'error', code: 'not_friends', message: 'Not friends' });
        return;
      }
      const target = getSessionByUsername(withUser);
      if (target && target.ws.readyState === 1) {
        target.ws.send(JSON.stringify({ type: 'track_stopped', by: currentName }));
      }
      return;
    }

    send({ type: 'error', code: 'invalid', message: `Unknown message type "${type}"` });
  });

  const cleanupSession = () => {
    activeClients.delete(sessionId);
    if (session.username) {
      const lower = session.username.toLowerCase();
      if (usernameToSessionId.get(lower) === sessionId) {
        usernameToSessionId.delete(lower);
      }
      if (!session.invisible) {
        broadcastFriendUpdate(session.username, false, null);
      }
    }
  };

  ws.on('close', cleanupSession);
  ws.on('error', cleanupSession);
});

// Drop silent clients after 75 seconds (heartbeat watchdog)
setInterval(() => {
  const now = Date.now();
  for (const [sessionId, session] of activeClients.entries()) {
    if (now - session.lastActive > CLIENT_TIMEOUT_MS) {
      console.log(`[Watchdog] Dropping silent client ${session.username || sessionId} after 75s`);
      session.ws.terminate();
      activeClients.delete(sessionId);
      if (session.username) {
        const lower = session.username.toLowerCase();
        if (usernameToSessionId.get(lower) === sessionId) {
          usernameToSessionId.delete(lower);
        }
        if (!session.invisible) {
          broadcastFriendUpdate(session.username, false, null);
        }
      }
    }
  }
}, 10000);

// Prune expired DMs hourly
setInterval(pruneExpiredDms, 60 * 60 * 1000);

// Initialize Storage and Start Server
loadStorage();

server.listen(PORT, '0.0.0.0', () => {
  console.log(`=======================================================`);
  console.log(` Offline Friends Relay Server (Protocol v1)`);
  console.log(` Running on port: ${PORT}`);
  console.log(` Health check URL: http://0.0.0.0:${PORT}/health`);
  console.log(` WebSocket URL:    ws://0.0.0.0:${PORT}/ws`);
  console.log(`=======================================================`);
});
