/**
 * BennSauce Game Server
 * Real-time multiplayer server using Socket.io
 * 
 * Phase 1: Player position synchronization
 * Phase 2: Server-authoritative monsters (shared monsters)
 */

const express = require('express');
const http = require('http');
const https = require('https');
const { Server } = require('socket.io');
const cors = require('cors');

// Debug logging - set DEBUG=true env var to enable verbose server logs
const DEBUG = process.env.DEBUG === 'true';

// Server start time - sent to clients so they can detect server restarts
const SERVER_START_TIME = Date.now();

const app = express();

// Configure CORS to allow itch.io and other domains
app.use(cors({
    origin: '*',
    credentials: true
}));

const server = http.createServer(app);
const io = new Server(server, {
    cors: {
        origin: '*',
        methods: ['GET', 'POST'],
        credentials: true,
        allowedHeaders: ['Content-Type']
    },
    transports: ['websocket', 'polling'],
    allowEIO3: true
});

// Store connected players by map
// Structure: { mapId: { odId: playerData } }
const maps = {};

// Store player socket mapping
// Structure: { odId: socketId }
const playerSockets = {};

// Store monsters by map
// Structure: { mapId: { monsterId: monsterData } }
const mapMonsters = {};

// Store damage tracking for loot distribution
// Structure: { monsterId: { odId: totalDamage } }
const monsterDamage = {};

// Monster AI update interval
let monsterAIInterval = null;

// Monster ID counter
let nextMonsterId = 1;

// Configuration
const CONFIG = {
    POSITION_UPDATE_RATE: 50, // ms between position broadcasts (20 updates/sec)
    PLAYER_TIMEOUT: 172800000, // 48 hours - effectively disabled (allow AFK players to stay visible)
    MAX_PLAYERS_PER_MAP: 50,
    MONSTER_AI_RATE: 50, // ms between monster AI updates (20 updates/sec for smoother movement)
    MONSTER_BROADCAST_RATE: 50, // ms between position broadcasts (20/sec for high-ping players)
    RESPAWN_TIME: 8000, // Regular monster respawn time (8 seconds)
    BOSS_RESPAWN_TIME: 300000, // Boss respawn time (5 minutes)
    MONSTER_SPEED: 0.8, // Base monster movement speed
    PATROL_CHANGE_CHANCE: 0.02, // Chance to change direction per update
    
    // Anti-cheat configuration
    MAX_DAMAGE_PER_HIT: 50000, // Maximum reasonable damage per hit (high level + crits)
    MAX_ATTACKS_PER_SECOND: 10, // Maximum attacks allowed per second
    MAX_PICKUPS_PER_SECOND: 20, // Maximum item pickups per second
    RATE_LIMIT_WINDOW: 1000, // Rate limit window in ms
    MAX_POSITION_UPDATES_PER_SECOND: 30, // Max position updates per second
    MAX_TELEPORT_DISTANCE: 2000, // Max distance player can move in one update (pixels)
    
    // GM Authentication - MUST set GM_PASSWORD environment variable on Render/hosting platform.
    // GM mode is DISABLED if the env var is not set.
    GM_PASSWORD: process.env.GM_PASSWORD || null
};

// Authorized GM sessions (socket IDs that have been authenticated)
const authorizedGMs = new Set();

// Rate limiting trackers
// Structure: { odId: { attacks: [{timestamp}], pickups: [{timestamp}], positions: [{timestamp, x, y}] } }
const rateLimiters = {};

// ============================================
// CHESS GAME MATCHMAKING
// ============================================
// Players waiting for a chess match per map
// Structure: { mapId: { socketId, playerName, gameId } }
const chessWaiting = {};
// Active chess games
// Structure: { gameId: { whiteSocketId, blackSocketId, whiteName, blackName } }
const chessGames = {};

// ============================================
// SERVER-SIDE SHINY & ELITE MONSTER CONFIG
// ============================================
const SHINY_CONFIG = {
    spawnChance: 0.02, // 2% chance on each monster spawn
    hpMultiplier: 3    // 3x HP (visuals/loot handled client-side)
};

const ELITE_CONFIG = {
    checkIntervalMin: 2 * 60 * 1000,  // Min 2 minutes between checks
    checkIntervalMax: 7 * 60 * 1000,  // Max 7 minutes between checks
    spawnChance: 0.3,                  // 30% chance per check
    hpMultiplier: 100,                 // 100x HP
    damageMultiplier: 3,               // 3x damage
    excludedMapPrefixes: ['dewdrop', 'pq'] // Don't spawn on tutorial/party quest maps
};

// Track current elite monsters per map (only one per map)
const currentEliteMonsters = {};

// Track ground items per map for pickup validation (prevents double-pickup duplication)
// Structure: { mapId: { itemId: { name, x, y, droppedBy, timestamp } } }
const mapGroundItems = {};

// Elite check timer
let eliteCheckInterval = null;

/**
 * Check rate limit for an action
 * @returns {boolean} true if action is allowed, false if rate limited
 */
function checkRateLimit(odId, action, limit) {
    if (!rateLimiters[odId]) {
        rateLimiters[odId] = { attacks: [], pickups: [], positions: [] };
    }
    
    const now = Date.now();
    const tracker = rateLimiters[odId][action];
    
    // Remove old entries outside the window
    while (tracker.length > 0 && now - tracker[0].timestamp > CONFIG.RATE_LIMIT_WINDOW) {
        tracker.shift();
    }
    
    // Check if over limit
    if (tracker.length >= limit) {
        console.warn(`[Security] Rate limit exceeded for ${odId}: ${action} (${tracker.length}/${limit} per second)`);
        return false;
    }
    
    // Add new entry
    tracker.push({ timestamp: now });
    return true;
}

/**
 * Validate damage value is reasonable
 * @returns {number} Clamped damage value
 */
function validateDamage(damage, attackerId) {
    if (typeof damage !== 'number' || isNaN(damage) || damage < 0) {
        console.warn(`[Security] Invalid damage value from ${attackerId}: ${damage}`);
        return 0;
    }
    
    if (damage > CONFIG.MAX_DAMAGE_PER_HIT) {
        console.warn(`[Security] Suspicious damage from ${attackerId}: ${damage} (capped to ${CONFIG.MAX_DAMAGE_PER_HIT})`);
        return CONFIG.MAX_DAMAGE_PER_HIT;
    }
    
    return Math.floor(damage);
}

/**
 * Clean up rate limiter data for disconnected players
 */
function cleanupRateLimiter(odId) {
    delete rateLimiters[odId];
}

// Map spawn definitions - will be received from clients
// Structure: { mapId: { monsters: [{type, count}], spawners: [{type, maxCount}] } }
const mapSpawnData = {};

/**
 * Initialize monsters for a map when first player joins
 * Uses pre-calculated spawn positions from client if available
 */
function initializeMapMonsters(mapId, mapData) {
    if (mapMonsters[mapId]) return; // Already initialized
    
    mapMonsters[mapId] = {};
    mapSpawnData[mapId] = mapData;
    
    if (!mapData || !mapData.monsters) return;
    
    console.log(`[Server] Initializing monsters for map ${mapId}`);
    
    // If client sent pre-calculated positions, use those
    if (mapData.spawnPositions && mapData.spawnPositions.length > 0) {
        console.log(`[Server] Using ${mapData.spawnPositions.length} pre-calculated spawn positions`);
        for (const pos of mapData.spawnPositions) {
            spawnMonster(mapId, pos.type, {
                ...mapData,
                x: pos.x,
                y: pos.y,
                // Pass surface bounds from spawn position for proper patrol limits
                surfaceX: pos.surfaceX,
                surfaceWidth: pos.surfaceWidth
            });
        }
    } else {
        // Fallback: spawn at random positions (old behavior)
        for (const spawner of mapData.monsters) {
            const count = spawner.count || 5;
            for (let i = 0; i < count; i++) {
                spawnMonster(mapId, spawner.type, mapData);
            }
        }
    }
    
    // Start monster AI if not already running
    startMonsterAI();
    
    // Start elite monster check system if not already running
    startEliteCheckSystem();
}

/**
 * Spawn a new monster on a map (position can be provided by client)
 */
function spawnMonster(mapId, type, spawnerData = {}) {
    const monsterId = `m_${nextMonsterId++}`;
    const mapWidth = spawnerData.mapWidth || mapSpawnData[mapId]?.mapWidth || 1366;
    const groundY = spawnerData.groundY || mapSpawnData[mapId]?.groundY || 300;
    
    // Get monster type data from stored data
    const monsterTypeData = mapSpawnData[mapId]?.monsterTypes?.[type] || {};
    
    if (DEBUG) console.log(`[Server] Spawning ${type} - canJump: ${monsterTypeData.canJump}, jumpForce: ${monsterTypeData.jumpForce}, monsterTypeData keys:`, Object.keys(monsterTypeData));
    
    const maxHp = monsterTypeData.hp || spawnerData.maxHp || 100;
    const speed = monsterTypeData.speed || CONFIG.MONSTER_SPEED;
    const monsterHeight = monsterTypeData.height || 40;
    
    // Use provided spawn position or generate random
    const x = spawnerData.x !== undefined ? spawnerData.x : Math.random() * (mapWidth - 100) + 50;
    // CRITICAL: Always use client-provided Y position if available, as it accounts for anchor points
    // Client calculates: spawnY = surfaceY - anchorY - groundOffset
    // If not provided, fall back to simple ground calculation
    const y = spawnerData.y !== undefined ? spawnerData.y : groundY - monsterHeight - 3;
    
    const direction = Math.random() > 0.5 ? 1 : -1;
    
    // Determine AI type - static monsters don't move
    const aiType = monsterTypeData.aiType || 'patrolling';
    
    const monster = {
        id: monsterId,
        type: type,
        x: x,
        y: y,
        hp: maxHp,
        maxHp: maxHp,
        direction: direction,
        facing: direction === 1 ? 'right' : 'left',
        aiState: aiType === 'static' ? 'idle' : 'patrolling',
        aiType: aiType,
        velocityX: 0,
        velocityY: 0,
        speed: speed,
        isDead: false,
        isMiniBoss: monsterTypeData.isMiniBoss || false,
        isEliteMonster: false, // Elites are created by client transformation
        isTrialBoss: false,
        width: monsterTypeData.width || 40,
        height: monsterHeight,
        mapWidth: mapWidth,
        groundY: groundY, // Store the surface ground level (not spawn Y)
        spawnTime: Date.now(),
        lastUpdate: Date.now(),
        // Store spawn info for proper respawning
        spawnX: x,
        spawnY: y,
        // Store surface X and width for patrol bounds preservation
        patrolSurfaceX: spawnerData.surfaceX,
        patrolSurfaceWidth: spawnerData.surfaceWidth,
        // Elite monster properties (set when transformed)
        originalMaxHp: null,
        originalDamage: null,
        // Jumping properties
        canJump: monsterTypeData.canJump || false,
        jumpForce: monsterTypeData.jumpForce || -8,
        isJumping: false,
        // Aggro detection
        aggroRange: monsterTypeData.isMiniBoss ? 350 : 250, // Detection range for aggro
        chaseStartTime: 0
    };
    
    // Calculate patrol bounds based on platform/structure bounds if provided, otherwise use spawn position
    // Use 50px buffer from edges to prevent monsters from walking off platforms
    const EDGE_BUFFER = 50;
    const MIN_PATROL_DISTANCE = 80; // Minimum patrol range to prevent stuck flipping
    
    if (spawnerData.surfaceX !== undefined && spawnerData.surfaceWidth !== undefined) {
        const surfaceLeft = spawnerData.surfaceX + EDGE_BUFFER;
        const surfaceRight = spawnerData.surfaceX + spawnerData.surfaceWidth - EDGE_BUFFER;
        const surfacePatrolWidth = surfaceRight - surfaceLeft;
        
        if (surfacePatrolWidth >= MIN_PATROL_DISTANCE) {
            // Normal case: surface is wide enough for patrol
            monster.patrolMinX = Math.max(0, surfaceLeft);
            monster.patrolMaxX = Math.min(mapWidth - EDGE_BUFFER, surfaceRight);
        } else {
            // Surface too narrow - just stand still in the center
            const center = spawnerData.surfaceX + spawnerData.surfaceWidth / 2;
            monster.patrolMinX = center - 10;
            monster.patrolMaxX = center + 10;
            monster.aiState = 'idle'; // Start as idle since can't patrol
        }
    } else {
        // Fallback: patrol around spawn position
        monster.patrolMinX = Math.max(0, x - 150);
        monster.patrolMaxX = Math.min(mapWidth - EDGE_BUFFER, x + 150);
    }
    
    mapMonsters[mapId][monsterId] = monster;
    monsterDamage[monsterId] = {};
    
    // Server-side shiny roll: 2% chance for eligible monsters
    if (!monster.isMiniBoss && !monster.isTrialBoss && monster.type !== 'testDummy') {
        const isExcludedMap = ELITE_CONFIG.excludedMapPrefixes.some(prefix => mapId.startsWith(prefix));
        if (!isExcludedMap && Math.random() < SHINY_CONFIG.spawnChance) {
            monster.isShiny = true;
            monster.maxHp = Math.floor(monster.maxHp * SHINY_CONFIG.hpMultiplier);
            monster.hp = monster.maxHp;
            console.log(`[Server] ✨ SHINY ${type} spawned on ${mapId}!`);
        }
    }
    
    if (DEBUG) console.log(`[Server] Spawned ${type} (${monsterId}) with ${maxHp} HP at (${Math.round(x)}, ${Math.round(y)})${monster.isShiny ? ' [SHINY]' : ''}`);
    
    // Notify all players on this map about the new monster
    io.to(mapId).emit('monsterSpawned', monster);
    
    return monster;
}

/**
 * Server-side monster AI update loop
 */
function startMonsterAI() {
    if (monsterAIInterval) return; // Already running
    
    console.log('[Server] Starting monster AI loop');
    
    monsterAIInterval = setInterval(() => {
        updateAllMonsters();
        broadcastMonsterPositions();
    }, CONFIG.MONSTER_AI_RATE);
}

/**
 * Server-side elite monster check system
 * Periodically checks each active map for a possible elite spawn
 */
function startEliteCheckSystem() {
    if (eliteCheckInterval) return; // Already running
    
    console.log('[Server] Starting elite monster check system');
    
    // Schedule the first check after a random delay
    scheduleNextEliteCheck();
}

function scheduleNextEliteCheck() {
    const delay = ELITE_CONFIG.checkIntervalMin + Math.random() * (ELITE_CONFIG.checkIntervalMax - ELITE_CONFIG.checkIntervalMin);
    eliteCheckInterval = setTimeout(() => {
        attemptServerEliteSpawn();
        scheduleNextEliteCheck(); // Schedule next check
    }, delay);
}

function attemptServerEliteSpawn() {
    // Check each active map
    for (const mapId in mapMonsters) {
        // Skip if no players on this map
        if (!maps[mapId] || Object.keys(maps[mapId]).length === 0) continue;
        
        // Skip excluded maps
        if (ELITE_CONFIG.excludedMapPrefixes.some(prefix => mapId.startsWith(prefix))) continue;
        
        // Skip if this map already has an elite
        if (currentEliteMonsters[mapId]) continue;
        
        // 30% chance per check
        if (Math.random() > ELITE_CONFIG.spawnChance) continue;
        
        // Get eligible monsters (alive, not boss, not already elite/shiny)
        const eligible = Object.values(mapMonsters[mapId]).filter(m => 
            !m.isDead && !m.isMiniBoss && !m.isTrialBoss && !m.isEliteMonster && m.type !== 'testDummy'
        );
        
        if (eligible.length === 0) continue;
        
        // Pick random monster
        const target = eligible[Math.floor(Math.random() * eligible.length)];
        
        // Transform to elite on server
        target.isEliteMonster = true;
        target.originalMaxHp = target.maxHp;
        target.originalDamage = target.damage || 10;
        target.maxHp = Math.floor(target.maxHp * ELITE_CONFIG.hpMultiplier);
        target.hp = target.maxHp;
        target.damage = Math.floor((target.damage || 10) * ELITE_CONFIG.damageMultiplier);
        
        currentEliteMonsters[mapId] = target.id;
        
        console.log(`[Server] ⚠️ ELITE ${target.type} spawned on ${mapId}! (monster ${target.id})`);
        
        // Broadcast to all clients on this map
        io.to(mapId).emit('monsterTransformedElite', {
            monsterId: target.id,
            maxHp: target.maxHp,
            hp: target.hp,
            damage: target.damage,
            originalMaxHp: target.originalMaxHp,
            originalDamage: target.originalDamage
        });
    }
}

/**
 * Update all monsters across all maps
 */
function updateAllMonsters() {
    for (const mapId in mapMonsters) {
        // Update monsters regardless of player presence (server runs independently)
        // Only skip if map has never been initialized
        if (!mapMonsters[mapId]) continue;
        
        for (const monsterId in mapMonsters[mapId]) {
            const monster = mapMonsters[mapId][monsterId];
            if (monster.isDead) continue;
            
            updateMonsterAI(monster, mapId);
        }
    }
}

/**
 * Simple server-side monster AI - handles X movement only
 * Client handles Y physics (gravity, jumping) locally
 */
function updateMonsterAI(monster, mapId) {
    // Skip AI for static monsters (like test dummy)
    if (monster.aiType === 'static') {
        monster.velocityX = 0;
        return;
    }
    
    // Skip AI during knockback
    if (monster.knockbackEndTime && Date.now() < monster.knockbackEndTime) {
        monster.velocityX = 0;
        return;
    }
    
    const speedMultiplier = 4.2;
    const CHASE_TIMEOUT = 5000;
    const CHASE_RANGE = 500;
    const now = Date.now();
    
    // Monsters only aggro when attacked (set in damageMonster function)
    // No proximity aggro
    
    // Check if monster should stop chasing
    if (monster.aiState === 'chasing') {
        const timeSinceInteraction = now - (monster.lastInteractionTime || 0);
        
        if (timeSinceInteraction > CHASE_TIMEOUT) {
            monster.aiState = 'patrolling';
            monster.targetPlayer = null;
            // Update patrol bounds to current position so monster doesn't snap back
            const patrolRadius = (monster.patrolMaxX - monster.patrolMinX) / 2;
            monster.patrolMinX = Math.max(0, monster.x - patrolRadius);
            monster.patrolMaxX = Math.min(monster.mapWidth - monster.width, monster.x + patrolRadius);
            monster.spawnX = monster.x; // Update spawn point too
        } else if (monster.targetPlayer && maps[mapId]) {
            const target = maps[mapId][monster.targetPlayer];
            if (target) {
                const targetX = target.x + 15;
                const dx = targetX - monster.x;
                const distFromSpawn = Math.abs(monster.x - monster.spawnX);
                
                if (distFromSpawn < CHASE_RANGE) {
                    monster.direction = dx > 0 ? 1 : -1;
                    monster.facing = monster.direction === 1 ? 'right' : 'left';
                    
                    // Chase speed (1.5x patrol)
                    const chaseSpeed = (monster.speed || CONFIG.MONSTER_SPEED) * speedMultiplier * 1.5;
                    const moveAmount = monster.direction * chaseSpeed;
                    const newX = monster.x + moveAmount;
                    
                    // Respect map boundaries
                    if (newX >= 0 && newX <= monster.mapWidth - monster.width) {
                        monster.velocityX = moveAmount;
                        monster.x = newX;
                    } else {
                        monster.velocityX = 0;
                    }
                } else {
                    // Too far from spawn - stop chasing but stay at current position
                    monster.aiState = 'patrolling';
                    monster.targetPlayer = null;
                    // Update patrol bounds to current position
                    const patrolRadius = 100;
                    monster.patrolMinX = Math.max(0, monster.x - patrolRadius);
                    monster.patrolMaxX = Math.min(monster.mapWidth - monster.width, monster.x + patrolRadius);
                    monster.spawnX = monster.x;
                }
            } else {
                monster.targetPlayer = null;
            }
        }
        monster.lastUpdate = now;
        return;
    }
    
    // Simple patrol behavior
    if (monster.aiState === 'patrolling' || monster.aiState === 'idle') {
        // Turn at patrol boundaries
        if (monster.x <= monster.patrolMinX + 30) {
            monster.direction = 1;
            monster.facing = 'right';
        } else if (monster.x >= monster.patrolMaxX - 30) {
            monster.direction = -1;
            monster.facing = 'left';
        } else if (Math.random() < CONFIG.PATROL_CHANGE_CHANCE) {
            monster.direction *= -1;
            monster.facing = monster.direction === 1 ? 'right' : 'left';
        }
        
        // Move
        const moveAmount = monster.direction * (monster.speed || CONFIG.MONSTER_SPEED) * speedMultiplier;
        const newX = monster.x + moveAmount;
        
        if (newX >= monster.patrolMinX && newX <= monster.patrolMaxX) {
            monster.velocityX = moveAmount;
            monster.x = newX;
        } else {
            monster.velocityX = 0;
            if (newX < monster.patrolMinX) {
                monster.x = monster.patrolMinX;
                monster.direction = 1;
                monster.facing = 'right';
            } else {
                monster.x = monster.patrolMaxX;
                monster.direction = -1;
                monster.facing = 'left';
            }
        }
        
        // Clamp to map
        if (monster.x < 0) {
            monster.x = 0;
            monster.direction = 1;
            monster.facing = 'right';
        }
        if (monster.x > monster.mapWidth - monster.width) {
            monster.x = monster.mapWidth - monster.width;
            monster.direction = -1;
            monster.facing = 'left';
        }
        
        monster.aiState = 'patrolling';
    }
    
    monster.lastUpdate = now;
}

/**
 * Broadcast monster positions to all players
 * Server only sends X position/direction - client handles Y physics locally
 */
function broadcastMonsterPositions() {
    const serverTime = Date.now();
    
    for (const mapId in mapMonsters) {
        if (!maps[mapId] || Object.keys(maps[mapId]).length === 0) continue;
        
        const monsterPositions = [];
        for (const monsterId in mapMonsters[mapId]) {
            const m = mapMonsters[mapId][monsterId];
            if (m.isDead) continue;
            
            monsterPositions.push({
                id: m.id,
                x: m.x,
                y: m.y,           // Sync Y so all clients share same reference position
                facing: m.facing,
                direction: m.direction,
                aiState: m.aiState,
                velocityX: m.velocityX || 0,
                velocityY: m.velocityY || 0,  // Sync Y velocity for jump state detection
                t: serverTime // Timestamp for client-side lag compensation
            });
        }
        
        if (monsterPositions.length > 0) {
            io.to(mapId).emit('monsterPositions', { monsters: monsterPositions, t: serverTime });
        }
    }
}

/**
 * Handle monster damage from a player (with prediction reconciliation)
 */
function damageMonster(mapId, monsterId, damage, attackerId, attackDirection, seq, predictedHp) {
    if (!mapMonsters[mapId] || !mapMonsters[mapId][monsterId]) return null;
    
    const monster = mapMonsters[mapId][monsterId];
    if (monster.isDead) return null;
    
    // Anti-cheat: Rate limit attacks
    if (!checkRateLimit(attackerId, 'attacks', CONFIG.MAX_ATTACKS_PER_SECOND)) {
        return { rateLimited: true };
    }
    
    // Anti-cheat: Validate and cap damage
    const validatedDamage = validateDamage(damage, attackerId);
    if (validatedDamage === 0) {
        return null;
    }
    
    // Track damage for loot distribution
    if (!monsterDamage[monsterId]) {
        monsterDamage[monsterId] = {};
    }
    monsterDamage[monsterId][attackerId] = (monsterDamage[monsterId][attackerId] || 0) + validatedDamage;
    
    // Apply damage (use validated damage)
    monster.hp -= validatedDamage;
    monster.lastUpdate = Date.now();
    
    // Set monster to chase the attacker (aggro)
    if (monster.aiType !== 'static') {
        monster.aiState = 'chasing';
        monster.targetPlayer = attackerId;
        monster.lastInteractionTime = Date.now();
    }
    
    // Calculate knockback (only for non-static monsters)
    let knockbackVelocityX = 0;
    if (monster.aiType !== 'static' && attackDirection !== undefined) {
        // Knockback force: 6 units in the direction the player is facing (matches client KNOCKBACK_FORCE)
        const knockbackForce = 6;
        knockbackVelocityX = attackDirection * knockbackForce;
        
        // Actually apply knockback displacement to server position
        // Apply knockback over multiple frames worth (30 pixels = ~5 server ticks worth of knockback)
        const knockbackDistance = knockbackForce * 5;
        const newX = monster.x + (attackDirection * knockbackDistance);
        
        // Clamp to patrol bounds
        if (monster.patrolMinX !== undefined && monster.patrolMaxX !== undefined) {
            monster.x = Math.max(monster.patrolMinX, Math.min(monster.patrolMaxX, newX));
        } else {
            monster.x = newX;
        }
        
        // Set knockback state to prevent AI from immediately moving back
        monster.knockbackEndTime = Date.now() + 500; // 500ms knockback duration
        
        if (DEBUG) console.log(`[Server] Knockback applied: monster ${monsterId} moved to x=${monster.x}, knockbackVelocityX=${knockbackVelocityX}`);
    }
    
    // Check for prediction mismatch (only if client sent predicted HP)
    let correction = null;
    const HP_CORRECTION_THRESHOLD = 50;
    if (predictedHp !== undefined && seq) {
        const hpDifference = Math.abs(monster.hp - predictedHp);
        if (hpDifference > HP_CORRECTION_THRESHOLD) {
            console.log(`[Prediction] HP mismatch for seq=${seq}: predicted=${predictedHp}, actual=${monster.hp}, diff=${hpDifference}`);
            correction = {
                correctHp: monster.hp,
                maxHp: monster.maxHp
            };
        }
    }
    
    // Broadcast damage to all players on map (use validated damage)
    // Include sequence number so attacker can reconcile their prediction
    io.to(mapId).emit('monsterDamaged', {
        id: monsterId,
        seq: seq, // Include sequence number for prediction reconciliation
        damage: validatedDamage,
        currentHp: monster.hp,
        maxHp: monster.maxHp,
        attackerId: attackerId,
        knockbackVelocityX: knockbackVelocityX,
        isCritical: damage > validatedDamage // If damage was capped, wasn't a crit
    });
    
    // Check for death
    if (monster.hp <= 0) {
        return killMonster(mapId, monsterId);
    }
    
    // Return result with any correction needed
    return { monster, killed: false, correction: correction };
}

/**
 * Kill a monster and determine loot recipient
 */
function killMonster(mapId, monsterId) {
    if (!mapMonsters[mapId] || !mapMonsters[mapId][monsterId]) return null;
    
    const monster = mapMonsters[mapId][monsterId];
    monster.isDead = true;
    monster.hp = 0;
    
    // Clean up elite tracking for this map if the elite monster died
    if (monster.isEliteMonster && currentEliteMonsters[mapId] === monsterId) {
        delete currentEliteMonsters[mapId];
    }
    
    // Find player who dealt most damage
    const damageMap = monsterDamage[monsterId] || {};
    let topDamager = null;
    let topDamage = 0;
    
    for (const [odId, damage] of Object.entries(damageMap)) {
        if (damage > topDamage) {
            topDamage = damage;
            topDamager = odId;
        }
    }
    
    console.log(`[Server] Monster ${monsterId} (${monster.type}) killed. Top damager: ${topDamager} with ${topDamage} damage`);
    
    // Generate drops server-side for consistency
    const drops = generateMonsterDrops(mapId, monster, monsterId);
    
    // Register all drops in server ground item tracking for pickup validation
    if (!mapGroundItems[mapId]) mapGroundItems[mapId] = {};
    for (const drop of drops) {
        if (drop.id) {
            mapGroundItems[mapId][drop.id] = {
                name: drop.name,
                x: drop.x,
                y: drop.y,
                droppedBy: '__monster__',
                timestamp: Date.now()
            };
        }
    }
    
    // Find party members of the killer for shared EXP
    const partyMembers = getPartyMembersOnMap(mapId, topDamager);
    
    // Broadcast death to all players with drops and party info
    io.to(mapId).emit('monsterKilled', {
        id: monsterId,
        type: monster.type,
        x: monster.x,
        y: monster.y,
        lootRecipient: topDamager, // Player who gets the loot
        drops: drops, // Server-generated drops
        partyMembers: partyMembers, // Party members who get shared EXP
        isEliteMonster: monster.isEliteMonster || false, // Elite status for client effects
        isShiny: monster.isShiny || false // Shiny status for client effects
    });
    
    // Clean up damage tracking
    delete monsterDamage[monsterId];
    
    // Skip respawn for Party Quest maps - monsters should not respawn
    if (mapId.startsWith('pq')) {
        console.log(`[Server] PQ map ${mapId} - skipping respawn for ${monster.type}`);
        // Remove monster immediately (no respawn timer)
        setTimeout(() => {
            if (mapMonsters[mapId] && mapMonsters[mapId][monsterId]) {
                delete mapMonsters[mapId][monsterId];
            }
        }, 1000); // Short delay to let death animation play
        return { monster, killed: true, lootRecipient: topDamager };
    }
    
    // Schedule respawn (keep monster data for animation timing)
    const respawnTime = monster.isMiniBoss ? CONFIG.BOSS_RESPAWN_TIME : CONFIG.RESPAWN_TIME;
    
    // Store spawn info for respawn - don't use exact spawn coords, let it randomize
    // Use stored surface bounds if available, otherwise reconstruct from patrol
    const respawnData = {
        // Don't set x/y - let spawnMonster randomize within surface bounds
        surfaceX: monster.patrolSurfaceX !== undefined ? monster.patrolSurfaceX : monster.patrolMinX - 20,
        surfaceWidth: monster.patrolSurfaceWidth !== undefined ? monster.patrolSurfaceWidth : (monster.patrolMaxX + 20) - (monster.patrolMinX - 20),
        y: monster.spawnY, // Use same Y as original spawn
        mapWidth: monster.mapWidth,
        groundY: monster.groundY,
        maxHp: monster.maxHp
    };
    
    // Store monster type for respawn (in case map data is cleared)
    const monsterType = monster.type;
    
    setTimeout(() => {
        // SAFETY CHECK: Make sure map still exists before trying to delete/respawn
        // This prevents crashes when map is cleaned up while respawn is pending
        if (!mapMonsters[mapId]) {
            console.log(`[Server] Map ${mapId} no longer exists, skipping respawn for ${monsterId}`);
            return;
        }
        
        // Remove dead monster (with additional safety check)
        if (mapMonsters[mapId][monsterId]) {
            delete mapMonsters[mapId][monsterId];
        }
        
        // Spawn replacement if map still has players
        if (maps[mapId] && Object.keys(maps[mapId]).length > 0) {
            // Respawn with randomized position on same surface
            spawnMonster(mapId, monsterType, respawnData);
        }
    }, respawnTime);
    
    return { monster, killed: true, lootRecipient: topDamager };
}

/**
 * Generate drops for a monster (server-side for consistency)
 */
function generateMonsterDrops(mapId, monster, monsterId) {
    const drops = [];
    const monsterTypeData = mapSpawnData[mapId]?.monsterTypes?.[monster.type];
    
    if (!monsterTypeData || !monsterTypeData.loot) {
        return drops;
    }
    
    const baseX = monster.x + (monster.width || 40) / 2;
    const baseY = monster.y + (monster.height || 40) / 2;
    let dropIndex = 0;
    
    // ELITE MONSTER SPECIAL DROPS
    if (monster.isEliteMonster) {
        // Elite Gold (50k-100k)
        const eliteGoldAmount = Math.floor(50000 + Math.random() * 50000);
        drops.push({
            id: `drop_${Date.now()}_${dropIndex++}_${Math.random().toString(36).substr(2, 9)}`,
            name: 'Gold',
            x: baseX - 40,
            y: baseY,
            amount: eliteGoldAmount,
            velocityX: -2,
            velocityY: -4
        });
        
        // Guaranteed Gachapon Tickets (2-5)
        const ticketCount = Math.floor(2 + Math.random() * 4);
        for (let i = 0; i < ticketCount; i++) {
            drops.push({
                id: `drop_${Date.now()}_${dropIndex++}_${Math.random().toString(36).substr(2, 9)}`,
                name: 'Gachapon Ticket',
                x: baseX - 20 + (i * 15),
                y: baseY,
                velocityX: (Math.random() * 2) - 1,
                velocityY: -3 - (Math.random() * 2)
            });
        }
        
        // Guaranteed Enhancement Scrolls (4-8)
        const scrollCount = Math.floor(4 + Math.random() * 5);
        for (let i = 0; i < scrollCount; i++) {
            drops.push({
                id: `drop_${Date.now()}_${dropIndex++}_${Math.random().toString(36).substr(2, 9)}`,
                name: 'Enhancement Scroll',
                x: baseX + 20 + (i * 15),
                y: baseY,
                velocityX: (Math.random() * 2) - 1,
                velocityY: -3 - (Math.random() * 2)
            });
        }
    }
    
    // Elite monsters have 3x drop rate for regular loot
    const dropRateMultiplier = monster.isEliteMonster ? 3 : 1;
    
    for (const loot of monsterTypeData.loot) {
        const roll = Math.random();
        if (roll < ((loot.rate || 0.1) * dropRateMultiplier)) {
            // Generate consistent velocity for this drop
            const velocityX = (Math.random() * 4) - 2; // -2 to 2
            const velocityY = -3 - (Math.random() * 2); // -3 to -5 (upward)
            
            dropIndex++;
            if (loot.name === 'Gold') {
                const baseGoldAmount = Math.floor(Math.random() * ((loot.max || 10) - (loot.min || 1) + 1) + (loot.min || 1));
                const goldAmount = monster.isEliteMonster ? baseGoldAmount * 20 : baseGoldAmount;
                drops.push({
                    id: `drop_${Date.now()}_${dropIndex}_${Math.random().toString(36).substr(2, 9)}`,
                    name: 'Gold',
                    x: baseX + (dropIndex * 10),
                    y: baseY,
                    amount: goldAmount,
                    velocityX: velocityX,
                    velocityY: velocityY
                });
            } else {
                drops.push({
                    id: `drop_${Date.now()}_${dropIndex}_${Math.random().toString(36).substr(2, 9)}`,
                    name: loot.name,
                    x: baseX + (dropIndex * 10),
                    y: baseY,
                    velocityX: velocityX,
                    velocityY: velocityY
                });
            }
        }
    }
    
    // Salami Celebration Event: 20% chance to drop Salami Stick from any monster
    if (Math.random() < 0.2) {
        dropIndex++;
        drops.push({
            id: `drop_${Date.now()}_${dropIndex}_${Math.random().toString(36).substr(2, 9)}`,
            name: 'Salami Stick',
            x: baseX,
            y: baseY,
            velocityX: (Math.random() * 4) - 2,
            velocityY: -3 - (Math.random() * 2)
        });
    }
    
    return drops;
}

/**
 * Get party members of a player who are on the same map
 */
function getPartyMembersOnMap(mapId, playerOdId) {
    if (!maps[mapId] || !playerOdId) return [];
    
    const player = maps[mapId][playerOdId];
    if (!player || !player.partyId) {
        return [];
    }
    
    const partyMembers = [];
    for (const odId in maps[mapId]) {
        const p = maps[mapId][odId];
        if (p.odId !== playerOdId && p.partyId === player.partyId) {
            partyMembers.push(p.odId);
        }
    }
    
    if (DEBUG) console.log(`[Server] Found ${partyMembers.length} party members for ${playerOdId}:`, partyMembers);
    return partyMembers;
}

/**
 * Get all monsters on a map
 */
function getMapMonsters(mapId) {
    if (!mapMonsters[mapId]) return [];
    return Object.values(mapMonsters[mapId]).filter(m => !m.isDead);
}

io.on('connection', (socket) => {
    console.log(`[Server] Player connected: ${socket.id}`);
    
    // Issue #10: Send server start time so clients can detect restarts
    socket.emit('serverStartTime', { time: SERVER_START_TIME });
    
    let currentPlayer = null;
    let currentMapId = null;

    /**
     * Ping/Pong for latency measurement (using custom event names to avoid Socket.io reserved names)
     */
    socket.on('latencyPing', () => {
        socket.emit('latencyPong');
    });

    /**
     * Player joins the game with their character data
     */
    socket.on('join', (data) => {
        const { odId, name, mapId, x, y, customization, level, playerClass, guild, equipped, cosmeticEquipped, equippedMedal, displayMedals, partyId } = data;
        
        if (DEBUG) console.log(`[Server] Player ${name} joining with partyId: ${partyId}`);
        
        if (!odId || !name || !mapId) {
            socket.emit('error', { message: 'Invalid join data' });
            return;
        }

        // Store player data
        currentPlayer = {
            odId,
            name,
            x: x || 400,
            y: y || 300,
            mapId,
            facing: 'right',
            animationState: 'idle',
            customization: (customization && customization.skinTone !== undefined) ? customization : { skinTone: 0, hairStyle: 0, hairColor: 0, eyeColor: 0 },
            level: level || 1,
            playerClass: playerClass || 'beginner',
            guild: guild || null,
            equipped: equipped || {},
            cosmeticEquipped: cosmeticEquipped || {},
            equippedMedal: equippedMedal || null,
            displayMedals: displayMedals || [],
            partyId: partyId || null, // Track party for EXP sharing
            lastUpdate: Date.now(),
            socketId: socket.id
        };
        currentMapId = mapId;

        // Track socket -> player mapping
        playerSockets[odId] = socket.id;

        // Initialize map if needed
        if (!maps[mapId]) {
            maps[mapId] = {};
        }

        // Add player to map
        maps[mapId][odId] = currentPlayer;

        // Join the map's socket room
        socket.join(mapId);

        // Send current players on this map to the new player
        const otherPlayers = Object.values(maps[mapId]).filter(p => p.odId !== odId);
        socket.emit('currentPlayers', otherPlayers);

        // Send existing monsters on this map to the new player
        if (mapMonsters[mapId] && Object.keys(mapMonsters[mapId]).length > 0) {
            const existingMonsters = getMapMonsters(mapId);
            if (DEBUG) console.log(`[Server] Sending ${existingMonsters.length} existing monsters to ${name}`);
            socket.emit('currentMonsters', existingMonsters);
        }

        // Notify other players on this map about the new player
        socket.to(mapId).emit('playerJoined', currentPlayer);

        console.log(`[Server] ${name} joined map ${mapId} (${Object.keys(maps[mapId]).length} players on map)`);
        if (DEBUG) console.log(`[Server] Player equipment:`, JSON.stringify(equipped));
    });

    /**
     * Player rejoins with a different character (character switch)
     * This cleans up the old character and joins with new character data
     */
    socket.on('rejoin', (data) => {
        const { odId, name, mapId, x, y, customization, level, playerClass, guild, equipped, cosmeticEquipped, equippedMedal, displayMedals, partyId, oldOdId } = data;
        
        console.log(`[Server] Player switching character: ${oldOdId || 'unknown'} -> ${name} (${odId})`);
        
        if (!odId || !name || !mapId) {
            socket.emit('error', { message: 'Invalid rejoin data' });
            return;
        }

        // Clean up old character data if it exists
        if (currentPlayer && currentMapId) {
            // Remove old player from their map
            if (maps[currentMapId] && maps[currentMapId][currentPlayer.odId]) {
                delete maps[currentMapId][currentPlayer.odId];
            }
            // Also check for old odId explicitly
            if (oldOdId && maps[currentMapId] && maps[currentMapId][oldOdId]) {
                delete maps[currentMapId][oldOdId];
            }
            
            // Notify others that old character left
            socket.to(currentMapId).emit('playerLeft', { odId: currentPlayer.odId });
            if (oldOdId && oldOdId !== currentPlayer.odId) {
                socket.to(currentMapId).emit('playerLeft', { odId: oldOdId });
            }
            
            // Remove old socket mapping
            delete playerSockets[currentPlayer.odId];
            if (oldOdId) delete playerSockets[oldOdId];
            
            // Leave old map room
            socket.leave(currentMapId);
            
            console.log(`[Server] Cleaned up old character: ${currentPlayer.name}`);
        }

        // Store new player data
        currentPlayer = {
            odId,
            name,
            x: x || 400,
            y: y || 300,
            mapId,
            facing: 'right',
            animationState: 'idle',
            customization: (customization && customization.skinTone !== undefined) ? customization : { skinTone: 0, hairStyle: 0, hairColor: 0, eyeColor: 0 },
            level: level || 1,
            playerClass: playerClass || 'beginner',
            guild: guild || null,
            equipped: equipped || {},
            cosmeticEquipped: cosmeticEquipped || {},
            equippedMedal: equippedMedal || null,
            displayMedals: displayMedals || [],
            partyId: partyId || null,
            lastUpdate: Date.now(),
            socketId: socket.id
        };
        currentMapId = mapId;

        // Track socket -> player mapping
        playerSockets[odId] = socket.id;

        // Initialize map if needed
        if (!maps[mapId]) {
            maps[mapId] = {};
        }

        // Add player to map
        maps[mapId][odId] = currentPlayer;

        // Join the map's socket room
        socket.join(mapId);

        // Send current players on this map to the new player
        const otherPlayers = Object.values(maps[mapId]).filter(p => p.odId !== odId);
        socket.emit('currentPlayers', otherPlayers);

        // Send existing monsters on this map
        if (mapMonsters[mapId] && Object.keys(mapMonsters[mapId]).length > 0) {
            const existingMonsters = getMapMonsters(mapId);
            socket.emit('currentMonsters', existingMonsters);
        }

        // Notify other players on this map about the new player
        socket.to(mapId).emit('playerJoined', currentPlayer);

        console.log(`[Server] ${name} rejoined on map ${mapId} (${Object.keys(maps[mapId]).length} players on map)`);
    });

    /**
     * Player position/state update
     */
    socket.on('updatePosition', (data) => {
        if (!currentPlayer || !currentMapId) return;

        const { x, y, facing, animationState, velocityX, velocityY, activeBuffs, pet } = data;

        // Update player data
        currentPlayer.x = x;
        currentPlayer.y = y;
        currentPlayer.facing = facing || currentPlayer.facing;
        currentPlayer.animationState = animationState || 'idle';
        currentPlayer.velocityX = velocityX || 0;
        currentPlayer.velocityY = velocityY || 0;
        currentPlayer.activeBuffs = activeBuffs || [];
        currentPlayer.pet = pet || null;
        currentPlayer.lastUpdate = Date.now();

        // Broadcast to other players on the same map
        const moveData = {
            odId: currentPlayer.odId,
            x,
            y,
            facing,
            animationState,
            velocityX,
            velocityY,
            activeBuffs: currentPlayer.activeBuffs
        };
        if (currentPlayer.pet) {
            moveData.pet = currentPlayer.pet;
        }
        socket.to(currentMapId).emit('playerMoved', moveData);
    });

    /**
     * Player changes map
     */
    socket.on('changeMap', (data) => {
        if (!currentPlayer) return;

        const { newMapId, x, y } = data;
        const oldMapId = currentMapId;

        // Remove from old map
        if (maps[oldMapId] && maps[oldMapId][currentPlayer.odId]) {
            delete maps[oldMapId][currentPlayer.odId];
            socket.leave(oldMapId);
            socket.to(oldMapId).emit('playerLeft', { odId: currentPlayer.odId });
            
            // If old map is now empty, clean up monster data
            // so next visitor triggers fresh spawn initialization
            if (Object.keys(maps[oldMapId]).length === 0) {
                delete maps[oldMapId];
                if (mapMonsters[oldMapId]) {
                    delete mapMonsters[oldMapId];
                    delete mapSpawnData[oldMapId];
                    console.log(`[Server] Cleaned up empty map on map change: ${oldMapId}`);
                }
                // Clean up ground item tracking
                if (mapGroundItems[oldMapId]) {
                    delete mapGroundItems[oldMapId];
                }
            }
        }

        // Add to new map
        currentMapId = newMapId;
        currentPlayer.mapId = newMapId;
        currentPlayer.x = x || 400;
        currentPlayer.y = y || 300;

        if (!maps[newMapId]) {
            maps[newMapId] = {};
        }
        maps[newMapId][currentPlayer.odId] = currentPlayer;

        // Join new map room
        socket.join(newMapId);

        // Send current players on new map
        const otherPlayers = Object.values(maps[newMapId]).filter(p => p.odId !== currentPlayer.odId);
        socket.emit('currentPlayers', otherPlayers);

        // Send current monsters on new map (if already initialized)
        if (mapMonsters[newMapId]) {
            socket.emit('currentMonsters', getMapMonsters(newMapId));
        }

        // Notify players on new map
        socket.to(newMapId).emit('playerJoined', currentPlayer);

        console.log(`[Server] ${currentPlayer.name} moved from ${oldMapId} to ${newMapId}`);
    });

    /**
     * Player chat message (local/map chat)
     */
    socket.on('chatMessage', (data) => {
        if (!currentPlayer || !currentMapId) return;

        const { message } = data;
        
        if (DEBUG) console.log(`[Server] Chat from ${currentPlayer.name} on ${currentMapId}:`, message);
        // Broadcast chat bubble to other players on map
        const chatData = {
            odId: currentPlayer.odId,
            name: currentPlayer.name,
            message
        };
        socket.to(currentMapId).emit('playerChat', chatData);
    });

    /**
     * Initialize monsters for a map (sent by first player to join)
     */
    socket.on('initMapMonsters', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        const { mapId, monsters, spawnPositions, mapWidth, groundY, monsterTypes: clientMonsterTypes } = data;
        
        // Store monster type data from client if not already stored
        if (clientMonsterTypes && !mapSpawnData[mapId]?.monsterTypes) {
            if (!mapSpawnData[mapId]) mapSpawnData[mapId] = {};
            mapSpawnData[mapId].monsterTypes = clientMonsterTypes;
        }
        
        // Only initialize if not already done
        if (mapMonsters[mapId] && Object.keys(mapMonsters[mapId]).length > 0) {
            // Map already has monsters - send current state
            socket.emit('currentMonsters', getMapMonsters(mapId));
            return;
        }
        
        if (DEBUG) console.log(`[Server] Initializing monsters for ${mapId}:`, monsters);
        if (spawnPositions && DEBUG) {
            console.log(`[Server] Received ${spawnPositions.length} pre-calculated spawn positions`);
        }
        
        // Initialize this map's monsters with pre-calculated positions
        initializeMapMonsters(mapId, {
            monsters,
            spawnPositions,
            mapWidth,
            groundY,
            monsterTypes: clientMonsterTypes
        });
        
        // Send initialized monsters back to all players on map
        io.to(mapId).emit('currentMonsters', getMapMonsters(mapId));
    });

    /**
     * Player attacks a monster (with client-side prediction support)
     */
    socket.on('attackMonster', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        const { seq, monsterId, damage, isCritical, attackType, playerDirection, predictedHp } = data;
        
        if (DEBUG) console.log(`[Server] Attack received from ${currentPlayer.name}: seq=${seq}, monster ${monsterId}, damage ${damage}`);
        
        // Validate monster exists and is on this map
        if (!mapMonsters[currentMapId] || !mapMonsters[currentMapId][monsterId]) {
            if (DEBUG) console.log(`[Server] Monster ${monsterId} not found on map ${currentMapId}`);
            // Send correction back to client - monster doesn't exist
            if (seq) {
                socket.emit('attackCorrection', {
                    seq: seq,
                    monsterId: monsterId,
                    type: 'attack_invalid',
                    reason: 'monster_not_found'
                });
            }
            return;
        }
        
        const result = damageMonster(currentMapId, monsterId, damage, currentPlayer.odId, playerDirection, seq, predictedHp);
        
        if (result && result.killed) {
            if (DEBUG) console.log(`[Server] ${currentPlayer.name} killed monster ${monsterId}, loot goes to ${result.lootRecipient}`);
        } else if (result && result.correction) {
            // Send HP correction to the attacker only
            socket.emit('attackCorrection', {
                seq: seq,
                monsterId: monsterId,
                type: 'hp_correction',
                correctHp: result.correction.correctHp,
                maxHp: result.correction.maxHp,
                reason: 'hp_mismatch'
            });
        }
    });

    /**
     * Player transformed a monster to elite (broadcast to all clients)
     */
    socket.on('transformElite', (data) => {
        if (DEBUG) {
            console.log(`[ELITE DEBUG Server] ===== RECEIVED transformElite event =====`);
            console.log(`[ELITE DEBUG Server] Data:`, data);
            console.log(`[ELITE DEBUG Server] Current player:`, currentPlayer?.name);
            console.log(`[ELITE DEBUG Server] Current map:`, currentMapId);
        }
        
        if (!currentPlayer || !currentMapId) {
            if (DEBUG) console.log(`[ELITE DEBUG Server] Transform received but no player/map`);
            return;
        }
        
        const { monsterId, maxHp, damage, originalMaxHp, originalDamage } = data;
        if (DEBUG) console.log(`[ELITE DEBUG Server] Transform request from ${currentPlayer.name}:`, { monsterId, mapId: currentMapId, maxHp, damage });
        
        // Update server monster state
        if (mapMonsters[currentMapId] && mapMonsters[currentMapId][monsterId]) {
            const monster = mapMonsters[currentMapId][monsterId];
            monster.isEliteMonster = true;
            monster.maxHp = maxHp;
            monster.hp = maxHp;
            monster.damage = damage;
            monster.originalMaxHp = originalMaxHp;
            monster.originalDamage = originalDamage;
            
            if (DEBUG) console.log(`[ELITE DEBUG Server] Monster ${monsterId} transformed to ELITE by ${currentPlayer.name}`);
            
            // Broadcast to ALL clients on map (including sender) so they all apply the transformation
            io.to(currentMapId).emit('monsterTransformedElite', {
                monsterId: monsterId,
                maxHp: maxHp,
                hp: maxHp,
                damage: damage,
                originalMaxHp: originalMaxHp,
                originalDamage: originalDamage
            });
        } else {
            if (DEBUG) console.log(`[ELITE DEBUG Server] Monster NOT FOUND:`, {
                hasMapMonsters: !!mapMonsters[currentMapId],
                hasThisMonster: mapMonsters[currentMapId] ? !!mapMonsters[currentMapId][monsterId] : false
            });
        }
    });

    /**
     * Player picks up an item - validate server-side then broadcast removal
     */
    socket.on('itemPickup', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        // Rate limit pickups
        if (!checkRateLimit(currentPlayer.odId, 'pickups', CONFIG.MAX_PICKUPS_PER_SECOND)) return;
        
        const { itemId, itemName, x, y } = data;
        
        // Server-side validation: check if the item actually exists on ground
        if (mapGroundItems[currentMapId] && mapGroundItems[currentMapId][itemId]) {
            // Item exists — remove from server tracking (first-come-first-served)
            delete mapGroundItems[currentMapId][itemId];
            
            if (DEBUG) console.log(`[Server] ${currentPlayer.name} picked up ${itemName} (${itemId}) - validated`);
            
            // Broadcast to ALL players on map so everyone removes the item
            io.to(currentMapId).emit('itemPickedUp', {
                itemId: itemId,
                itemName: itemName,
                x: x,
                y: y,
                pickedUpBy: currentPlayer.odId,
                pickedUpByName: currentPlayer.name
            });
        } else {
            // Item not found on server — already picked up by someone else
            if (DEBUG) console.log(`[Server] ${currentPlayer.name} tried to pick up ${itemName} (${itemId}) but it's already gone`);
            
            // Tell the requesting player the pickup was rejected
            socket.emit('itemPickupRejected', {
                itemId: itemId,
                itemName: itemName,
                reason: 'already_picked_up'
            });
        }
    });

    /**
     * Player drops an item on the ground (from inventory or GM spawn)
     * Server assigns canonical ID and broadcasts to ALL players
     */
    socket.on('playerDropItem', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        const { name, x, y, stats, rarity, enhancement, quantity, levelReq, isQuestItem, isGold, amount } = data;
        
        if (DEBUG) console.log(`[Server] ${currentPlayer.name} dropped ${name} at (${x}, ${y})`);
        
        // Server assigns canonical ID — all clients MUST use this ID
        const dropId = `pdrop_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
        const velocityX = (Math.random() * 4) - 2;
        const velocityY = -3 - (Math.random() * 2);
        
        // Track on server for pickup validation
        if (!mapGroundItems[currentMapId]) mapGroundItems[currentMapId] = {};
        mapGroundItems[currentMapId][dropId] = {
            name, x, y,
            droppedBy: currentPlayer.odId,
            timestamp: Date.now()
        };
        
        const dropData = {
            name,
            x,
            y,
            id: dropId,
            velocityX,
            velocityY,
            stats: stats || null,
            rarity: rarity || null,
            enhancement: enhancement || 0,
            quantity: quantity || 1,
            levelReq: levelReq || 0,
            isQuestItem: isQuestItem || false,
            isGold: isGold || false,
            amount: amount || 0,
            droppedBy: currentPlayer.name
        };
        
        // Broadcast to OTHER players on the map
        socket.to(currentMapId).emit('playerItemDropped', dropData);
        
        // Send canonical ID back to sender so their local item uses the same ID
        socket.emit('playerDropConfirm', {
            id: dropId,
            velocityX,
            velocityY
        });
    });

    /**
     * Player updates their HP/stats for party tracking
     */
    /**
     * Update party info (called when player joins/leaves a party)
     */
    socket.on('updateParty', (data) => {
        if (!currentPlayer) return;
        
        const oldPartyId = currentPlayer.partyId;
        currentPlayer.partyId = data.partyId || null;
        
        if (DEBUG) console.log(`[${currentPlayer.name}] Party updated: ${oldPartyId} -> ${currentPlayer.partyId}`);
        
        // Broadcast to others on map so they know about party change
        if (currentMapId) {
            socket.to(currentMapId).emit('playerPartyUpdated', {
                odId: currentPlayer.odId,
                name: currentPlayer.name,
                partyId: currentPlayer.partyId
            });
        }
    });

    socket.on('updatePartyStats', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        const { hp, maxHp, level, exp, maxExp } = data;
        
        // Update player data
        currentPlayer.hp = hp;
        currentPlayer.maxHp = maxHp;
        currentPlayer.level = level;
        currentPlayer.exp = exp;
        currentPlayer.maxExp = maxExp;
        
        // Only broadcast to party members on same map
        if (currentPlayer.partyId) {
            const partyUpdate = {
                odId: currentPlayer.odId,
                name: currentPlayer.name,
                hp: hp,
                maxHp: maxHp,
                level: level,
                exp: exp,
                maxExp: maxExp
            };
            
            // Broadcast to all players on map (they'll filter by party)
            socket.to(currentMapId).emit('partyMemberStats', partyUpdate);
        }
    });

    /**
     * Share gold with party members
     */
    socket.on('sharePartyGold', (data) => {
        if (!currentPlayer || !currentMapId || !currentPlayer.partyId) return;
        
        const { totalAmount } = data;
        if (!totalAmount || totalAmount <= 0) return;
        
        // Find party members on the same map (excluding looter)
        const partyMembers = getPartyMembersOnMap(currentMapId, currentPlayer.odId);
        
        // Total members = party members + the looter
        const totalMembers = partyMembers.length + 1;
        
        if (totalMembers <= 1) {
            // No party members on map, looter keeps all
            console.log(`[Server] ${currentPlayer.name} - no party members on map, keeping all ${totalAmount} gold`);
            return;
        }
        
        // Split evenly among all members - minimum 1 gold per member
        // Use ceiling to ensure everyone gets at least 1 gold (except when 0)
        const rawShare = totalAmount / totalMembers;
        const sharePerMember = Math.max(1, Math.ceil(rawShare));
        // Looter might get less to compensate (minimum 1)
        const totalDistributed = sharePerMember * (totalMembers - 1);
        const looterShare = Math.max(1, totalAmount - totalDistributed);
        
        console.log(`[Server] ${currentPlayer.name} sharing ${totalAmount} gold: ${sharePerMember} to ${partyMembers.length} members, ${looterShare} kept`);
        
        // Send gold to each party member
        for (const memberOdId of partyMembers) {
            // Find the socket for this party member
            for (const [socketId, playerData] of Object.entries(maps[currentMapId] || {})) {
                if (playerData.odId === memberOdId) {
                    io.to(socketId).emit('partyGoldShare', {
                        amount: sharePerMember,
                        fromName: currentPlayer.name
                    });
                    break;
                }
            }
        }
        
        // Tell the looter how much they actually get (their share)
        socket.emit('partyGoldShareResult', {
            originalAmount: totalAmount,
            yourShare: looterShare,
            memberCount: totalMembers
        });
    });

    /**
     * Broadcast VFX event to other players on the same map
     */
    socket.on('playerVFX', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        // Relay VFX to other players on the map
        socket.to(currentMapId).emit('remotePlayerVFX', {
            odId: currentPlayer.odId,
            vfxType: data.vfxType,
            x: data.x,
            y: data.y
        });
    });

    /**
     * Broadcast projectile event to other players on the same map
     * Projectiles are visual-only for remote players (damage is calculated locally)
     */
    socket.on('playerProjectile', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        if (DEBUG) console.log(`[Server] Relaying projectile from ${currentPlayer.odId}, id: ${data.projectileId}`);
        
        // Relay projectile to other players on the map
        socket.to(currentMapId).emit('remoteProjectile', {
            odId: currentPlayer.odId,
            projectileId: data.projectileId,
            spriteName: data.spriteName,
            x: data.x,
            y: data.y,
            velocityX: data.velocityX,
            velocityY: data.velocityY,
            angle: data.angle || 0,
            isGrenade: data.isGrenade || false,
            isHoming: data.isHoming || false
        });
    });

    /**
     * Broadcast projectile hit event to other players on the same map
     * This tells remote clients to stop/remove a projectile when it hits a target
     */
    socket.on('playerProjectileHit', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        if (DEBUG) console.log(`[Server] Relaying projectile HIT from ${currentPlayer.odId}, id: ${data.projectileId}`);
        
        // Relay projectile hit to other players on the map
        socket.to(currentMapId).emit('remoteProjectileHit', {
            odId: currentPlayer.odId,
            projectileId: data.projectileId,
            x: data.x,
            y: data.y
        });
    });

    /**
     * Broadcast skill VFX event to other players on the same map
     * Skill VFX are visual-only for remote players (melee slashes, spell effects, etc.)
     */
    socket.on('playerSkillVFX', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        // Relay skill VFX to other players on the map
        socket.to(currentMapId).emit('remoteSkillVFX', {
            odId: currentPlayer.odId,
            effectName: data.effectName,
            x: data.x,
            y: data.y,
            width: data.width || 150,
            height: data.height || 150,
            facing: data.facing || 'right',
            duration: data.duration || 300
        });
    });

    /**
     * Request current monsters on map (for late joiners)
     */
    socket.on('requestMonsters', () => {
        if (!currentMapId) return;
        
        const monsters = getMapMonsters(currentMapId);
        socket.emit('currentMonsters', monsters);
    });

    /**
     * Player updates their appearance (equipment, cosmetics, guild, medal)
     */
    socket.on('updateAppearance', (data) => {
        if (DEBUG) console.log(`[Server] Received updateAppearance from ${currentPlayer?.name || 'unknown'}`);
        if (!currentPlayer || !currentMapId) {
            if (DEBUG) console.warn('[Server] updateAppearance ignored - no currentPlayer or mapId');
            return;
        }
        
        // Update player data on server
        if (data.equipped !== undefined) {
            currentPlayer.equipped = data.equipped;
        }
        if (data.cosmeticEquipped !== undefined) {
            currentPlayer.cosmeticEquipped = data.cosmeticEquipped;
        }
        if (data.guild !== undefined) {
            currentPlayer.guild = data.guild;
        }
        if (data.equippedMedal !== undefined) {
            currentPlayer.equippedMedal = data.equippedMedal;
        }
        if (data.displayMedals !== undefined) {
            currentPlayer.displayMedals = data.displayMedals;
        }
        if (data.customization && data.customization.skinTone !== undefined) {
            currentPlayer.customization = data.customization;
        }
        
        // Broadcast appearance update to other players on the map
        const broadcastData = {
            odId: currentPlayer.odId,
            equipped: currentPlayer.equipped,
            cosmeticEquipped: currentPlayer.cosmeticEquipped,
            customization: currentPlayer.customization,
            guild: currentPlayer.guild,
            equippedMedal: currentPlayer.equippedMedal,
            displayMedals: currentPlayer.displayMedals
        };
        socket.to(currentMapId).emit('playerAppearanceUpdated', broadcastData);
        
        console.log(`[Server] ${currentPlayer.name} updated appearance, broadcasting to map ${currentMapId}`);
        if (DEBUG) console.log(`[Server] Appearance data:`, broadcastData);
    });

    /**
     * Player death - broadcast to other players on map
     */
    socket.on('playerDeath', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        console.log(`[Server] ${currentPlayer.name} died on ${currentMapId}`);
        
        // Broadcast death to all other players on the map
        socket.to(currentMapId).emit('playerDied', {
            odId: currentPlayer.odId,
            name: currentPlayer.name,
            x: data.x,
            y: data.y
        });
    });

    /**
     * Player respawn - broadcast to other players on map
     */
    socket.on('playerRespawn', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        console.log(`[Server] ${currentPlayer.name} respawned`);
        
        // Broadcast respawn to all other players on the map
        socket.to(currentMapId).emit('playerRespawned', {
            odId: currentPlayer.odId
        });
    });

    /**
     * GM Authentication - requires password set in GM_PASSWORD environment variable
     * This keeps the password server-side only, not visible in client code
     */
    socket.on('gmAuth', (data) => {
        const { password } = data;
        
        // Check if GM password is configured
        if (!CONFIG.GM_PASSWORD) {
            console.warn(`[Security] GM auth attempted but GM_PASSWORD not configured`);
            socket.emit('gmAuthResult', { success: false, message: 'GM system not configured' });
            return;
        }
        
        // Validate password
        if (password === CONFIG.GM_PASSWORD) {
            authorizedGMs.add(socket.id);
            console.log(`[Security] GM authorized: ${currentPlayer?.name || 'unknown'} (${socket.id})`);
            socket.emit('gmAuthResult', { success: true, message: 'GM access granted' });
        } else {
            console.warn(`[Security] Failed GM auth attempt from ${currentPlayer?.name || 'unknown'} (${socket.id})`);
            socket.emit('gmAuthResult', { success: false, message: 'Invalid password' });
        }
    });

    /**
     * Check if current socket is GM authorized
     */
    socket.on('checkGmAuth', () => {
        const isAuthorized = authorizedGMs.has(socket.id);
        socket.emit('gmAuthStatus', { authorized: isAuthorized });
    });

    // ==========================================
    // PARTY QUEST SOCKET EVENTS
    // ==========================================
    
    // Store active party quests
    // Structure: { pqId_partyId: { pqId, partyId, members: [odId], currentStage, startTime, stageProgress } }
    
    /**
     * Start a party quest - transports all party members to the PQ Stage 1
     */
    socket.on('startPartyQuest', (data) => {
        const { pqId, partyId, leaderId, originalMap, originalX, originalY } = data;
        
        if (!currentPlayer || currentPlayer.odId !== leaderId) {
            socket.emit('pqError', { message: 'Only the party leader can start the party quest.' });
            return;
        }
        
        console.log(`[PQ] Starting Party Quest ${pqId} for party ${partyId}`);
        
        // Notify all players in the same party to warp to PQ Stage 1 (not lobby)
        io.emit('partyQuestStarted', {
            pqId,
            partyId,
            leaderId,
            targetMap: 'pqStage1',
            targetX: 200,
            targetY: 300,
            originalMap: originalMap || 'onyxCity',
            originalX: originalX || 600,
            originalY: originalY || 300
        });
    });
    
    /**
     * Player completes a PQ stage objective
     */
    socket.on('pqStageComplete', (data) => {
        const { pqId, partyId, stage } = data;
        
        console.log(`[PQ] Stage ${stage} completed for PQ ${pqId}, party ${partyId}`);
        
        // Determine next stage map
        const stageProgression = {
            1: { nextMap: 'pqStage2', nextX: 200, nextY: 300 },
            2: { nextMap: 'pqStage3', nextX: 200, nextY: 300 },
            3: { nextMap: 'pqStage4', nextX: 200, nextY: 300 },
            4: { nextMap: 'pqBoss', nextX: 200, nextY: 300 },
            5: { nextMap: 'pqReward', nextX: 500, nextY: 300 } // Boss stage
        };
        
        const nextStageInfo = stageProgression[stage];
        
        // Notify all party members that stage is complete
        io.emit('pqStageCleared', {
            pqId,
            partyId,
            stage,
            clearedBy: currentPlayer?.name || 'Unknown',
            nextMap: nextStageInfo?.nextMap,
            nextX: nextStageInfo?.nextX,
            nextY: nextStageInfo?.nextY,
            countdownSeconds: 10
        });
    });
    
    /**
     * Party Quest completed (boss defeated)
     */
    socket.on('pqCompleted', (data) => {
        const { pqId, partyId } = data;
        
        console.log(`[PQ] Party Quest ${pqId} completed by party ${partyId}`);
        
        // Notify all party members
        io.emit('partyQuestCompleted', {
            pqId,
            partyId,
            completedBy: currentPlayer?.name || 'Unknown'
        });
    });
    
    /**
     * Player leaves the party quest
     */
    socket.on('leavePQ', (data) => {
        const { pqId, partyId } = data;
        
        console.log(`[PQ] ${currentPlayer?.name || 'Unknown'} left PQ ${pqId}`);
        
        // Notify party members
        io.emit('pqMemberLeft', {
            pqId,
            partyId,
            playerName: currentPlayer?.name || 'Unknown',
            playerId: currentPlayer?.odId
        });
    });

    // ==========================================
    // CHESS GAME SOCKET EVENTS
    // ==========================================

    /**
     * Player wants to play chess - join waiting queue or match with waiting player
     */
    socket.on('chessJoin', (data) => {
        const { playerName, mapId } = data;
        if (!currentPlayer) return;

        // Check if someone is already waiting on this map
        if (chessWaiting[mapId] && chessWaiting[mapId].socketId !== socket.id) {
            const waiter = chessWaiting[mapId];
            delete chessWaiting[mapId];

            // Create a game - randomly assign colors
            const whiteIsWaiter = Math.random() < 0.5;
            const gameId = `chess_${Date.now()}_${Math.random().toString(36).substr(2, 6)}`;

            chessGames[gameId] = {
                whiteSocketId: whiteIsWaiter ? waiter.socketId : socket.id,
                blackSocketId: whiteIsWaiter ? socket.id : waiter.socketId,
                whiteName: whiteIsWaiter ? waiter.playerName : playerName,
                blackName: whiteIsWaiter ? playerName : waiter.playerName
            };

            // Notify both players
            io.to(waiter.socketId).emit('chessMatchFound', {
                gameId,
                opponentName: playerName,
                yourColor: whiteIsWaiter ? 'white' : 'black'
            });
            socket.emit('chessMatchFound', {
                gameId,
                opponentName: waiter.playerName,
                yourColor: whiteIsWaiter ? 'black' : 'white'
            });

            console.log(`[Chess] Match started: ${chessGames[gameId].whiteName} (white) vs ${chessGames[gameId].blackName} (black)`);
        } else {
            // No one waiting - add to queue
            chessWaiting[mapId] = { socketId: socket.id, playerName, gameId: data.gameId };
            console.log(`[Chess] ${playerName} waiting for opponent on ${mapId}`);
        }
    });

    /**
     * Player makes a chess move
     */
    socket.on('chessMove', (data) => {
        const { gameId, fromR, fromC, toR, toC, promotion } = data;
        const game = chessGames[gameId];
        if (!game) return;

        // Determine opponent socket
        const opponentSocketId = game.whiteSocketId === socket.id ? game.blackSocketId : game.whiteSocketId;

        // Forward move to opponent
        io.to(opponentSocketId).emit('chessOpponentMove', {
            fromR, fromC, toR, toC, promotion
        });
    });

    /**
     * Player resigns
     */
    socket.on('chessResign', (data) => {
        const { gameId } = data;
        const game = chessGames[gameId];
        if (!game) return;

        const opponentSocketId = game.whiteSocketId === socket.id ? game.blackSocketId : game.whiteSocketId;
        io.to(opponentSocketId).emit('chessOpponentResigned', {});

        delete chessGames[gameId];
        console.log(`[Chess] Game ${gameId} ended by resignation`);
    });

    /**
     * Player leaves chess (closes window)
     */
    socket.on('chessLeave', (data) => {
        const { gameId } = data;

        // Remove from waiting queue
        for (const mapId in chessWaiting) {
            if (chessWaiting[mapId].socketId === socket.id) {
                delete chessWaiting[mapId];
            }
        }

        // If in a game, notify opponent
        if (gameId && chessGames[gameId]) {
            const game = chessGames[gameId];
            const opponentSocketId = game.whiteSocketId === socket.id ? game.blackSocketId : game.whiteSocketId;
            io.to(opponentSocketId).emit('chessOpponentLeft', {});
            delete chessGames[gameId];
            console.log(`[Chess] Game ${gameId} ended - player left`);
        }
    });

    /**
     * Player disconnects
     */
    socket.on('disconnect', () => {
        // Clean up chess state on disconnect
        for (const mapId in chessWaiting) {
            if (chessWaiting[mapId].socketId === socket.id) {
                delete chessWaiting[mapId];
            }
        }
        for (const gameId in chessGames) {
            const game = chessGames[gameId];
            if (game.whiteSocketId === socket.id || game.blackSocketId === socket.id) {
                const opponentSocketId = game.whiteSocketId === socket.id ? game.blackSocketId : game.whiteSocketId;
                io.to(opponentSocketId).emit('chessOpponentLeft', {});
                delete chessGames[gameId];
            }
        }

        if (currentPlayer && currentMapId) {
            // Remove from map
            if (maps[currentMapId] && maps[currentMapId][currentPlayer.odId]) {
                delete maps[currentMapId][currentPlayer.odId];
            }

            // Remove socket mapping
            delete playerSockets[currentPlayer.odId];
            
            // Clean up rate limiter data
            cleanupRateLimiter(currentPlayer.odId);
            
            // Remove from GM authorized set
            authorizedGMs.delete(socket.id);

            // Notify other players
            socket.to(currentMapId).emit('playerLeft', { odId: currentPlayer.odId });

            console.log(`[Server] ${currentPlayer.name} disconnected from ${currentMapId}`);
            
            // If map is now empty, clean up monster data immediately
            // so next player triggers fresh spawn initialization with latest client logic
            if (maps[currentMapId] && Object.keys(maps[currentMapId]).length === 0) {
                delete maps[currentMapId];
                if (mapMonsters[currentMapId]) {
                    delete mapMonsters[currentMapId];
                    delete mapSpawnData[currentMapId];
                    console.log(`[Server] Cleaned up empty map on disconnect: ${currentMapId}`);
                }
                // Clean up ground item tracking
                if (mapGroundItems[currentMapId]) {
                    delete mapGroundItems[currentMapId];
                }
            }
        }
    });
});

// Health check endpoint
app.get('/', (req, res) => {
    const totalPlayers = Object.values(maps).reduce((sum, map) => sum + Object.keys(map).length, 0);
    const totalMonsters = Object.values(mapMonsters).reduce((sum, map) => sum + Object.keys(map).length, 0);
    res.json({
        status: 'ok',
        totalPlayers,
        totalMonsters,
        maps: Object.keys(maps).map(mapId => ({
            id: mapId,
            players: Object.keys(maps[mapId]).length,
            monsters: mapMonsters[mapId] ? Object.keys(mapMonsters[mapId]).length : 0
        }))
    });
});

// Cleanup inactive players periodically
setInterval(() => {
    const now = Date.now();
    for (const mapId in maps) {
        for (const odId in maps[mapId]) {
            if (now - maps[mapId][odId].lastUpdate > CONFIG.PLAYER_TIMEOUT) {
                const player = maps[mapId][odId];
                delete maps[mapId][odId];
                io.to(mapId).emit('playerLeft', { odId });
                console.log(`[Server] Removed inactive player: ${player.name}`);
            }
        }
        // Clean up empty maps - clear ALL map data when no players remain
        // This ensures fresh monster initialization with latest client spawn logic
        // Pending respawn timers safely check for mapMonsters[mapId] before acting
        if (Object.keys(maps[mapId]).length === 0) {
            delete maps[mapId];
            if (mapMonsters[mapId]) {
                delete mapMonsters[mapId];
                delete mapSpawnData[mapId];
                console.log(`[Server] Cleaned up empty map and monster data: ${mapId}`);
            }
            // Clean up ground item tracking
            if (mapGroundItems[mapId]) {
                delete mapGroundItems[mapId];
            }
        }
    }
}, 10000); // Check every 10 seconds

const PORT = process.env.PORT || 3001;
server.listen(PORT, '0.0.0.0', () => {
    console.log(`[Server] BennSauce Game Server running on port ${PORT}`);
});

// ====================================================
// ISSUE #1: Self keep-alive ping to prevent Render.com
// free-tier cold starts (spins down after 15min idle).
// Pings own health endpoint every 10 minutes.
// ====================================================
const SELF_URL = process.env.RENDER_EXTERNAL_URL || `http://localhost:${PORT}`;
setInterval(() => {
    try {
        const url = new URL(SELF_URL);
        const lib = url.protocol === 'https:' ? https : require('http');
        lib.get(SELF_URL, (res) => {
            if (DEBUG) console.log(`[KeepAlive] Self-ping OK (status ${res.statusCode})`);
        }).on('error', (err) => {
            if (DEBUG) console.warn('[KeepAlive] Self-ping failed:', err.message);
        });
    } catch (e) {
        if (DEBUG) console.warn('[KeepAlive] Invalid URL for self-ping:', SELF_URL);
    }
}, 10 * 60 * 1000); // Every 10 minutes
