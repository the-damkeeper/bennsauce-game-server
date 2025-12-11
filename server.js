/**
 * BennSauce Game Server
 * Real-time multiplayer server using Socket.io
 * 
 * Phase 1: Player position synchronization
 * Phase 2: Server-authoritative monsters (shared monsters)
 */

const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const cors = require('cors');

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
    MONSTER_AI_RATE: 100, // ms between monster AI updates (10 updates/sec)
    MONSTER_BROADCAST_RATE: 100, // ms between position broadcasts
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
    
    // GM Authentication - password is stored in environment variable
    // Set GM_PASSWORD environment variable on Render/hosting platform for production
    // Default password for development - CHANGE THIS IN PRODUCTION!
    GM_PASSWORD: process.env.GM_PASSWORD || 'bennsauce_gm_2024_secret'
};

// Authorized GM sessions (socket IDs that have been authenticated)
const authorizedGMs = new Set();

// Rate limiting trackers
// Structure: { odId: { attacks: [{timestamp}], pickups: [{timestamp}], positions: [{timestamp, x, y}] } }
const rateLimiters = {};

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
    
    // DEBUG: Log monster type data to verify canJump is being received
    console.log(`[Server] Spawning ${type} - canJump: ${monsterTypeData.canJump}, jumpForce: ${monsterTypeData.jumpForce}, monsterTypeData keys:`, Object.keys(monsterTypeData));
    
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
    
    console.log(`[Server] Spawned ${type} (${monsterId}) with ${maxHp} HP at (${Math.round(x)}, ${Math.round(y)})`);
    
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
 * Simple server-side monster AI
 */
function updateMonsterAI(monster, mapId) {
    // Skip AI for static monsters (like test dummy)
    if (monster.aiType === 'static') {
        monster.velocityX = 0;
        return;
    }
    
    // Skip AI during knockback - monster shouldn't move while being knocked back
    if (monster.knockbackEndTime && Date.now() < monster.knockbackEndTime) {
        monster.velocityX = 0;
        return;
    }
    
    const speedMultiplier = 4.2;
    const CHASE_TIMEOUT = 5000; // Stop chasing after 5 seconds of no interaction
    const CHASE_RANGE = 500; // How far monster can chase from spawn
    const now = Date.now();
    
    // --- PROXIMITY AGGRO DETECTION ---
    // Check for nearby players to aggro (if not already chasing)
    if (monster.aiState !== 'chasing' && maps[mapId]) {
        const playersOnMap = Object.values(maps[mapId]);
        let closestPlayer = null;
        let closestDist = monster.aggroRange || 250;
        
        for (const p of playersOnMap) {
            if (!p || p.isDead) continue;
            const dx = (p.x + 15) - (monster.x + monster.width / 2);
            const dy = (p.y + 30) - (monster.y + monster.height / 2);
            const dist = Math.sqrt(dx * dx + dy * dy);
            
            if (dist < closestDist) {
                closestDist = dist;
                closestPlayer = p;
            }
        }
        
        if (closestPlayer) {
            // Found a nearby player - aggro!
            monster.aiState = 'chasing';
            monster.targetPlayer = closestPlayer.odId;
            monster.lastInteractionTime = now;
            monster.chaseStartTime = now;
        }
    }
    
    // --- GRAVITY & JUMPING PHYSICS ---
    // Server runs at 10fps, client at 60fps. Scale physics accordingly.
    // Client GRAVITY = 0.4 at 60fps, so server needs ~0.4 * 6 = 2.4 per tick
    const SERVER_GRAVITY = 2.4;
    const groundLevel = monster.groundY - monster.height - 3; // Where the monster should land
    const isAboveGround = monster.y < groundLevel - 5; // Some threshold
    
    if (monster.isJumping || monster.isFalling || isAboveGround) {
        // Apply scaled gravity for server tick rate
        monster.velocityY = (monster.velocityY || 0) + SERVER_GRAVITY;
        monster.y += monster.velocityY;
        
        // Mark as falling if not jumping but above ground
        if (!monster.isJumping && isAboveGround) {
            monster.isFalling = true;
        }
        
        // Check if landed (hit ground level)
        if (monster.y >= groundLevel) {
            monster.y = groundLevel;
            monster.velocityY = 0;
            monster.isJumping = false;
            monster.isFalling = false;
        }
    }
    
    // Check if monster should stop chasing (timeout or target lost)
    if (monster.aiState === 'chasing') {
        const timeSinceInteraction = now - (monster.lastInteractionTime || 0);
        
        if (timeSinceInteraction > CHASE_TIMEOUT) {
            // Lost aggro - return to patrol
            monster.aiState = 'patrolling';
            monster.targetPlayer = null;
            monster.chaseStartTime = 0;
        } else if (monster.targetPlayer && maps[mapId]) {
            // Chase the target player
            const target = maps[mapId][monster.targetPlayer];
            if (target) {
                // Calculate direction to target
                const targetX = target.x + 15; // Center of player (width ~30)
                const dx = targetX - monster.x;
                
                // Only chase if within range from spawn
                const distFromSpawn = Math.abs(monster.x - monster.spawnX);
                if (distFromSpawn < CHASE_RANGE) {
                    monster.direction = dx > 0 ? 1 : -1;
                    monster.facing = monster.direction === 1 ? 'right' : 'left';
                    
                    // Move MUCH faster when chasing (2.5x patrol speed) - aggressive pursuit!
                    const chaseSpeed = (monster.speed || CONFIG.MONSTER_SPEED) * speedMultiplier * 2.5;
                    const moveAmount = monster.direction * chaseSpeed;
                    const newX = monster.x + moveAmount;
                    
                    // When chasing, allow falling off platforms - only respect map boundaries
                    // This makes monsters more threatening as they pursue players
                    if (newX >= 0 && newX <= monster.mapWidth - monster.width) {
                        monster.velocityX = moveAmount;
                        monster.x = newX;
                    } else {
                        // Hit map boundary - stop but keep facing target
                        monster.velocityX = 0;
                    }
                    
                    // --- JUMPING WHILE CHASING ---
                    // Jump frequently when chasing - especially if player is above
                    if (monster.canJump && !monster.isJumping && !monster.isFalling) {
                        const playerAbove = target.y < monster.y - 30;
                        const jumpChance = playerAbove ? 0.12 : 0.05; // 12% if player above, 5% otherwise
                        if (Math.random() < jumpChance) {
                            // Scale jump force for server tick rate (10fps vs 60fps)
                            // Jump forces are ~2.5x to match client physics feel
                            const baseJump = monster.jumpForce || -8;
                            monster.velocityY = baseJump * 2.5;
                            monster.isJumping = true;
                        }
                    }
                } else {
                    // Too far from spawn - return to patrol
                    monster.aiState = 'patrolling';
                    monster.targetPlayer = null;
                    monster.chaseStartTime = 0;
                }
            } else {
                // Target no longer on map - look for new target
                monster.targetPlayer = null;
                // Don't immediately drop aggro, proximity check will find new target
            }
        }
        monster.lastUpdate = now;
        return;
    }
    
    // Simple patrol behavior
    if (monster.aiState === 'patrolling' || monster.aiState === 'idle') {
        // Check if at patrol boundary BEFORE moving - turn around with 30px buffer
        if (monster.x <= monster.patrolMinX + 30) {
            monster.direction = 1;
            monster.facing = 'right';
        } else if (monster.x >= monster.patrolMaxX - 30) {
            monster.direction = -1;
            monster.facing = 'left';
        } else if (Math.random() < CONFIG.PATROL_CHANGE_CHANCE) {
            // Random chance to change direction (only if not at boundary)
            monster.direction *= -1;
            monster.facing = monster.direction === 1 ? 'right' : 'left';
        }
        
        // Move in current direction
        const moveAmount = monster.direction * (monster.speed || CONFIG.MONSTER_SPEED) * speedMultiplier;
        const newX = monster.x + moveAmount;
        
        // Only move if staying within patrol bounds
        if (newX >= monster.patrolMinX && newX <= monster.patrolMaxX) {
            monster.velocityX = moveAmount;
            monster.x = newX;
        } else {
            // Hit boundary - stop and turn around
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
        
        // --- RANDOM JUMPING WHILE PATROLLING ---
        if (monster.canJump && !monster.isJumping && !monster.isFalling) {
            const jumpChance = monster.isMiniBoss ? 0.04 : 0.02; // 4% for bosses, 2% for regular
            if (Math.random() < jumpChance) {
                // Scale jump force for server tick rate (10fps vs 60fps)
                const baseJump = monster.jumpForce || -6;
                monster.velocityY = baseJump * 2.5;
                monster.isJumping = true;
            }
        }
        
        // Clamp to map boundaries as safety net
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
 */
function broadcastMonsterPositions() {
    for (const mapId in mapMonsters) {
        // Skip if no players on this map
        if (!maps[mapId] || Object.keys(maps[mapId]).length === 0) continue;
        
        const monsterPositions = [];
        for (const monsterId in mapMonsters[mapId]) {
            const m = mapMonsters[mapId][monsterId];
            if (m.isDead) continue;
            
            monsterPositions.push({
                id: m.id,
                x: m.x,
                y: m.y,
                facing: m.facing,
                direction: m.direction,
                aiState: m.aiState,
                velocityX: m.velocityX || 0,
                velocityY: m.velocityY || 0,
                isJumping: m.isJumping || false,
                isFalling: m.isFalling || false
            });
        }
        
        if (monsterPositions.length > 0) {
            io.to(mapId).emit('monsterPositions', { monsters: monsterPositions });
        }
    }
}

/**
 * Handle monster damage from a player
 */
function damageMonster(mapId, monsterId, damage, attackerId, attackDirection) {
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
        
        console.log(`[Server] Knockback applied: monster ${monsterId} moved to x=${monster.x}, knockbackVelocityX=${knockbackVelocityX}`);
    }
    
    // Broadcast damage to all players on map (use validated damage)
    io.to(mapId).emit('monsterDamaged', {
        id: monsterId,
        damage: validatedDamage,
        currentHp: monster.hp,
        maxHp: monster.maxHp,
        attackerId: attackerId,
        knockbackVelocityX: knockbackVelocityX
    });
    
    // Check for death
    if (monster.hp <= 0) {
        return killMonster(mapId, monsterId);
    }
    
    return { monster, killed: false };
}

/**
 * Kill a monster and determine loot recipient
 */
function killMonster(mapId, monsterId) {
    if (!mapMonsters[mapId] || !mapMonsters[mapId][monsterId]) return null;
    
    const monster = mapMonsters[mapId][monsterId];
    monster.isDead = true;
    monster.hp = 0;
    
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
        isEliteMonster: monster.isEliteMonster || false // Elite status for client effects
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
            velocityY: -8
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
                velocityY: -7 - (Math.random() * 2)
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
                velocityY: -7 - (Math.random() * 2)
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
            const velocityY = -7 - (Math.random() * 3); // -7 to -10 (upward)
            
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
    
    // Guaranteed salami stick on baby slimes
    if (monster.type === 'babySlime' || monster.type === 'babyRedSlime' || monster.type === 'babyBlueSlime') {
        dropIndex++;
        drops.push({
            id: `drop_${Date.now()}_${dropIndex}_${Math.random().toString(36).substr(2, 9)}`,
            name: 'Salami Stick',
            x: baseX,
            y: baseY,
            velocityX: (Math.random() * 4) - 2,
            velocityY: -7 - (Math.random() * 3)
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
        console.log(`[Server] getPartyMembersOnMap - player ${playerOdId} has no partyId`);
        return [];
    }
    
    console.log(`[Server] Looking for party members with partyId: ${player.partyId}`);
    
    const partyMembers = [];
    for (const odId in maps[mapId]) {
        const p = maps[mapId][odId];
        console.log(`[Server] Checking player ${p.name} (${odId}) - partyId: ${p.partyId}`);
        if (p.odId !== playerOdId && p.partyId === player.partyId) {
            partyMembers.push(p.odId);
        }
    }
    
    console.log(`[Server] Found ${partyMembers.length} party members:`, partyMembers);
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
    
    let currentPlayer = null;
    let currentMapId = null;

    /**
     * Player joins the game with their character data
     */
    socket.on('join', (data) => {
        const { odId, name, mapId, x, y, customization, level, playerClass, guild, equipped, cosmeticEquipped, equippedMedal, displayMedals, partyId } = data;
        
        console.log(`[Server] Player ${name} joining with partyId: ${partyId}`);
        
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
            customization: customization || {},
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
            console.log(`[Server] Sending ${existingMonsters.length} existing monsters to ${name}`);
            socket.emit('currentMonsters', existingMonsters);
        }

        // Notify other players on this map about the new player
        socket.to(mapId).emit('playerJoined', currentPlayer);

        console.log(`[Server] ${name} joined map ${mapId} (${Object.keys(maps[mapId]).length} players on map)`);
        console.log(`[Server] Player equipment:`, JSON.stringify(equipped));
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
            customization: customization || {},
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

        const { x, y, facing, animationState, velocityX, velocityY } = data;

        // Update player data
        currentPlayer.x = x;
        currentPlayer.y = y;
        currentPlayer.facing = facing || currentPlayer.facing;
        currentPlayer.animationState = animationState || 'idle';
        currentPlayer.velocityX = velocityX || 0;
        currentPlayer.velocityY = velocityY || 0;
        currentPlayer.lastUpdate = Date.now();

        // Broadcast to other players on the same map
        socket.to(currentMapId).emit('playerMoved', {
            odId: currentPlayer.odId,
            x,
            y,
            facing,
            animationState,
            velocityX,
            velocityY
        });
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
        
        // Broadcast chat bubble to other players on map
        const chatData = {
            odId: currentPlayer.odId,
            name: currentPlayer.name,
            message
        };
        console.log(`[Server] Broadcasting chat from ${currentPlayer.name} to map ${currentMapId}:`, chatData);
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
        
        console.log(`[Server] Initializing monsters for ${mapId}:`, monsters);
        if (spawnPositions) {
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
     * Player attacks a monster
     */
    socket.on('attackMonster', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        const { monsterId, damage, isCritical, attackType, playerDirection } = data;
        
        console.log(`[Server] Attack received from ${currentPlayer.name}: monster ${monsterId}, damage ${damage}, playerDirection ${playerDirection}`);
        
        // Validate monster exists and is on this map
        if (!mapMonsters[currentMapId] || !mapMonsters[currentMapId][monsterId]) {
            console.log(`[Server] Monster ${monsterId} not found on map ${currentMapId}`);
            return;
        }
        
        const result = damageMonster(currentMapId, monsterId, damage, currentPlayer.odId, playerDirection);
        
        if (result && result.killed) {
            console.log(`[Server] ${currentPlayer.name} killed monster ${monsterId}, loot goes to ${result.lootRecipient}`);
        }
    });

    /**
     * Player transformed a monster to elite (broadcast to all clients)
     */
    socket.on('transformElite', (data) => {
        console.log(`[ELITE DEBUG Server] ===== RECEIVED transformElite event =====`);
        console.log(`[ELITE DEBUG Server] Data:`, data);
        console.log(`[ELITE DEBUG Server] Current player:`, currentPlayer?.name);
        console.log(`[ELITE DEBUG Server] Current map:`, currentMapId);
        
        if (!currentPlayer || !currentMapId) {
            console.log(`[ELITE DEBUG Server] Transform received but no player/map:`, {
                hasPlayer: !!currentPlayer,
                hasMap: !!currentMapId
            });
            return;
        }
        
        const { monsterId, maxHp, damage, originalMaxHp, originalDamage } = data;
        console.log(`[ELITE DEBUG Server] Transform request from ${currentPlayer.name}:`, {
            monsterId,
            mapId: currentMapId,
            maxHp,
            damage
        });
        
        // Update server monster state
        if (mapMonsters[currentMapId] && mapMonsters[currentMapId][monsterId]) {
            const monster = mapMonsters[currentMapId][monsterId];
            monster.isEliteMonster = true;
            monster.maxHp = maxHp;
            monster.hp = maxHp;
            monster.damage = damage;
            monster.originalMaxHp = originalMaxHp;
            monster.originalDamage = originalDamage;
            
            console.log(`[ELITE DEBUG Server] Monster ${monsterId} transformed to ELITE by ${currentPlayer.name}`);
            console.log(`[ELITE DEBUG Server] Broadcasting to room: ${currentMapId}`);
            
            // Broadcast to ALL clients on map (including sender) so they all apply the transformation
            io.to(currentMapId).emit('monsterTransformedElite', {
                monsterId: monsterId,
                maxHp: maxHp,
                hp: maxHp,
                damage: damage,
                originalMaxHp: originalMaxHp,
                originalDamage: originalDamage
            });
            
            console.log(`[ELITE DEBUG Server] Broadcast complete`);
        } else {
            console.log(`[ELITE DEBUG Server] Monster NOT FOUND:`, {
                hasMapMonsters: !!mapMonsters[currentMapId],
                hasThisMonster: mapMonsters[currentMapId] ? !!mapMonsters[currentMapId][monsterId] : false,
                availableMonsters: mapMonsters[currentMapId] ? Object.keys(mapMonsters[currentMapId]) : []
            });
        }
    });

    /**
     * Player picks up an item - broadcast to all players so they can remove it
     */
    socket.on('itemPickup', (data) => {
        if (!currentPlayer || !currentMapId) return;
        
        const { itemId, itemName, x, y } = data;
        
        console.log(`[Server] ${currentPlayer.name} picked up ${itemName} at (${x}, ${y})`);
        
        // Broadcast to ALL players on map (including sender) so everyone removes the item
        io.to(currentMapId).emit('itemPickedUp', {
            itemId: itemId,
            itemName: itemName,
            x: x,
            y: y,
            pickedUpBy: currentPlayer.odId,
            pickedUpByName: currentPlayer.name
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
        
        console.log(`[${currentPlayer.name}] Party updated: ${oldPartyId} -> ${currentPlayer.partyId}`);
        
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
        
        console.log(`[Server] Relaying projectile from ${currentPlayer.odId}, id: ${data.projectileId}`);
        
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
        
        console.log(`[Server] Relaying projectile HIT from ${currentPlayer.odId}, id: ${data.projectileId}`);
        
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
        console.log(`[Server] Received updateAppearance from ${currentPlayer?.name || 'unknown'} on map ${currentMapId || 'none'}`);
        if (!currentPlayer || !currentMapId) {
            console.warn('[Server] updateAppearance ignored - no currentPlayer or mapId');
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
        
        // Broadcast appearance update to other players on the map
        const broadcastData = {
            odId: currentPlayer.odId,
            equipped: currentPlayer.equipped,
            cosmeticEquipped: currentPlayer.cosmeticEquipped,
            guild: currentPlayer.guild,
            equippedMedal: currentPlayer.equippedMedal,
            displayMedals: currentPlayer.displayMedals
        };
        socket.to(currentMapId).emit('playerAppearanceUpdated', broadcastData);
        
        console.log(`[Server] ${currentPlayer.name} updated appearance, broadcasting to map ${currentMapId}:`, broadcastData);
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

    /**
     * Player disconnects
     */
    socket.on('disconnect', () => {
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
        // Clean up empty maps
        // Only delete monster data if no monsters are pending (prevents crash on respawn)
        if (Object.keys(maps[mapId]).length === 0) {
            delete maps[mapId];
            // Only clean up monster data if no monsters exist (all have respawned or been cleaned)
            if (mapMonsters[mapId] && Object.keys(mapMonsters[mapId]).length === 0) {
                delete mapMonsters[mapId];
                delete mapSpawnData[mapId];
                console.log(`[Server] Cleaned up empty map: ${mapId}`);
            }
        }
    }
}, 10000); // Check every 10 seconds

const PORT = process.env.PORT || 3001;
server.listen(PORT, '0.0.0.0', () => {
    console.log(`[Server] BennSauce Game Server running on port ${PORT}`);
});
