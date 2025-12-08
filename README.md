# BennSauce Game Server

Real-time multiplayer server for BennSauce game using Socket.io.

## Phase 1 Implementation

This is the Phase 1 implementation that allows players to see other players moving in real-time on the same map.

### Features
- Real-time player position synchronization
- Player customization/equipment display
- Map-based rooms (only see players on the same map)
- Smooth position interpolation on client
- Automatic cleanup of disconnected/inactive players

## Setup

### 1. Install Dependencies

```bash
cd game-server
npm install
```

### 2. Start the Server

```bash
npm start
```

Or for development with auto-restart:
```bash
npm run dev
```

The server will start on port 3001 by default.

### 3. Configure Client

The client (`socketClient.js`) is configured to connect to `http://localhost:3001` by default.

For production, change `SOCKET_CONFIG.SERVER_URL` in `socketClient.js` to your server's URL.

## API Reference

### Client → Server Events

| Event | Data | Description |
|-------|------|-------------|
| `join` | `{ odId, name, mapId, x, y, customization, level, playerClass, guild, equipped }` | Join the game server |
| `updatePosition` | `{ x, y, facing, animationState, velocityX, velocityY }` | Send position update |
| `changeMap` | `{ newMapId, x, y }` | Notify server of map change |
| `chatMessage` | `{ message }` | Send chat message to players on same map |

### Server → Client Events

| Event | Data | Description |
|-------|------|-------------|
| `currentPlayers` | `[playerData, ...]` | List of players on current map |
| `playerJoined` | `playerData` | New player joined the map |
| `playerMoved` | `{ odId, x, y, facing, animationState, velocityX, velocityY }` | Player position update |
| `playerLeft` | `{ odId }` | Player left the map |
| `playerChat` | `{ odId, name, message }` | Chat message from player |
| `error` | `{ message }` | Error message |

## Health Check

GET `/` returns server status:
```json
{
    "status": "ok",
    "totalPlayers": 5,
    "maps": [
        { "id": "henesys", "players": 3 },
        { "id": "ellinia", "players": 2 }
    ]
}
```

## Future Phases

### Phase 2: Server-Authoritative Monsters
- Monsters spawned and controlled by server
- Damage calculation on server
- Loot distribution

### Phase 3: Server-Authoritative Combat
- Player attacks validated by server
- Anti-cheat measures
- PvP support

## Production Deployment

1. Set `PORT` environment variable
2. Update CORS origin in `server.js` for security
3. Use a process manager like PM2
4. Consider using Redis for scaling across multiple server instances

```bash
# Example with PM2
npm install -g pm2
pm2 start server.js --name bennsauce-game
```
