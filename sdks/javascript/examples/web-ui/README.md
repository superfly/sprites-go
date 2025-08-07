# Sprite Web UI

A simple web-based terminal interface for managing and connecting to Sprites using xterm.js.

## Features

- Create and delete sprites
- Connect to sprites with a full terminal interface
- Real-time terminal interaction using WebSockets
- Clean, modern UI with xterm.js

## Setup

1. Install dependencies:
```bash
npm install
```

2. Build the SDK (from the SDK root directory):
```bash
cd ../..
npm run build
```

3. Start the server:
```bash
npm start
```

4. Open your browser to http://localhost:3000

## Usage

1. Enter your Sprite API token
2. Optionally specify a custom base URL (defaults to https://api.sprites.dev)
3. Click "Connect" to authenticate
4. Create a new sprite or select an existing one
5. Use the terminal interface to interact with your sprite

## Architecture

- **server.js**: Node.js Express server that:
  - Uses the Sprites SDK to manage sprites
  - Proxies WebSocket connections between browser and sprites
  - Provides REST API for sprite management

- **public/index.html**: Main UI with sidebar for sprite management
- **public/app.js**: Frontend JavaScript handling UI interactions and xterm.js

## Notes

This is a simple example implementation:
- Sprite list is stored in memory (resets on server restart)
- No authentication beyond the Sprite API token
- Basic error handling
- Single terminal session per sprite

For production use, consider adding:
- Persistent storage for sprite list
- User authentication
- Multiple terminal sessions
- Better error handling and recovery