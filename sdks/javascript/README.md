# Sprites JavaScript/TypeScript SDK

A modern TypeScript/JavaScript SDK for interacting with Sprites environments.

## Features

- 🚀 **Modern TypeScript** - Full type safety and IntelliSense support
- 🔌 **WebSocket Streaming** - Real-time command execution with streaming I/O
- 📦 **ESM Support** - ES modules for modern Node.js applications
- 🛡️ **Error Handling** - Comprehensive error types and handling
- 🔧 **CLI Wrapper** - Command-line interface for integration testing
- ✅ **Well Tested** - Unit and integration tests

## Installation

```bash
npm install @sprites/sdk
```

## Quick Start

```typescript
import { SpritesClient } from '@sprites/sdk';

// Create a client
const client = new SpriteClient({
  baseUrl: 'https://api.sprites.dev',
  token: 'your-api-token'
});

// Create/get a sprite
const sprite = client.sprite('my-sprite-id');

// Spawn commands (matches child_process.spawn)
const child = sprite.spawn('echo', ['Hello World!']);
child.stdout.on('data', (data) => console.log(data.toString()));
child.on('close', (code) => console.log('Exit code:', code));
```

## API Reference

### SpritesClient

```typescript
const client = new SpriteClient({
  baseUrl?: string;     // API base URL (default: https://api.sprites.dev)
  token: string;        // Auth token
});
```

### Command Execution

```javascript
// Spawn method (matches child_process.spawn)
const child = sprite.spawn('ls', ['-la']);
child.stdout.on('data', (data) => console.log(data.toString()));
child.on('close', (code) => console.log('Exit code:', code));

// Exec method with callback (matches child_process.exec)  
sprite.exec('npm test', { cwd: '/app', env: { NODE_ENV: 'test' } }, (error, stdout, stderr) => {
  if (error) {
    console.error('Error:', error);
    return;
  }
  console.log('Output:', stdout);
});

// Spawn command with real-time output (matches child_process.spawn)
const child = sprite.spawn('tail', ['-f', '/var/log/app.log']);

child.stdout.on('data', (data) => console.log('OUT:', data.toString()));
child.stderr.on('data', (data) => console.error('ERR:', data.toString()));
child.on('close', (code) => console.log('Process exited:', code));
```

### Checkpoint Operations

```typescript
// Create checkpoint
const checkpoint = await sprite.checkpoint({ 
  name: 'before-deployment' 
});

// List checkpoints
const checkpoints = await sprite.listCheckpoints();

// Restore from checkpoint
const success = await sprite.restore({ 
  checkpointId: checkpoint.id 
});
```

### Admin Operations

```typescript
// Reset sprite state
const result = await sprite.resetState();
```

## Environment Variables

- `SPRITE_URL` - Sprite server URL
- `SPRITE_TOKEN` - Authentication token
- `SPRITE_ADMIN_TOKEN` - Admin authentication token

## CLI Usage

The SDK includes a CLI wrapper for compatibility with test harnesses:

```bash
# Execute commands
./sprite-cli exec echo "Hello World"
./sprite-cli exec -dir /tmp -env VAR=value command

# Checkpoint operations
./sprite-cli checkpoint create my-checkpoint
./sprite-cli checkpoint list
./sprite-cli checkpoint restore checkpoint-id

# Admin operations
./sprite-cli admin reset-state
```

## Examples

See the `examples/` directory for complete usage examples:

- `basic_usage.js` - Basic command execution
- `checkpoint_example.js` - Checkpoint operations
- `streaming_example.js` - Real-time streaming

## Development

```bash
# Install dependencies
npm install

# Build TypeScript
npm run build

# Run tests
npm test

# Run integration tests
npm run test:integration

# Watch mode for development
npm run dev
```

## Error Handling

The SDK provides specific error types:

```typescript
import { SpritesError, AuthenticationError, ConnectionError, ExecError } from '@sprites/sdk';

try {
  await sprite.exec(['invalid-command']);
} catch (error) {
  if (error instanceof ExecError) {
    console.log(`Command failed with exit code: ${error.exitCode}`);
  } else if (error instanceof AuthenticationError) {
    console.log('Authentication failed');
  } else if (error instanceof ConnectionError) {
    console.log('Connection error');
  }
}
```

## Requirements

- Node.js 18 or higher
- Modern browsers (ES2022 support)

## License

MIT License - see LICENSE file for details.