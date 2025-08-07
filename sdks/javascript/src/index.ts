// Sprites JavaScript SDK - Main exports

export { SpriteClient } from './SpriteClient.js';
export { Sprite } from './Sprite.js';
export { ExecProcess } from './ExecProcess.js';

// Export types
export type {
  SpritesConfig,
  ExecOptions,
  Checkpoint,
  CheckpointRequest,
  RestoreRequest,
  WebSocketMessage
} from './types.js';

// Export error classes
export {
  SpritesError,
  AuthenticationError,
  ConnectionError,
  ExecError,
  StreamConstants
} from './types.js';

// Default export
export { SpriteClient as default } from './SpriteClient.js';