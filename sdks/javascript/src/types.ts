// Core types for Sprites JavaScript SDK

export interface SpritesConfig {
  token: string;
  baseUrl?: string;
  debug?: boolean;
}

export interface ExecOptions {
  cwd?: string;
  env?: Record<string, string>;
  tty?: boolean;
}

export interface Checkpoint {
  id: string;
  createTime: Date;
  sourceId?: string;
  history?: string[];
}

export interface CheckpointRequest {
  name?: string;
  description?: string;
}

export interface RestoreRequest {
  checkpointId: string;
  force?: boolean;
}

// WebSocket protocol types
export const StreamConstants = {
  STDIN: 0x00,
  STDOUT: 0x01,
  STDERR: 0x02,
  EXIT: 0x03,
  STDIN_EOF: 0x04,
} as const;

export type StreamType = typeof StreamConstants[keyof typeof StreamConstants];

export interface WebSocketMessage {
  processId: string;
  stream: StreamType;
  data?: Buffer;
  exitCode?: number;
  signal?: string;
}

// API types
export interface ExecCreateRequest {
  Cmd: string[];
  AttachStdout: boolean;
  AttachStderr: boolean;
  Tty: boolean;
  Env?: string[];
  WorkingDir?: string;
}

export interface ExecCreateResponse {
  Id: string;
}

// Error classes
export class SpritesError extends Error {
  constructor(
    message: string,
    public code?: string,
    public statusCode?: number
  ) {
    super(message);
    this.name = 'SpritesError';
  }
}

export class AuthenticationError extends SpritesError {
  constructor(message: string) {
    super(message, 'AUTH_ERROR', 401);
    this.name = 'AuthenticationError';
  }
}

export class ConnectionError extends SpritesError {
  constructor(message: string) {
    super(message, 'CONNECTION_ERROR');
    this.name = 'ConnectionError';
  }
}

export class ExecError extends SpritesError {
  constructor(message: string, public exitCode?: number) {
    super(message, 'EXEC_ERROR');
    this.name = 'ExecError';
  }
}