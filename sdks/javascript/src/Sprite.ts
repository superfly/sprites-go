import { randomUUID } from 'crypto';
import { SpriteClient } from './SpriteClient.js';
import { ExecProcess } from './ExecProcess.js';
import { WebSocketManager } from './WebSocketManager.js';
import { 
  ExecOptions, 
  Checkpoint, 
  CheckpointRequest, 
  RestoreRequest,
  ExecCreateRequest,
  ExecCreateResponse
} from './types.js';

/**
 * Sprite - Individual sprite operations
 * 
 * Provides spawn() that returns child_process.spawn compatible object
 * and exec() that matches child_process.exec with callback
 * and checkpoint operations
 */
export class Sprite {
  private client: SpriteClient;
  private wsManager: WebSocketManager | null = null;
  public readonly name: string;

  constructor(client: SpriteClient, name: string) {
    this.client = client;
    this.name = name;
  }

  /**
   * Get sprite ID/name
   */
  public getId(): string {
    return this.name;
  }

  /**
   * Spawn command - returns child_process.spawn compatible object
   * 
   * CRITICAL: This MUST return object identical to child_process.spawn
   */
  public spawn(command: string, args: string[] = [], options: ExecOptions = {}): ExecProcess {
    // Generate unique process ID for WebSocket multiplexing
    const processId = randomUUID().replace(/-/g, '');

    if (this.client.isDebug()) {
      console.log('[Sprite.spawn] Starting process:', {
        processId,
        command,
        args,
        options
      });
    }

    // Create the process that will be returned
    const execProcess = new ExecProcess(processId);

    // Start async execution (don't await - return process immediately like spawn)
    this.startSpawnAsync(processId, execProcess, command, args, options);

    // Return process immediately (spawn behavior)
    return execProcess;
  }

  /**
   * Execute command with callback - matches child_process.exec
   */
  public exec(command: string, callback?: (error: Error | null, stdout: string, stderr: string) => void): ExecProcess;
  public exec(command: string, options: ExecOptions, callback?: (error: Error | null, stdout: string, stderr: string) => void): ExecProcess;
  public exec(command: string, optionsOrCallback?: ExecOptions | ((error: Error | null, stdout: string, stderr: string) => void), callback?: (error: Error | null, stdout: string, stderr: string) => void): ExecProcess {
    let options: ExecOptions = {};
    let cb: ((error: Error | null, stdout: string, stderr: string) => void) | undefined;
    
    if (typeof optionsOrCallback === 'function') {
      cb = optionsOrCallback;
    } else if (optionsOrCallback) {
      options = optionsOrCallback;
      cb = callback;
    } else {
      cb = callback;
    }
    
    // Parse command string into command and args
    const parts = command.trim().split(/\s+/);
    const cmd = parts[0];
    const args = parts.slice(1);
    
    const child = this.spawn(cmd, args, options);
    
    if (cb) {
      let stdout = '';
      let stderr = '';
      
      child.stdout?.on('data', (data) => {
        stdout += data.toString();
      });
      
      child.stderr?.on('data', (data) => {
        stderr += data.toString();
      });
      
      child.on('close', (code) => {
        const error = code !== 0 ? new Error(`Command failed with exit code ${code}`) : null;
        cb(error, stdout, stderr);
      });
      
      child.on('error', (error) => {
        cb(error, stdout, stderr);
      });
    }
    
    return child;
  }

  /**
   * Start spawn process asynchronously
   */
  private async startSpawnAsync(
    processId: string, 
    execProcess: ExecProcess,
    command: string, 
    args: string[], 
    options: ExecOptions
  ): Promise<void> {
    try {
      // Connect directly to WebSocket exec endpoint
      const baseUrl = this.client.getBaseUrl();
      // Use wss:// for https:// URLs, ws:// for http://
      const wsBaseUrl = baseUrl.replace(/^https:/, 'wss:').replace(/^http:/, 'ws:');
      
      // Build WebSocket URL with command parameters
      const url = new URL(`${wsBaseUrl}/v1/sprites/${encodeURIComponent(this.name)}/exec`);
      url.searchParams.set('cmd', command);
      args.forEach(arg => url.searchParams.append('cmd', arg));
      if (options.tty) {
        url.searchParams.set('tty', 'true');
      }
      
      // Add environment variables if provided
      if (options.env) {
        Object.entries(options.env).forEach(([key, value]) => {
          url.searchParams.append('env', `${key}=${value}`);
        });
      }

      // Create WebSocket manager if needed
      if (!this.wsManager) {
        this.wsManager = new WebSocketManager(url.toString(), this.client.getToken(), this.client.isDebug());
      }

      // Connect the existing process to WebSocket
      await this.wsManager.connectExecProcess(processId, execProcess, options);

    } catch (error) {
      // If there's an error, notify the process
      // This maintains spawn-like error behavior
      console.error(`Spawn start error for ${processId}:`, error);
      execProcess._exit(1);
    }
  }



  /**
   * Create checkpoint
   */
  public async checkpoint(name?: string): Promise<Checkpoint> {
    const request: CheckpointRequest = { name };

    const response = await this.client.makeRequest(`/${this.name}/checkpoints`, {
      method: 'POST',
      body: JSON.stringify(request)
    });

    const result = await response.json();
    
    return {
      id: result.checkpointId || result.id,
      createTime: new Date(),
      sourceId: result.sourceId,
      history: result.history || []
    };
  }

  /**
   * Restore from checkpoint
   */
  public async restore(checkpointId: string): Promise<void> {
    const request: RestoreRequest = { checkpointId };

    await this.client.makeRequest(`/${this.name}/restore/${checkpointId}`, {
      method: 'POST',
      body: JSON.stringify(request)
    });
  }

  /**
   * List checkpoints
   */
  public async listCheckpoints(): Promise<Checkpoint[]> {
    const response = await this.client.makeRequest(`/${this.name}/checkpoints`);
    const results = await response.json();

    return results.map((item: any) => ({
      id: item.id,
      createTime: new Date(item.create_time || item.createTime),
      sourceId: item.source_id || item.sourceId,
      history: item.history || []
    }));
  }

  /**
   * Delete checkpoint
   */
  public async deleteCheckpoint(id: string): Promise<void> {
    await this.client.makeRequest(`/${this.name}/checkpoints/${id}`, {
      method: 'DELETE'
    });
  }

  /**
   * Close WebSocket connection
   */
  public close(): void {
    if (this.wsManager) {
      this.wsManager.close();
      this.wsManager = null;
    }
  }
}