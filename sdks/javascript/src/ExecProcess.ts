import { EventEmitter } from 'events';
import { Readable, Writable } from 'stream';

/**
 * ExecProcess - child_process.spawn compatible class
 * 
 * CRITICAL: This class MUST be identical to child_process.spawn interface
 * for seamless integration with existing Node.js ecosystem
 */
export class ExecProcess extends EventEmitter {
  public readonly stdout: Readable;
  public readonly stderr: Readable;
  public readonly stdin: Writable;
  public readonly pid: number | null = null;
  public exitCode: number | null = null;
  public signalCode: string | null = null;
  
  private _killed = false;
  private _connected = true;

  constructor(public readonly processId: string) {
    super();
    
    // Create streams that behave like child_process.spawn streams
    this.stdout = new Readable({
      read() {
        // Readable._read is required but data comes from WebSocket
      }
    });
    
    this.stderr = new Readable({
      read() {
        // Readable._read is required but data comes from WebSocket
      }
    });
    
    const self = this;
    this.stdin = new Writable({
      write(chunk, encoding, callback) {
        // Will be handled by WebSocketManager
        self.emit('stdin-write', chunk);
        callback();
      }
    });

    // Setup stdin end handling
    this.stdin.on('finish', () => {
      this.emit('stdin-end');
    });
  }

  /**
   * Simulate process spawn - called when WebSocket connection established
   */
  public _spawn(): void {
    process.nextTick(() => {
      this.emit('spawn');
    });
  }

  /**
   * Push data to stdout stream
   */
  public _pushStdout(data: Buffer): void {
    this.stdout.push(data);
  }

  /**
   * Push data to stderr stream  
   */
  public _pushStderr(data: Buffer): void {
    this.stderr.push(data);
  }

  /**
   * Handle process exit
   */
  public _exit(code: number, signal?: string): void {
    this.exitCode = code;
    this.signalCode = signal || null;
    this._connected = false;

    // End streams
    this.stdout.push(null); // EOF
    this.stderr.push(null); // EOF

    // Emit exit event (same as child_process.spawn)
    process.nextTick(() => {
      this.emit('exit', code, signal);
      
      // Close event comes after exit (child_process.spawn behavior)
      process.nextTick(() => {
        this.emit('close', code, signal);
      });
    });
  }

  /**
   * Handle connection error
   */
  public _error(error: Error): void {
    this._connected = false;
    process.nextTick(() => {
      this.emit('error', error);
    });
  }

  /**
   * Kill the process (child_process.spawn compatible)
   */
  public kill(signal: string = 'SIGTERM'): boolean {
    if (!this._connected || this._killed) {
      return false;
    }

    this._killed = true;
    this.emit('kill-request', signal);
    return true;
  }

  /**
   * Resize the terminal (for TTY mode)
   */
  public resize(cols: number, rows: number): void {
    if (this._connected) {
      this.emit('resize-request', { cols, rows });
    }
  }

  /**
   * Check if process is connected
   */
  public get connected(): boolean {
    return this._connected;
  }

  /**
   * Check if process was killed
   */
  public get killed(): boolean {
    return this._killed;
  }
}