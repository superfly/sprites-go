import WebSocket from 'ws';
import { ExecProcess } from './ExecProcess.js';
import { StreamConstants, StreamType, ConnectionError } from './types.js';

/**
 * WebSocketManager - Handles WebSocket multiplexing with STRICT protocol
 * 
 * CRITICAL RULES:
 * - NO sleep() calls ever
 * - STRICT state machine - no timing assumptions
 * - Each exec gets unique ID for multiplexing
 * - Explicit state tracking for each process
 */
export class WebSocketManager {
  private ws: WebSocket | null = null;
  private processes = new Map<string, ExecProcess>();
  private connectionPromise: Promise<void> | null = null;
  private url: string;
  private token: string;
  private debug: boolean;
  private bytesReceived: number = 0;
  private bytesSent: number = 0;
  private statsInterval: NodeJS.Timeout | null = null;

  constructor(url: string, token: string, debug: boolean = false) {
    this.url = url;
    this.token = token;
    this.debug = debug;
    
    // Start stats logging if debug is enabled
    if (this.debug) {
      this.startStatsLogging();
    }
  }
  
  private startStatsLogging(): void {
    this.statsInterval = setInterval(() => {
      console.log(`[WebSocketManager Stats] Bytes sent: ${this.bytesSent}, Bytes received: ${this.bytesReceived}`);
    }, 5000); // Log every 5 seconds
  }
  
  private stopStatsLogging(): void {
    if (this.statsInterval) {
      clearInterval(this.statsInterval);
      this.statsInterval = null;
    }
  }

  /**
   * Connect to WebSocket - returns promise that resolves when connected
   */
  public async connect(): Promise<void> {
    if (this.connectionPromise) {
      return this.connectionPromise;
    }

    this.connectionPromise = new Promise((resolve, reject) => {
      if (this.debug) {
        console.log('[WebSocketManager] Connecting to:', this.url);
      }

      const ws = new WebSocket(this.url, {
        headers: {
          'Authorization': `Bearer ${this.token}`,
          'Connection': 'Upgrade',
          'Upgrade': 'websocket'
        }
      });

      const timeout = setTimeout(() => {
        ws.terminate();
        reject(new ConnectionError('WebSocket connection timeout'));
      }, 10000);

      ws.on('open', () => {
        clearTimeout(timeout);
        this.ws = ws;
        if (this.debug) {
          console.log('[WebSocketManager] Connected successfully');
        }
        this.setupWebSocketHandlers();
        resolve();
      });

      ws.on('error', (error) => {
        clearTimeout(timeout);
        if (this.debug) {
          console.error('[WebSocketManager] Connection error:', error);
        }
        reject(new ConnectionError(`WebSocket error: ${error.message}`));
      });
    });

    return this.connectionPromise;
  }

  /**
   * Setup WebSocket message handlers - STRICT protocol handling
   */
  private setupWebSocketHandlers(): void {
    if (!this.ws) return;

    this.ws.on('message', (data: Buffer) => {
      try {
        this.handleMessage(data);
      } catch (error) {
        console.error('WebSocket message handling error:', error);
      }
    });

    this.ws.on('close', () => {
      this.handleConnectionClose();
    });

    this.ws.on('error', (error) => {
      this.handleConnectionError(error);
    });
  }

  /**
   * Handle incoming WebSocket message - Direct exec endpoint
   */
  private handleMessage(data: Buffer): void {
    // The exec endpoint sends raw terminal data directly
    // Forward it to all connected processes (should be just one for exec)
    
    // Track bytes for stats
    this.bytesReceived += data.length;

    // Forward to the single process (exec is 1:1 connection)
    for (const [processId, process] of this.processes) {
      // Send raw data as stdout
      process._pushStdout(data);
    }
  }

  /**
   * Start a new exec process
   */
  public async startExec(processId: string, options: any = {}): Promise<ExecProcess> {
    await this.connect();

    const process = new ExecProcess(processId);
    this.processes.set(processId, process);

    // Handle stdin writes from the process
    process.on('stdin-write', (data: Buffer) => {
      this.sendStdin(processId, data);
    });

    process.on('stdin-end', () => {
      if (this.debug) {
        console.log('[WebSocketManager] stdin end');
      }
    });

    process.on('kill-request', (signal: string) => {
      // Close the WebSocket connection to kill the process
      if (this.debug) {
        console.log(`[WebSocketManager] Kill request for ${processId} with signal ${signal}`);
      }
      if (this.ws) {
        this.ws.close();
      }
    });

    process.on('resize-request', (dimensions: { cols: number; rows: number }) => {
      this.sendResize(processId, dimensions.cols, dimensions.rows);
    });

    // Emit spawn event after connection is established
    process._spawn();

    return process;
  }

  /**
   * Connect an existing exec process to the WebSocket
   */
  public async connectExecProcess(processId: string, process: ExecProcess, options: any = {}): Promise<void> {
    await this.connect();

    this.processes.set(processId, process);

    // Handle stdin writes from the process
    process.on('stdin-write', (data: Buffer) => {
      this.sendStdin(processId, data);
    });

    process.on('stdin-end', () => {
      if (this.debug) {
        console.log('[WebSocketManager] stdin end');
      }
    });

    process.on('kill-request', (signal: string) => {
      // Close the WebSocket connection to kill the process
      if (this.debug) {
        console.log(`[WebSocketManager] Kill request for ${processId} with signal ${signal}`);
      }
      if (this.ws) {
        this.ws.close();
      }
    });

    process.on('resize-request', (dimensions: { cols: number; rows: number }) => {
      this.sendResize(processId, dimensions.cols, dimensions.rows);
    });

    // Emit spawn event after connection is established
    process._spawn();
  }

  /**
   * Send stdin data to process
   */
  private sendStdin(processId: string, data: Buffer): void {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
      console.error('[WebSocketManager] Cannot send stdin: WebSocket not connected');
      return;
    }

    // Track bytes for stats
    this.bytesSent += data.length;

    // Send raw data directly to the exec WebSocket
    this.ws.send(data);
  }

  /**
   * Send resize command to process
   */
  private sendResize(processId: string, cols: number, rows: number): void {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
      console.error('[WebSocketManager] Cannot send resize: WebSocket not connected');
      return;
    }

    // Send resize as a JSON text frame
    const resizeMsg = JSON.stringify({
      type: 'resize',
      cols: cols,
      rows: rows
    });

    this.ws.send(resizeMsg);
  }

  /**
   * Handle connection close
   */
  private handleConnectionClose(): void {
    this.ws = null;
    this.connectionPromise = null;
    
    // Stop stats logging
    this.stopStatsLogging();

    if (this.debug) {
      console.log('[WebSocketManager] Connection closed');
      console.log(`[WebSocketManager Final Stats] Total sent: ${this.bytesSent} bytes, Total received: ${this.bytesReceived} bytes`);
    }

    // Notify all processes that they've exited
    for (const [processId, process] of this.processes) {
      process._exit(0); // Normal exit when connection closes
    }
    this.processes.clear();
  }

  /**
   * Handle connection error
   */
  private handleConnectionError(error: Error): void {
    for (const process of this.processes.values()) {
      process._error(error);
    }
  }

  /**
   * Close WebSocket connection
   */
  public close(): void {
    if (this.ws) {
      this.ws.close();
      this.ws = null;
    }
    this.connectionPromise = null;
  }
}