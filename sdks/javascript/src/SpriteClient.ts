import { Sprite } from './Sprite.js';
import { SpritesConfig, AuthenticationError } from './types.js';

/**
 * SpriteClient - Main entry point for Sprites SDK
 * 
 * Usage:
 *   const sprites = new SpriteClient("token");
 *   const sprites = new SpriteClient({ token: "...", baseUrl: "..." });
 */
export class SpriteClient {
  private token: string;
  private baseUrl: string;
  private debug: boolean;

  constructor(config: string | SpritesConfig) {
    const resolved = this.resolveConfig(config);
    this.token = resolved.token;
    this.baseUrl = resolved.baseUrl;
    this.debug = (config as SpritesConfig).debug || process.env.SPRITE_DEBUG === 'true';

    if (!this.token) {
      throw new AuthenticationError(
        'API token must be provided'
      );
    }

    if (this.debug) {
      console.log('[SpriteClient] Initialized with:', {
        baseUrl: this.baseUrl,
        tokenLength: this.token.length,
        debug: this.debug
      });
    }
  }

  /**
   * Resolve configuration from string token or config object
   */
  private resolveConfig(input: string | SpritesConfig): { token: string; baseUrl: string } {
    if (typeof input === 'string') {
      return {
        token: input,
        baseUrl: 'https://api.sprites.dev'
      };
    }

    const baseUrl = (input.baseUrl || 'https://api.sprites.dev').replace(/\/+$/, '');
    return {
      token: input.token,
      baseUrl: baseUrl
    };
  }

  /**
   * Create or get a sprite
   */
  public async create(name: string): Promise<Sprite> {
    const url = `${this.baseUrl}/v1/sprites`;
    
    const response = await fetch(url, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${this.token}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify({ name })
    });

    if (!response.ok) {
      const error = await response.text().catch(() => 'Unknown error');
      throw new Error(`Failed to create sprite: HTTP ${response.status}: ${error}`);
    }

    return new Sprite(this, name);
  }

  /**
   * List all sprites
   */
  public async list(prefix?: string): Promise<Array<{ name: string; created_at: string; status: string }>> {
    const url = new URL(`${this.baseUrl}/v1/sprites`);
    url.searchParams.set('max_results', '100');
    if (prefix) {
      url.searchParams.set('prefix', prefix);
    }
    
    const response = await fetch(url.toString(), {
      method: 'GET',
      headers: {
        'Authorization': `Bearer ${this.token}`,
        'Content-Type': 'application/json'
      }
    });

    if (!response.ok) {
      const error = await response.text().catch(() => 'Unknown error');
      throw new Error(`Failed to list sprites: HTTP ${response.status}: ${error}`);
    }

    const data = await response.json();
    return data.sprites || [];
  }

  /**
   * Destroy a sprite
   */
  public async destroy(name: string): Promise<void> {
    const url = `${this.baseUrl}/v1/sprites/${encodeURIComponent(name)}`;
    
    const response = await fetch(url, {
      method: 'DELETE',
      headers: {
        'Authorization': `Bearer ${this.token}`,
        'Content-Type': 'application/json'
      }
    });

    if (!response.ok) {
      const error = await response.text().catch(() => 'Unknown error');
      throw new Error(`Failed to destroy sprite: HTTP ${response.status}: ${error}`);
    }
  }

  /**
   * Make HTTP request to sprite API
   */
  public async makeRequest(path: string, options: RequestInit = {}): Promise<Response> {
    const url = `${this.baseUrl}/v1/sprites${path}`;
    
    const headers = new Headers(options.headers);
    headers.set('Authorization', `Bearer ${this.token}`);
    headers.set('Content-Type', 'application/json');

    if (this.debug) {
      const headerObj: Record<string, string> = {};
      headers.forEach((value, key) => {
        headerObj[key] = key === 'Authorization' ? `Bearer [REDACTED]` : value;
      });
      console.log('[SpriteClient.makeRequest] Request:', {
        url,
        method: options.method || 'GET',
        headers: headerObj,
        body: options.body
      });
    }

    const response = await fetch(url, {
      ...options,
      headers
    });

    if (this.debug) {
      const responseHeaders: Record<string, string> = {};
      response.headers.forEach((value, key) => {
        responseHeaders[key] = value;
      });
      console.log('[SpriteClient.makeRequest] Response:', {
        status: response.status,
        statusText: response.statusText,
        headers: responseHeaders
      });
    }

    if (!response.ok) {
      const error = await response.text().catch(() => 'Unknown error');
      if (this.debug) {
        console.error('[SpriteClient.makeRequest] Error response body:', error);
      }
      throw new Error(`HTTP ${response.status}: ${error}`);
    }

    return response;
  }

  /**
   * Get WebSocket URL for sprite
   */
  public getWebSocketUrl(spriteName: string, path: string): string {
    const wsBaseUrl = this.baseUrl.replace(/^https?/, 'ws');
    const url = `${wsBaseUrl}/v1/sprites/${encodeURIComponent(spriteName)}${path}`;
    const separator = path.includes('?') ? '&' : '?';
    return `${url}${separator}token=${encodeURIComponent(this.token)}`;
  }

  /**
   * Get token for internal use
   */
  public getToken(): string {
    return this.token;
  }

  /**
   * Get base URL for internal use
   */
  public getBaseUrl(): string {
    return this.baseUrl;
  }

  /**
   * Get debug flag
   */
  public isDebug(): boolean {
    return this.debug;
  }

  /**
   * Create sprite instance
   */
  public sprite(name: string): Sprite {
    return new Sprite(this, name);
  }
}