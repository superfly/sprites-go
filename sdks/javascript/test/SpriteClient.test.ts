import { SpriteClient, AuthenticationError } from '../src/index';

describe('SpriteClient', () => {
  const originalEnv = process.env;

  beforeEach(() => {
    jest.resetModules();
    process.env = { ...originalEnv };
  });

  afterAll(() => {
    process.env = originalEnv;
  });

  it('should create client with token from config', () => {
    const client = new SpriteClient({ token: 'test-token' });
    expect(client.getToken()).toBe('test-token');
  });

  it('should create client with token from environment', () => {
    process.env.SPRITE_TOKEN = 'env-token';
    const client = new SpriteClient({ token: process.env.SPRITE_TOKEN });
    expect(client.getToken()).toBe('env-token');
  });

  it('should throw error when no token provided', () => {
    delete process.env.SPRITE_TOKEN;
    delete process.env.SPRITES_TOKEN;
    
    expect(() => new SpriteClient({ token: '' })).toThrow(AuthenticationError);
  });

  it('should use default base URL', () => {
    const client = new SpriteClient({ token: 'test-token' });
    expect(client.getBaseUrl()).toBe('https://api.sprites.dev');
  });

  it('should use custom base URL', () => {
    const client = new SpriteClient({ 
      token: 'test-token',
      baseUrl: 'https://custom.sprites.dev' 
    });
    expect(client.getBaseUrl()).toBe('https://custom.sprites.dev');
  });

  it('should strip trailing slashes from base URL', () => {
    const client = new SpriteClient({ 
      token: 'test-token',
      baseUrl: 'https://custom.sprites.dev/' 
    });
    expect(client.getBaseUrl()).toBe('https://custom.sprites.dev');
  });

  it('should create sprite instance', () => {
    const client = new SpriteClient({ token: 'test-token' });
    const sprite = client.sprite('test-sprite');
    expect(sprite.getId()).toBe('test-sprite');
  });

  it('should generate WebSocket URLs correctly', () => {
    const client = new SpriteClient({ 
      token: 'test-token',
      baseUrl: 'https://api.sprites.dev'
    });
    
    const wsUrl = client.getWebSocketUrl('test-sprite', '/exec/123/attach');
    expect(wsUrl).toBe('ws://api.sprites.dev/v1/sprites/test-sprite/exec/123/attach?token=test-token');
  });
});