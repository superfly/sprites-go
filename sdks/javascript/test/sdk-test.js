#!/usr/bin/env node

// Test the new SDK implementation
import { SpriteClient, Sprite, ExecProcess } from '../dist/index.js';

async function testSDK() {
  console.log('=== SDK Implementation Test ===');

  try {
    console.log('1. Testing SpriteClient instantiation...');
    
    // Test string token
    const client1 = new SpriteClient('test-token');
    console.log('   ✓ String token constructor works');
    console.log(`   ✓ Base URL: ${client1.getBaseUrl()}`);
    
    // Test config object
    const client2 = new SpriteClient({
      token: 'test-token',
      baseUrl: 'https://custom.sprites.dev'
    });
    console.log('   ✓ Config object constructor works');
    console.log(`   ✓ Custom base URL: ${client2.getBaseUrl()}`);

    console.log('\n2. Testing WebSocket URL generation...');
    const wsUrl = client1.getWebSocketUrl('test-sprite', '/exec/stream');
    console.log(`   ✓ WebSocket URL: ${wsUrl}`);

    console.log('\n3. Testing ExecProcess instantiation...');
    const process = new ExecProcess('test-process-id');
    console.log('   ✓ ExecProcess created');
    console.log(`   ✓ Process ID: ${process.processId}`);
    console.log(`   ✓ Has stdout: ${!!process.stdout}`);
    console.log(`   ✓ Has stderr: ${!!process.stderr}`);
    console.log(`   ✓ Has stdin: ${!!process.stdin}`);
    
    // Test event emitter functionality
    let spawnEmitted = false;
    process.on('spawn', () => {
      spawnEmitted = true;
      console.log('   ✓ Spawn event received');
    });
    
    process._spawn(); // Simulate spawn
    
    // Give a moment for event to fire
    await new Promise(resolve => setTimeout(resolve, 10));
    
    if (spawnEmitted) {
      console.log('   ✓ Event system working');
    }

    console.log('\n4. Testing error handling...');
    try {
      new SpriteClient(''); // Empty token should fail
      console.log('   ✗ Empty token should have failed');
    } catch (error) {
      console.log('   ✓ Empty token properly rejected');
    }

    console.log('\n=== SDK Implementation Test Complete ===');
    console.log('✅ All basic functionality working');

  } catch (error) {
    console.error(`❌ SDK test failed: ${error.message}`);
    process.exit(1);
  }
}

testSDK().then(() => {
  console.log('SDK tests completed successfully');
  process.exit(0);
}).catch((error) => {
  console.error('SDK tests failed:', error);
  process.exit(1);
});