#!/usr/bin/env node

// Example: Executing commands in a new sprite using the planned API
// This shows the ideal usage based on our js-sdk-plan.md

// NOTE: This is a mockup of the planned API - the actual implementation
// needs to be built following the simplified flat file structure

import { SpriteClient } from '../src/index.js'; // Will work once implemented

async function spawnExample() {
  console.log('=== Sprite Spawn Example ===');
  
  // Initialize client with token (simple form)
  const sprites = new SpriteClient(process.env.SPRITE_TOKEN);
  
  // Or with full config
  // const sprites = new SpriteClient({
  //   token: process.env.SPRITE_TOKEN,
  //   baseUrl: 'https://api.sprites.dev'
  // });

  try {
    console.log('1. Creating new sprite...');
    const sprite = await sprites.create('my-dev-environment');
    console.log(`   ✓ Created sprite: ${sprite.name}`);

    console.log('\n2. Executing command with spawn-like interface...');
    
    // exec() returns object identical to child_process.spawn()
    const child = sprite.exec('echo', ['Hello from Sprite!'], {
      cwd: '/tmp',
      env: { NODE_ENV: 'development' },
      tty: false
    });

    // Standard child_process.spawn events and streams
    child.stdout.on('data', (data) => {
      console.log(`   stdout: ${data.toString().trim()}`);
    });

    child.stderr.on('data', (data) => {
      console.log(`   stderr: ${data.toString().trim()}`);
    });

    child.on('spawn', () => {
      console.log('   ✓ Process spawned');
    });

    child.on('exit', (code, signal) => {
      console.log(`   ✓ Process exited with code: ${code}, signal: ${signal}`);
    });

    // Wait for process to complete
    await new Promise((resolve, reject) => {
      child.on('exit', resolve);
      child.on('error', reject);
    });

    console.log('\n3. Multiple rapid-fire commands (testing race conditions)...');
    
    const processes = [];
    for (let i = 0; i < 5; i++) {
      const proc = sprite.exec('echo', [`Process ${i}`]);
      processes.push(new Promise((resolve) => {
        let output = '';
        proc.stdout.on('data', (data) => output += data.toString());
        proc.on('exit', (code) => resolve({ id: i, output: output.trim(), code }));
      }));
    }

    const results = await Promise.all(processes);
    results.forEach(result => {
      console.log(`   Process ${result.id}: "${result.output}" (exit: ${result.code})`);
    });

    console.log('\n4. Interactive command with TTY...');
    
    const interactive = sprite.exec('python3', ['-c', 'print("Interactive Python ready")'], {
      tty: true  // Passed to server, no special client handling
    });

    interactive.stdout.on('data', (data) => {
      console.log(`   tty output: ${data.toString().trim()}`);
    });

    await new Promise((resolve) => {
      interactive.on('exit', resolve);
    });

    console.log('\n5. Pipe output to another process (standard Node.js)...');
    
    import { spawn } from 'child_process';
    
    const spriteCmd = sprite.exec('find', ['/usr', '-name', '*.so'], { 
      cwd: '/' 
    });
    
    const grep = spawn('head', ['-n', '5']);
    
    // Standard Node.js piping - works because sprite.exec returns 
    // object identical to child_process.spawn
    spriteCmd.stdout.pipe(grep.stdin);
    
    grep.stdout.on('data', (data) => {
      console.log(`   piped result: ${data.toString().trim()}`);
    });

    await new Promise((resolve) => {
      grep.on('exit', resolve);
    });

    console.log('\n6. Working with checkpoints...');
    
    // Create checkpoint before risky operation
    const checkpoint = await sprite.checkpoint('before-build');
    console.log(`   ✓ Created checkpoint: ${checkpoint.id}`);

    // Run potentially destructive command
    const build = sprite.exec('npm', ['run', 'build'], {
      cwd: '/app'
    });

    build.on('exit', async (code) => {
      if (code !== 0) {
        console.log('   ❌ Build failed, restoring checkpoint...');
        await sprite.restore(checkpoint.id);
        console.log('   ✓ Restored to checkpoint');
      } else {
        console.log('   ✓ Build succeeded');
      }
    });

    await new Promise((resolve) => {
      build.on('exit', resolve);
    });

    console.log('\n7. Cleanup...');
    await sprites.destroy('my-dev-environment');
    console.log('   ✓ Sprite destroyed');

  } catch (error) {
    console.error(`❌ Error: ${error.message}`);
    process.exit(1);
  }
}

// Show what the implementation should look like
console.log(`
=== Expected API Implementation Structure ===

src/
├── SpriteClient.ts     # Main client with token/config handling
├── Sprite.ts          # Individual sprite operations
├── ExecProcess.ts     # child_process.spawn compatible class
├── WebSocketManager.ts # WebSocket multiplexing + strict protocol
├── types.ts          # All TypeScript interfaces
└── index.ts          # Main exports

Key Requirements:
✅ sprite.exec() returns object identical to child_process.spawn()
✅ Multiple rapid-fire exec() calls work without race conditions
✅ Strict WebSocket protocol handling (no sleep() calls ever)
✅ Node.js 22 with native fetch and modern streams
✅ /v1/sprites/:name/... API pattern
`);

// Run the example (will fail until implementation is complete)
if (process.env.SPRITE_TOKEN) {
  spawnExample().catch(console.error);
} else {
  console.log('\n⚠️  Set SPRITE_TOKEN environment variable to run example');
  console.log('This example shows the planned API - implementation needed');
}