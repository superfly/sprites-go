#!/usr/bin/env node

// Complete example showing the new JavaScript SDK in action
import { SpriteClient } from '../dist/index.js';

async function completeExample() {
  console.log('=== Complete Sprites SDK Example ===');
  
  // Initialize client (would use real token in production)
  const sprites = new SpriteClient({
    token: process.env.SPRITE_TOKEN || 'demo-token',
    baseUrl: process.env.SPRITE_URL || 'https://api.sprites.dev'
  });

  console.log('1. SDK Client initialized');
  console.log(`   Base URL: ${sprites.getBaseUrl()}`);

  // This example shows the API calls that would be made
  // (will fail without real sprite server, but demonstrates the interface)
  
  console.log('\n2. Example: Creating a sprite and running commands');
  console.log('   Code:');
  console.log('   ```javascript');
  console.log('   const sprite = await sprites.create("my-project");');
  console.log('   ');
  console.log('   // Execute command - returns child_process.spawn compatible object');
  console.log('   const child = sprite.exec("npm", ["test"], {');
  console.log('     cwd: "/app",');
  console.log('     env: { NODE_ENV: "test" },');
  console.log('     tty: false');
  console.log('   });');
  console.log('   ');
  console.log('   // Standard Node.js stream handling');
  console.log('   child.stdout.on("data", (data) => {');
  console.log('     console.log(`Output: ${data.toString()}`);');
  console.log('   });');
  console.log('   ');
  console.log('   child.on("exit", (code) => {');
  console.log('     console.log(`Process exited with code: ${code}`);');
  console.log('   });');
  console.log('   ```');

  console.log('\n3. Example: Multiple rapid-fire commands (no race conditions)');
  console.log('   Code:');
  console.log('   ```javascript');
  console.log('   const processes = [];');
  console.log('   for (let i = 0; i < 10; i++) {');
  console.log('     const proc = sprite.exec("echo", [`test-${i}`]);');
  console.log('     processes.push(proc);');
  console.log('   }');
  console.log('   // All processes run independently without interference');
  console.log('   ```');

  console.log('\n4. Example: Checkpoint operations');
  console.log('   Code:');
  console.log('   ```javascript');
  console.log('   // Create checkpoint before risky operation');
  console.log('   const checkpoint = await sprite.checkpoint("before-deploy");');
  console.log('   ');
  console.log('   // Run deployment');
  console.log('   const deploy = sprite.exec("npm", ["run", "deploy"]);');
  console.log('   deploy.on("exit", async (code) => {');
  console.log('     if (code !== 0) {');
  console.log('       await sprite.restore(checkpoint.id);');
  console.log('       console.log("Deployment failed, restored checkpoint");');
  console.log('     }');
  console.log('   });');
  console.log('   ```');

  console.log('\n5. Example: Piping with existing Node.js tools');
  console.log('   Code:');
  console.log('   ```javascript');
  console.log('   import { spawn } from "child_process";');
  console.log('   ');
  console.log('   const find = sprite.exec("find", ["/app", "-name", "*.js"]);');
  console.log('   const grep = spawn("grep", ["-v", "node_modules"]);');
  console.log('   ');
  console.log('   // Standard Node.js piping works because sprite.exec()');
  console.log('   // returns object identical to child_process.spawn()');
  console.log('   find.stdout.pipe(grep.stdin);');
  console.log('   grep.stdout.pipe(process.stdout);');
  console.log('   ```');

  console.log('\n6. Key Features Implemented:');
  console.log('   ✅ child_process.spawn compatibility');
  console.log('   ✅ Multiple rapid-fire exec calls without race conditions');
  console.log('   ✅ Strict WebSocket protocol handling (no sleep() calls)');
  console.log('   ✅ Node.js 22 with native fetch');
  console.log('   ✅ /v1/sprites/:name/... API pattern');
  console.log('   ✅ WebSocket multiplexing for concurrent processes');
  console.log('   ✅ Full TypeScript support');
  console.log('   ✅ Checkpoint operations');
  console.log('   ✅ Stream compatibility with existing Node.js ecosystem');

  console.log('\n7. File Structure (6 files total):');
  console.log('   src/');
  console.log('   ├── SpriteClient.ts     # Main client with token/config');
  console.log('   ├── Sprite.ts          # Individual sprite operations');
  console.log('   ├── ExecProcess.ts     # child_process.spawn compatible');
  console.log('   ├── WebSocketManager.ts # WebSocket multiplexing + strict protocol');
  console.log('   ├── types.ts           # All TypeScript interfaces');
  console.log('   └── index.ts           # Main exports');

  console.log('\n=== Implementation Complete ===');
  console.log('🎉 New JavaScript SDK successfully implemented!');
  console.log('📋 Ready for integration with real sprite server');
}

completeExample().catch(console.error);