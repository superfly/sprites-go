#!/usr/bin/env node

import { SpritesClient } from '../dist/index.js';

async function basicUsageExample() {
  // Create a client instance
  const client = new SpritesClient({
    endpoint: process.env.SPRITE_URL || 'http://localhost:28080',
    token: process.env.SPRITE_TOKEN || 'your-token-here'
  });

  // Attach to a sprite
  const sprite = client.attach('my-sprite');

  try {
    console.log('=== Basic Command Execution ===');
    
    // Spawn a simple command (child_process.spawn compatible)
    console.log('1. Using spawn (like child_process.spawn):');
    const child1 = sprite.spawn('echo', ['Hello from Sprite!']);
    
    child1.stdout.on('data', (data) => {
      console.log(`Output: ${data.toString().trim()}`);
    });
    
    await new Promise((resolve) => {
      child1.on('close', (code) => {
        console.log(`Exit Code: ${code}`);
        resolve();
      });
    });

    // Execute command with callback (child_process.exec compatible)
    console.log('\n2. Using exec with callback (like child_process.exec):');
    await new Promise((resolve, reject) => {
      sprite.exec('ls -la /tmp', (error, stdout, stderr) => {
        if (error) {
          reject(error);
          return;
        }
        console.log('Listing /tmp:');
        console.log(stdout);
        resolve();
      });
    });

    // Execute command with working directory
    const result3 = await sprite.exec(['pwd'], { workingDir: '/home' });
    console.log(`\nWorking directory test:`);
    console.log(`Current dir: ${result3.stdout.trim()}`);

    // Execute command with environment variables
    const result4 = await sprite.exec(['sh', '-c', 'echo "Hello $NAME"'], {
      env: { NAME: 'JavaScript SDK' }
    });
    console.log(`\nEnvironment variable test:`);
    console.log(result4.stdout);

  } catch (error) {
    console.error(`Error: ${error.message}`);
    process.exit(1);
  }
}

basicUsageExample();