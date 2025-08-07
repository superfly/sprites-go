#!/usr/bin/env node

import { SpritesClient } from '../dist/index.js';

async function checkpointExample() {
  const client = new SpritesClient({
    endpoint: process.env.SPRITE_URL || 'http://localhost:28080',
    token: process.env.SPRITE_TOKEN || 'your-token-here'
  });

  const sprite = client.attach('my-sprite');

  try {
    console.log('=== Checkpoint Operations ===');

    // Create some state to checkpoint
    await sprite.exec(['mkdir', '-p', '/tmp/checkpoint-test']);
    await sprite.exec(['sh', '-c', 'echo "Initial state" > /tmp/checkpoint-test/file.txt']);
    
    console.log('Created initial state');

    // Create a checkpoint
    const checkpoint1 = await sprite.checkpoint({ name: 'initial-state' });
    console.log(`Created checkpoint: ${checkpoint1.id}`);

    // Modify the state
    await sprite.exec(['sh', '-c', 'echo "Modified state" > /tmp/checkpoint-test/file.txt']);
    console.log('Modified state');

    // Create another checkpoint
    const checkpoint2 = await sprite.checkpoint({ name: 'modified-state' });
    console.log(`Created checkpoint: ${checkpoint2.id}`);

    // List all checkpoints
    console.log('\nListing all checkpoints:');
    const checkpoints = await sprite.listCheckpoints();
    for (const cp of checkpoints) {
      console.log(`  ${cp.id} - Created: ${cp.createTime.toISOString()}`);
    }

    // Restore to first checkpoint
    console.log(`\nRestoring to checkpoint: ${checkpoint1.id}`);
    const restored = await sprite.restore({ checkpointId: checkpoint1.id });
    
    if (restored) {
      console.log('Restoration successful!');
      
      // Verify the restoration
      const result = await sprite.exec(['cat', '/tmp/checkpoint-test/file.txt']);
      console.log(`File content after restore: ${result.stdout.trim()}`);
    } else {
      console.log('Restoration failed');
    }

  } catch (error) {
    console.error(`Error: ${error.message}`);
    process.exit(1);
  }
}

checkpointExample();