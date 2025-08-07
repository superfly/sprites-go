#!/usr/bin/env node

import { SpritesClient } from '../dist/index.js';

async function streamingExample() {
  const client = new SpritesClient({
    endpoint: process.env.SPRITE_URL || 'http://localhost:28080',
    token: process.env.SPRITE_TOKEN || 'your-token-here'
  });

  const sprite = client.attach('my-sprite');

  try {
    console.log('=== Streaming Command Execution ===');

    // Example 1: Real-time output streaming
    console.log('\n1. Streaming a long-running command with real-time output:');
    
    const result1 = await sprite.execStream(['sh', '-c', 'for i in {1..5}; do echo "Line $i"; sleep 1; done'], {
      onStdout: (data) => {
        process.stdout.write(`[STDOUT] ${data}`);
      },
      onStderr: (data) => {
        process.stderr.write(`[STDERR] ${data}`);
      }
    });
    
    console.log(`\nCommand completed with exit code: ${result1.exitCode}`);

    // Example 2: Command with both stdout and stderr
    console.log('\n2. Command that outputs to both stdout and stderr:');
    
    const result2 = await sprite.execStream(['sh', '-c', 'echo "This goes to stdout" && echo "This goes to stderr" >&2'], {
      onStdout: (data) => {
        console.log(`📤 STDOUT: ${data.trim()}`);
      },
      onStderr: (data) => {
        console.log(`📤 STDERR: ${data.trim()}`);
      }
    });

    console.log(`Command completed with exit code: ${result2.exitCode}`);

    // Example 3: Command with timeout
    console.log('\n3. Command with timeout (will be interrupted):');
    
    try {
      await sprite.execStream(['sleep', '10'], {
        timeout: 2000, // 2 second timeout
        onStdout: (data) => console.log(`Output: ${data}`),
      });
    } catch (error) {
      console.log(`Command timed out as expected: ${error.message}`);
    }

    // Example 4: Interactive-style command monitoring
    console.log('\n4. Monitoring a process with progress indication:');
    
    let lineCount = 0;
    const result4 = await sprite.execStream(['sh', '-c', 'find /usr -name "*.so" | head -20'], {
      onStdout: (data) => {
        const lines = data.split('\n').filter(line => line.trim());
        lineCount += lines.length;
        process.stdout.write(`\rFiles found: ${lineCount}`);
      }
    });
    
    console.log(`\nSearch completed. Found ${lineCount} files.`);

  } catch (error) {
    console.error(`Error: ${error.message}`);
    process.exit(1);
  }
}

streamingExample();