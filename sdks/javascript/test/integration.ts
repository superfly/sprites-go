#!/usr/bin/env node

import { SpriteClient } from '../src/index.js';

async function runIntegrationTests() {
  const endpoint = process.env.SPRITE_URL || 'http://localhost:28080';
  const token = process.env.SPRITE_TOKEN || 'f0e4c2f76c58916ec258f246851bea091d14d4247a2fc3e18694461b1816e13b';
  
  console.log(`Running integration tests against: ${endpoint}`);
  
  try {
    const client = new SpriteClient({ token, baseUrl: endpoint });
    const sprite = client.sprite('test-sprite');
    
    // Test basic exec
    console.log('Testing basic exec...');
    const result1 = await sprite.exec(['echo', 'hello']);
    console.log(`Exit code: ${result1.exitCode}, stdout: "${result1.stdout.trim()}"`);
    
    if (result1.exitCode !== 0 || result1.stdout.trim() !== 'hello') {
      throw new Error('Basic exec test failed');
    }
    
    // Test exec with args
    console.log('Testing exec with multiple args...');
    const result2 = await sprite.exec(['echo', 'hello', 'world']);
    console.log(`Exit code: ${result2.exitCode}, stdout: "${result2.stdout.trim()}"`);
    
    if (result2.exitCode !== 0 || result2.stdout.trim() !== 'hello world') {
      throw new Error('Exec with args test failed');
    }
    
    // Test exec with working directory
    console.log('Testing exec with working directory...');
    const result3 = await sprite.exec(['pwd'], { workingDir: '/tmp' });
    console.log(`Exit code: ${result3.exitCode}, stdout: "${result3.stdout.trim()}"`);
    
    if (result3.exitCode !== 0 || result3.stdout.trim() !== '/tmp') {
      throw new Error('Working directory test failed');
    }
    
    // Test exec with environment variable
    console.log('Testing exec with environment variable...');
    const result4 = await sprite.exec(['sh', '-c', 'echo $TEST_VAR'], { 
      env: { TEST_VAR: 'test_value' } 
    });
    console.log(`Exit code: ${result4.exitCode}, stdout: "${result4.stdout.trim()}"`);
    
    if (result4.exitCode !== 0 || result4.stdout.trim() !== 'test_value') {
      throw new Error('Environment variable test failed');
    }
    
    // Test exit code
    console.log('Testing exit code...');
    const result5 = await sprite.exec(['false']);
    console.log(`Exit code: ${result5.exitCode}`);
    
    if (result5.exitCode === 0) {
      throw new Error('Exit code test failed - expected non-zero exit code');
    }
    
    // Test stdout/stderr
    console.log('Testing stdout/stderr...');
    const result6 = await sprite.exec(['sh', '-c', 'echo stdout && echo stderr >&2']);
    console.log(`Exit code: ${result6.exitCode}, stdout: "${result6.stdout.trim()}", stderr: "${result6.stderr.trim()}"`);
    
    if (result6.exitCode !== 0 || !result6.stdout.includes('stdout') || !result6.stderr.includes('stderr')) {
      throw new Error('Stdout/stderr test failed');
    }
    
    console.log('All integration tests passed!');
    
  } catch (error) {
    console.error(`Integration test failed: ${error}`);
    process.exit(1);
  }
}

runIntegrationTests();