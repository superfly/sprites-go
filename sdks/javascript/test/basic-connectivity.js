#!/usr/bin/env node

// Basic connectivity test that doesn't require the SDK to be built
// This tests that we can reach the sprite server and basic Node.js functionality

import http from 'http';
import { spawn } from 'child_process';

async function testConnectivity() {
  const spriteUrl = process.env.SPRITE_URL || 'http://localhost:28080';
  const spriteToken = process.env.SPRITE_TOKEN || 'f0e4c2f76c58916ec258f246851bea091d14d4247a2fc3e18694461b1816e13b';
  
  console.log('=== Basic Connectivity Test ===');
  console.log(`Testing connection to: ${spriteUrl}`);
  console.log(`Using token: ${spriteToken.substring(0, 8)}...`);
  console.log(`Node.js version: ${process.version}`);
  
  // Test 1: Basic HTTP connectivity
  console.log('\n1. Testing HTTP connectivity...');
  try {
    const url = new URL(spriteUrl);
    await new Promise((resolve, reject) => {
      let resolved = false;
      
      const req = http.request({
        hostname: url.hostname,
        port: url.port,
        path: '/',
        method: 'GET',
        headers: {
          'Authorization': `Bearer ${spriteToken}`
        },
        timeout: 5000
      }, (res) => {
        if (!resolved) {
          resolved = true;
          console.log(`   ✓ HTTP response: ${res.statusCode} ${res.statusMessage}`);
          resolve();
        }
      });
      
      req.on('error', (err) => {
        if (!resolved) {
          resolved = true;
          console.log(`   ✗ HTTP error: ${err.message}`);
          reject(err);
        }
      });
      
      req.on('timeout', () => {
        if (!resolved) {
          resolved = true;
          console.log('   ✗ HTTP timeout');
          req.destroy();
          reject(new Error('HTTP timeout'));
        }
      });
      
      req.end();
    });
  } catch (error) {
    console.log(`   ✗ HTTP connectivity failed: ${error.message}`);
  }
  
  // Test 2: Child process spawn compatibility
  console.log('\n2. Testing child_process.spawn...');
  try {
    await new Promise((resolve, reject) => {
      const child = spawn('echo', ['Hello', 'from', 'spawn!']);
      let output = '';
      
      child.stdout.on('data', (data) => {
        output += data.toString();
      });
      
      child.on('exit', (code) => {
        if (code === 0) {
          console.log(`   ✓ spawn output: ${output.trim()}`);
          console.log(`   ✓ spawn exit code: ${code}`);
          resolve();
        } else {
          console.log(`   ✗ spawn failed with exit code: ${code}`);
          reject(new Error(`spawn failed: ${code}`));
        }
      });
      
      child.on('error', (err) => {
        console.log(`   ✗ spawn error: ${err.message}`);
        reject(err);
      });
    });
  } catch (error) {
    console.log(`   ✗ spawn test failed: ${error.message}`);
  }
  
  // Test 3: Multiple rapid spawn calls (testing the core requirement)
  console.log('\n3. Testing rapid-fire spawn calls...');
  try {
    const promises = [];
    for (let i = 0; i < 5; i++) {
      promises.push(new Promise((resolve, reject) => {
        const child = spawn('echo', [`test-${i}`]);
        let output = '';
        
        child.stdout.on('data', (data) => {
          output += data.toString();
        });
        
        child.on('exit', (code) => {
          if (code === 0) {
            resolve({ id: i, output: output.trim() });
          } else {
            reject(new Error(`Process ${i} failed with code ${code}`));
          }
        });
        
        child.on('error', reject);
      }));
    }
    
    const results = await Promise.all(promises);
    console.log('   ✓ All rapid-fire processes completed:');
    results.forEach(result => {
      console.log(`     Process ${result.id}: ${result.output}`);
    });
  } catch (error) {
    console.log(`   ✗ Rapid-fire test failed: ${error.message}`);
  }
  
  console.log('\n=== Basic connectivity tests completed ===');
}

// Run the test
testConnectivity().then(() => {
  console.log('Basic connectivity tests completed successfully');
  process.exit(0);
}).catch((error) => {
  console.error('Basic connectivity tests failed:', error);
  process.exit(1);
});