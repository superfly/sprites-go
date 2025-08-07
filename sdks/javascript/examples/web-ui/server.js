import express from 'express';
import expressWs from 'express-ws';
import { SpriteClient } from '@sprites/sdk';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Initialize express with WebSocket support
const app = express();
const wsInstance = expressWs(app);

app.use(express.json());
app.use(express.static('public'));

// Store sprite clients in memory
const spriteClients = new Map();

// API endpoint to create a sprite client
app.post('/api/init', (req, res) => {
  const { token, baseUrl } = req.body;
  
  if (!token) {
    return res.status(400).json({ error: 'Token is required' });
  }

  const clientId = Math.random().toString(36).substring(7);
  const client = new SpriteClient({
    token,
    baseUrl: baseUrl || 'https://api.sprites.dev',
    debug: true  // Enable debug logging
  });
  
  spriteClients.set(clientId, client);
  
  res.json({ clientId });
});

// API endpoint to list sprites from the API
app.get('/api/sprites/:clientId', async (req, res) => {
  const client = spriteClients.get(req.params.clientId);
  if (!client) {
    return res.status(404).json({ error: 'Client not found' });
  }
  
  try {
    const sprites = await client.list();
    res.json(sprites);
  } catch (error) {
    console.error('Error listing sprites:', error);
    // Check if it's an authentication error
    if (error.message && (error.message.includes('401') || error.message.includes('403') || 
        error.message.includes('Unauthorized') || error.message.includes('Forbidden'))) {
      res.status(401).json({ error: 'Authentication failed' });
    } else {
      res.status(500).json({ error: error.message });
    }
  }
});

// API endpoint to create a sprite
app.post('/api/sprites/:clientId/:name', async (req, res) => {
  const client = spriteClients.get(req.params.clientId);
  if (!client) {
    return res.status(404).json({ error: 'Client not found' });
  }
  
  try {
    const sprite = await client.create(req.params.name);
    res.json({ success: true, name: sprite.name });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// API endpoint to destroy a sprite
app.delete('/api/sprites/:clientId/:name', async (req, res) => {
  const client = spriteClients.get(req.params.clientId);
  if (!client) {
    return res.status(404).json({ error: 'Client not found' });
  }
  
  try {
    await client.destroy(req.params.name);
    res.json({ success: true });
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

// WebSocket endpoint for terminal
app.ws('/api/terminal/:clientId/:spriteName', (ws, req) => {
  const client = spriteClients.get(req.params.clientId);
  if (!client) {
    ws.close(1008, 'Client not found');
    return;
  }

  const sprite = client.sprite(req.params.spriteName);
  let execProcess = null;
  
  console.log(`Terminal connection established for sprite: ${req.params.spriteName}`);
  
  // Track stats
  let bytesSentToClient = 0;
  let bytesReceivedFromClient = 0;
  const statsInterval = setInterval(() => {
    console.log(`[Server Stats - ${req.params.spriteName}] Client->Server: ${bytesReceivedFromClient} bytes, Server->Client: ${bytesSentToClient} bytes`);
  }, 10000); // Log every 10 seconds

  try {
    // Use the SDK's spawn method to start a bash shell
    console.log('Starting bash shell via SDK spawn...');
    // Get initial terminal size from query params or defaults
    const cols = parseInt(req.query.cols) || 80;
    const rows = parseInt(req.query.rows) || 24;
    console.log(`Initial terminal size: ${cols}x${rows}`);
    
    execProcess = sprite.spawn('/bin/bash', ['-l'], {
      tty: true,
      env: {
        TERM: 'xterm-256color',
        COLORTERM: 'truecolor',
        LANG: 'en_US.UTF-8',
        LC_ALL: 'en_US.UTF-8',
        COLUMNS: String(cols),
        LINES: String(rows),
        SHELL: '/bin/bash',
        USER: 'sprite',
        HOME: '/home/sprite',
        PATH: '/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'
      }
    });
    
    console.log('Process spawned, setting up event handlers...');
    console.log('execProcess object:', {
      hasStdout: !!execProcess.stdout,
      hasStderr: !!execProcess.stderr,
      hasStdin: !!execProcess.stdin,
      processId: execProcess.processId
    });

    // Handle stdout data from the exec process
    execProcess.stdout.on('data', (data) => {
      if (ws.readyState === ws.OPEN) {
        // Ensure we're sending Buffer/binary data
        const buffer = Buffer.isBuffer(data) ? data : Buffer.from(data);
        bytesSentToClient += buffer.length;
        ws.send(buffer);
      }
    });

    // Handle stderr data from the exec process
    execProcess.stderr.on('data', (data) => {
      if (ws.readyState === ws.OPEN) {
        // Send raw binary data directly to browser
        const buffer = Buffer.isBuffer(data) ? data : Buffer.from(data);
        bytesSentToClient += buffer.length;
        ws.send(buffer);
      }
    });

    // Handle process spawn event
    execProcess.on('spawn', () => {
      console.log('✅ Process spawned successfully');
    });

    // Handle process exit
    execProcess.on('exit', (code, signal) => {
      console.log(`Process exited with code ${code}, signal ${signal}`);
      if (ws.readyState === ws.OPEN) {
        // Send exit message as text
        ws.send(`\r\n*** Process exited with code ${code} ***\r\n`);
        ws.close();
      }
    });

    // Handle process errors
    execProcess.on('error', (error) => {
      console.error('Process error:', error.message);
      if (ws.readyState === ws.OPEN) {
        // Send error message as text
        ws.send(`\r\n*** Process error: ${error.message} ***\r\n`);
      }
    });

  } catch (error) {
    console.error('Failed to spawn process:', error.message);
    if (ws.readyState === ws.OPEN) {
      ws.send(`\r\n*** Failed to start terminal: ${error.message} ***\r\n`);
      ws.close();
    }
    return;
  }

  // Handle input from browser to exec process
  ws.on('message', (msg) => {
    // Check if it's a text message (resize command)
    if (typeof msg === 'string') {
      try {
        const parsed = JSON.parse(msg);
        if (parsed.type === 'resize' && execProcess) {
          // Call the resize method on the execProcess
          if (execProcess.resize) {
            execProcess.resize(parsed.cols, parsed.rows);
          }
        }
      } catch (e) {
        // Not JSON, treat as binary stdin
        if (execProcess && execProcess.stdin) {
          const buffer = Buffer.from(msg, 'utf8');
          bytesReceivedFromClient += buffer.length;
          execProcess.stdin.write(buffer);
        }
      }
    } else {
      // Binary data - send to stdin
      if (execProcess && execProcess.stdin) {
        const buffer = Buffer.isBuffer(msg) ? msg : Buffer.from(msg);
        bytesReceivedFromClient += buffer.length;
        execProcess.stdin.write(buffer);
      }
    }
  });

  ws.on('close', () => {
    console.log('Browser WebSocket closed, killing process');
    clearInterval(statsInterval);
    console.log(`[Server Final Stats - ${req.params.spriteName}] Total Client->Server: ${bytesReceivedFromClient} bytes, Total Server->Client: ${bytesSentToClient} bytes`);
    
    if (execProcess) {
      try {
        execProcess.kill();
        console.log('Process killed');
      } catch (error) {
        console.error('Error killing process:', error);
      }
    }
  });

  ws.on('error', (error) => {
    console.error('Browser WebSocket error:', error);
    if (execProcess) {
      try {
        execProcess.kill();
      } catch (error) {
        console.error('Error killing process:', error);
      }
    }
  });
});

// Start server
const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`Sprite Web UI running on http://localhost:${PORT}`);
  console.log('Open this URL in your browser to use the Sprite terminal');
});