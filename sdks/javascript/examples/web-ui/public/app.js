// Client state
let clientId = null;
let currentSpriteName = null;
const terminals = {}; // Store terminal instances by sprite name
const connections = {}; // Store WebSocket connections by sprite name

// Cookie management
function setCookie(name, value, days = 7) {
  const expires = new Date(Date.now() + days * 24 * 60 * 60 * 1000).toUTCString();
  document.cookie = `${name}=${encodeURIComponent(value)}; expires=${expires}; path=/`;
}

function getCookie(name) {
  const match = document.cookie.match(new RegExp('(^| )' + name + '=([^;]+)'));
  return match ? decodeURIComponent(match[2]) : null;
}

function deleteCookie(name) {
  document.cookie = `${name}=; expires=Thu, 01 Jan 1970 00:00:00 UTC; path=/`;
}

// Update status bar
function updateStatus(text, isError = false) {
  const statusEl = document.getElementById('statusText');
  statusEl.textContent = text;
  statusEl.style.color = isError ? '#f14c4c' : '';
}

function updateStats(text) {
  document.getElementById('statsText').textContent = text;
}

// Show login error
function showLoginError(message) {
  const errorEl = document.getElementById('loginError');
  errorEl.textContent = message;
  errorEl.classList.add('show');
}

// Clear login error
function clearLoginError() {
  const errorEl = document.getElementById('loginError');
  errorEl.classList.remove('show');
}

// Connect to API
async function connect() {
  const token = document.getElementById('token').value;
  const baseUrl = document.getElementById('baseUrl').value || 'https://api.sprites.dev';
  
  // Clear any previous errors
  clearLoginError();
  
  if (!token) {
    showLoginError('Please enter an API token');
    return;
  }

  const button = document.querySelector('.login-button');
  button.disabled = true;
  button.textContent = 'Connecting...';
  
  try {
    const response = await fetch('/api/init', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ token, baseUrl })
    });
    
    if (!response.ok) {
      throw new Error('Invalid token or connection failed');
    }
    
    const data = await response.json();
    clientId = data.clientId;
    
    // Save to cookies
    setCookie('sprite_token', token);
    setCookie('sprite_base_url', baseUrl);
    
    // Update UI
    document.getElementById('loginContainer').style.display = 'none';
    document.getElementById('mainContainer').classList.add('active');
    updateStatus('Connected to Sprite API');
    
    // Load sprites (will handle auth failures)
    await loadSprites();
  } catch (error) {
    console.error('Connection error:', error);
    showLoginError(error.message || 'Failed to connect');
    button.disabled = false;
    button.textContent = 'Connect';
  }
}

// Logout
function logout(errorMessage = null) {
  deleteCookie('sprite_token');
  deleteCookie('sprite_base_url');
  
  // Cleanup all connections and terminals
  Object.keys(connections).forEach(name => {
    if (connections[name]) {
      if (connections[name].ws) {
        connections[name].ws.close();
      }
      if (connections[name].statsInterval) {
        clearInterval(connections[name].statsInterval);
      }
    }
  });
  
  Object.keys(terminals).forEach(name => {
    if (terminals[name]) {
      // Remove resize handler if it exists
      if (terminals[name].resizeHandler) {
        window.removeEventListener('resize', terminals[name].resizeHandler);
      }
      terminals[name].terminal.dispose();
    }
  });
  
  // Clear state
  clientId = null;
  currentSpriteName = null;
  Object.keys(terminals).forEach(key => delete terminals[key]);
  Object.keys(connections).forEach(key => delete connections[key]);
  
  // Reset UI
  document.getElementById('loginContainer').style.display = 'flex';
  document.getElementById('mainContainer').classList.remove('active');
  document.getElementById('token').value = '';
  
  // Reset login button
  const button = document.querySelector('.login-button');
  if (button) {
    button.disabled = false;
    button.textContent = 'Connect';
  }
  
  // Show error if provided
  if (errorMessage) {
    showLoginError(errorMessage);
  }
  
  updateStatus('Disconnected');
  updateStats('');
}

// Load sprites
async function loadSprites() {
  if (!clientId) return;
  
  try {
    const response = await fetch(`/api/sprites/${clientId}`);
    
    // Check for authentication failure
    if (response.status === 401 || response.status === 403) {
      console.error('Authentication failed, returning to login');
      logout('Invalid or expired token. Please login again.');
      return;
    }
    
    if (!response.ok) {
      throw new Error(`Failed to load sprites: ${response.statusText}`);
    }
    
    const sprites = await response.json();
    
    const listEl = document.getElementById('spriteList');
    listEl.innerHTML = '';
    
    sprites.forEach(sprite => {
      const item = document.createElement('div');
      item.className = 'sprite-item';
      item.id = `sprite-item-${sprite.name}`;
      
      // Mark as active if it's the current sprite
      if (sprite.name === currentSpriteName) {
        item.classList.add('active');
      }
      
      // Mark as connected if we have an active connection
      if (connections[sprite.name] && connections[sprite.name].ws && 
          connections[sprite.name].ws.readyState === WebSocket.OPEN) {
        item.classList.add('connected');
      }
      
      // Build menu items based on connection status
      const isConnected = connections[sprite.name] && connections[sprite.name].ws && 
                         connections[sprite.name].ws.readyState === WebSocket.OPEN;
      
      const menuItems = isConnected ? 
        `<div class="dropdown-item" onclick="disconnectSprite('${sprite.name}')">Disconnect</div>
         <div class="dropdown-item danger" onclick="deleteSprite('${sprite.name}')">Delete</div>` :
        `<div class="dropdown-item danger" onclick="deleteSprite('${sprite.name}')">Delete</div>`;
      
      item.innerHTML = `
        <div class="sprite-info" onclick="switchToSprite('${sprite.name}')">
          <div class="sprite-name">
            <span class="connection-indicator"></span>
            ${sprite.name}
          </div>
          <div class="sprite-date">${new Date(sprite.created_at).toLocaleString()}</div>
        </div>
        <div class="dropdown">
          <button class="sprite-menu-btn" onclick="toggleMenu(event, '${sprite.name}')">⋯</button>
          <div class="dropdown-menu" id="menu-${sprite.name}">
            ${menuItems}
          </div>
        </div>
      `;
      
      listEl.appendChild(item);
    });
  } catch (error) {
    console.error('Error loading sprites:', error);
    
    // Check if it's likely an auth issue
    if (error.message && error.message.includes('fetch')) {
      logout('Connection failed. Please check your token and try again.');
    } else {
      updateStatus('Failed to load sprites', true);
    }
  }
}

// Toggle dropdown menu
function toggleMenu(event, spriteName) {
  event.stopPropagation();
  
  // Close all other menus
  document.querySelectorAll('.dropdown-menu').forEach(menu => {
    if (menu.id !== `menu-${spriteName}`) {
      menu.classList.remove('show');
    }
  });
  
  // Toggle this menu
  const menu = document.getElementById(`menu-${spriteName}`);
  menu.classList.toggle('show');
}

// Close menus when clicking outside
document.addEventListener('click', () => {
  document.querySelectorAll('.dropdown-menu').forEach(menu => {
    menu.classList.remove('show');
  });
});

// Create sprite
async function createSprite() {
  const nameInput = document.getElementById('newSpriteName');
  const name = nameInput.value.trim();
  
  if (!name || !clientId) return;
  
  try {
    const response = await fetch(`/api/sprites/${clientId}/${name}`, {
      method: 'POST'
    });
    
    if (!response.ok) {
      throw new Error('Failed to create sprite');
    }
    
    nameInput.value = '';
    loadSprites();
    updateStatus(`Created sprite: ${name}`);
  } catch (error) {
    console.error('Error creating sprite:', error);
    updateStatus('Failed to create sprite', true);
  }
}

// Disconnect sprite
function disconnectSprite(name) {
  // Close the menu
  document.querySelectorAll('.dropdown-menu').forEach(menu => {
    menu.classList.remove('show');
  });
  
  // Close the WebSocket connection
  if (connections[name]) {
    if (connections[name].ws) {
      connections[name].ws.close();
    }
    if (connections[name].statsInterval) {
      clearInterval(connections[name].statsInterval);
    }
    delete connections[name];
  }
  
  // Remove the terminal
  if (terminals[name]) {
    const termDiv = document.getElementById(`terminal-${name}`);
    if (termDiv) termDiv.remove();
    
    // Remove resize handler if it exists
    if (terminals[name].resizeHandler) {
      window.removeEventListener('resize', terminals[name].resizeHandler);
    }
    
    terminals[name].terminal.dispose();
    delete terminals[name];
  }
  
  // If this was the active sprite, show empty state
  if (currentSpriteName === name) {
    currentSpriteName = null;
    document.getElementById('emptyState').classList.remove('hidden');
    updateStatus('Ready');
    updateStats('');
  }
  
  // Reload sprites to update UI
  loadSprites();
  updateStatus(`Disconnected from ${name}`);
}

// Delete sprite
async function deleteSprite(name) {
  if (!clientId) return;
  
  // Close the menu
  document.querySelectorAll('.dropdown-menu').forEach(menu => {
    menu.classList.remove('show');
  });
  
  if (!confirm(`Delete sprite "${name}"?`)) return;
  
  try {
    const response = await fetch(`/api/sprites/${clientId}/${name}`, {
      method: 'DELETE'
    });
    
    if (!response.ok) {
      throw new Error('Failed to delete sprite');
    }
    
    // Clean up any existing connection and terminal
    if (connections[name]) {
      if (connections[name].ws) {
        connections[name].ws.close();
      }
      if (connections[name].statsInterval) {
        clearInterval(connections[name].statsInterval);
      }
      delete connections[name];
    }
    
    if (terminals[name]) {
      const termDiv = document.getElementById(`terminal-${name}`);
      if (termDiv) termDiv.remove();
      
      // Remove resize handler if it exists
      if (terminals[name].resizeHandler) {
        window.removeEventListener('resize', terminals[name].resizeHandler);
      }
      
      terminals[name].terminal.dispose();
      delete terminals[name];
    }
    
    // If we were viewing this sprite, show empty state
    if (currentSpriteName === name) {
      currentSpriteName = null;
      document.getElementById('emptyState').classList.remove('hidden');
      updateStatus('Ready');
      updateStats('');
    }
    
    loadSprites();
    updateStatus(`Deleted sprite: ${name}`);
  } catch (error) {
    console.error('Error deleting sprite:', error);
    updateStatus('Failed to delete sprite', true);
  }
}

// Switch to sprite (show existing or create new terminal)
function switchToSprite(spriteName) {
  if (!clientId) return;
  
  // Close any open menus
  document.querySelectorAll('.dropdown-menu').forEach(menu => {
    menu.classList.remove('show');
  });
  
  // If already viewing this sprite, do nothing
  if (currentSpriteName === spriteName) {
    return;
  }
  
  // Hide current terminal
  if (currentSpriteName) {
    const currentTermDiv = document.getElementById(`terminal-${currentSpriteName}`);
    if (currentTermDiv) {
      currentTermDiv.classList.remove('active');
    }
  }
  
  // Update current sprite
  currentSpriteName = spriteName;
  
  // Update UI
  document.getElementById('emptyState').classList.add('hidden');
  
  // Update active sprite in list
  document.querySelectorAll('.sprite-item').forEach(item => {
    item.classList.remove('active');
  });
  const activeItem = document.getElementById(`sprite-item-${spriteName}`);
  if (activeItem) {
    activeItem.classList.add('active');
  }
  
  // Check if we already have a terminal for this sprite
  if (terminals[spriteName]) {
    // Show existing terminal
    const termDiv = document.getElementById(`terminal-${spriteName}`);
    termDiv.classList.add('active');
    
    // Fit the terminal to the container and focus
    setTimeout(() => {
      terminals[spriteName].fitAddon.fit();
      terminals[spriteName].terminal.focus();
    }, 50);
    
    // Update status with existing connection info
    if (connections[spriteName]) {
      updateStatus(`Connected to ${spriteName}`);
      updateStats(`↑ ${connections[spriteName].bytesSent} bytes | ↓ ${connections[spriteName].bytesReceived} bytes`);
    }
  } else {
    // Create new terminal and connection
    createTerminalForSprite(spriteName);
  }
}

// Create terminal and WebSocket connection for sprite
function createTerminalForSprite(spriteName) {
  // Create terminal container
  const termDiv = document.createElement('div');
  termDiv.id = `terminal-${spriteName}`;
  termDiv.className = 'terminal-instance active';
  document.getElementById('terminals').appendChild(termDiv);
  
  // Create terminal with mouse support
  const terminal = new Terminal({
    cursorBlink: true,
    fontSize: 14,
    fontFamily: 'Menlo, Monaco, "Courier New", monospace',
    theme: {
      background: '#1e1e1e',
      foreground: '#d4d4d4'
    },
    // Enable mouse support
    mouseEvents: true,
    rightClickSelectsWord: true,
    altClickMovesCursor: true
  });
  
  const fitAddon = new FitAddon.FitAddon();
  terminal.loadAddon(fitAddon);
  terminal.open(termDiv);
  
  // Store terminal instance
  terminals[spriteName] = {
    terminal: terminal,
    fitAddon: fitAddon
  };
  
  // Initial fit to get container size
  fitAddon.fit();
  
  // Wait for terminal to be ready and get actual dimensions
  setTimeout(() => {
    fitAddon.fit();
    terminal.focus();
    
    // Get actual terminal size after fitting
    const cols = terminal.cols;
    const rows = terminal.rows;
    
    // Create WebSocket connection with correct dimensions
    const wsUrl = `/api/terminal/${clientId}/${spriteName}?cols=${cols}&rows=${rows}`;
    const ws = new WebSocket(wsUrl.replace(/^http/, 'ws'));
    ws.binaryType = 'arraybuffer';
    
    // Initialize connection data
    connections[spriteName] = {
      ws: ws,
      bytesReceived: 0,
      bytesSent: 0,
      statsInterval: null
    };
    
    // Start stats interval
    connections[spriteName].statsInterval = setInterval(() => {
      if (currentSpriteName === spriteName) {
        updateStats(`↑ ${connections[spriteName].bytesSent} bytes | ↓ ${connections[spriteName].bytesReceived} bytes`);
      }
    }, 1000);
    
    ws.onopen = () => {
      console.log(`WebSocket connected for ${spriteName}`);
      updateStatus(`Connected to ${spriteName}`);
      
      // Update sprite item to show connection
      const item = document.getElementById(`sprite-item-${spriteName}`);
      if (item) {
        item.classList.add('connected');
      }
    };
    
    // Track if we've sent initial resize
    let hasReceivedFirstMessage = false;
    
    ws.onmessage = (event) => {
      // Send resize after first message received
      if (!hasReceivedFirstMessage) {
        hasReceivedFirstMessage = true;
        // Send correct terminal size after connection is established
        const resizeMsg = JSON.stringify({
          type: 'resize',
          cols: terminal.cols,
          rows: terminal.rows
        });
        ws.send(resizeMsg);
        console.log(`Sent initial resize: ${terminal.cols}x${terminal.rows}`);
      }
      
      // Only process messages if this is the active sprite
      if (event.data instanceof ArrayBuffer) {
        connections[spriteName].bytesReceived += event.data.byteLength;
        const data = new Uint8Array(event.data);
        const text = new TextDecoder('utf-8').decode(data);
        terminal.write(text);
      } else if (typeof event.data === 'string') {
        connections[spriteName].bytesReceived += event.data.length;
        terminal.write(event.data);
      }
    };
    
    ws.onerror = (error) => {
      console.error(`WebSocket error for ${spriteName}:`, error);
      if (currentSpriteName === spriteName) {
        updateStatus(`Connection error: ${spriteName}`, true);
      }
    };
    
    ws.onclose = () => {
      console.log(`WebSocket disconnected for ${spriteName}`);
      
      // Clear stats interval
      if (connections[spriteName] && connections[spriteName].statsInterval) {
        clearInterval(connections[spriteName].statsInterval);
      }
      
      // Update sprite item to show disconnection
      const item = document.getElementById(`sprite-item-${spriteName}`);
      if (item) {
        item.classList.remove('connected');
      }
      
      if (currentSpriteName === spriteName) {
        updateStatus(`Disconnected from ${spriteName}`);
        updateStats(`Total: ↑ ${connections[spriteName].bytesSent} bytes | ↓ ${connections[spriteName].bytesReceived} bytes`);
      }
      
      // Mark connection as closed
      if (connections[spriteName]) {
        connections[spriteName].ws = null;
      }
    };
    
    // Handle terminal input
    terminal.onData(data => {
      if (ws.readyState === WebSocket.OPEN) {
        const binary = new TextEncoder().encode(data);
        connections[spriteName].bytesSent += binary.length;
        ws.send(binary);
      }
    });
    
    // Handle resize
    terminal.onResize(({ cols, rows }) => {
      console.log(`Terminal resized for ${spriteName}: ${cols}x${rows}`);
      if (ws.readyState === WebSocket.OPEN) {
        const resizeMsg = JSON.stringify({
          type: 'resize',
          cols: cols,
          rows: rows
        });
        ws.send(resizeMsg);
      }
    });
    
    // Handle window resize for this terminal
    const resizeHandler = () => {
      if (currentSpriteName === spriteName && fitAddon) {
        fitAddon.fit();
      }
    };
    window.addEventListener('resize', resizeHandler);
    
    // Store resize handler so we can remove it later if needed
    terminals[spriteName].resizeHandler = resizeHandler;
  }, 100); // Give terminal time to properly initialize
}

// Initialize on page load
document.addEventListener('DOMContentLoaded', () => {
  // Try to connect with saved credentials
  const savedToken = getCookie('sprite_token');
  const savedBaseUrl = getCookie('sprite_base_url');
  
  if (savedToken) {
    document.getElementById('token').value = savedToken;
    if (savedBaseUrl) {
      document.getElementById('baseUrl').value = savedBaseUrl;
    }
    connect();
  }
  
  // Enter key in sprite name input creates sprite
  document.getElementById('newSpriteName').addEventListener('keypress', (e) => {
    if (e.key === 'Enter') {
      createSprite();
    }
  });
  
  // Focus token input
  document.getElementById('token').focus();
  
  // Focus current terminal when window gains focus
  window.addEventListener('focus', () => {
    if (currentSpriteName && terminals[currentSpriteName]) {
      terminals[currentSpriteName].terminal.focus();
    }
  });
});