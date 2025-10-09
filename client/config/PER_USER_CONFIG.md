# Per-User Configuration Architecture

## Overview

The Sprite CLI uses a **per-user configuration** system that separates user-specific settings from global configuration. This allows multiple users to authenticate on the same machine without conflicts.

## Architecture

### Two-Level Configuration

1. **Global Config** (`~/.sprites/sprites.json`):
   - Version information
   - URL aliases
   - Global settings
   - List of authenticated users
   - Current user ID
   - Global organizations (fallback)

2. **Per-User Configs** (`~/.sprites/users/<userID>-<hash>.json`):
   - User-specific organizations
   - User-specific sprites
   - Same v1 config schema as global
   - One file per authenticated user

### File Locations

```
~/.sprites/
├── sprites.json                                  # Global config
└── users/
    ├── user123-a1b2c3d4e5f6a7b8.json           # User 1's config
    ├── user123-a1b2c3d4e5f6a7b8.token.enc      # User 1's encrypted Fly token
    ├── user456-9f8e7d6c5b4a3210.json           # User 2's config
    └── user456-9f8e7d6c5b4a3210.token.enc      # User 2's encrypted Fly token
```

### Filename Format

**Format**: `<userID>-<hash>.json`

**Hash**: SHA-256(userID), lowercase hex, 16 characters

**Why?**
- Case-insensitive filesystem safety (macOS, Windows)
- Deterministic (same userID = same filename)
- Only [0-9a-f] characters

## Configuration Schema

### Global Config (`sprites.json`)

```json
{
  "version": "1",
  "current_selection": {
    "url": "https://api.sprites.dev",
    "org": "my-org"
  },
  "urls": {
    "https://api.sprites.dev": {
      "url": "https://api.sprites.dev",
      "orgs": {
        "global-org": {
          "name": "global-org",
          "keyring_key": "global-org",
          "use_keyring": true,
          "sprites": {
            "my-sprite": {"name": "my-sprite"}
          }
        }
      }
    }
  },
  "url_aliases": {
    "prod": "https://api.sprites.dev"
  },
  "users": [
    {
      "id": "user123",
      "email": "alice@example.com"
    },
    {
      "id": "user456",
      "email": "bob@example.com"
    }
  ],
  "current_user": "user123"
}
```

### Per-User Config (`users/user123-hash.json`)

```json
{
  "version": "1",
  "urls": {
    "https://api.sprites.dev": {
      "url": "https://api.sprites.dev",
      "orgs": {
        "alice-org": {
          "name": "alice-org",
          "keyring_key": "sprites:org:alice-org",
          "use_keyring": true,
          "sprites": {
            "alice-sprite": {"name": "alice-sprite"}
          }
        }
      }
    }
  }
}
```

**Note**: User configs use the same v1 schema as global config, but only contain the `urls` section.

## Resolution Order

When looking up organizations or sprites:

1. **FIRST**: Check current user's config (`~/.sprites/users/<userID>-<hash>.json`)
2. **THEN**: Fall back to global config (`~/.sprites/sprites.json`)

This allows:
- User-specific overrides
- Global fallback for shared resources
- Gradual migration from global to user-scoped

## User Management

### Adding a User

```go
// Adds user to global config and creates/loads their config file
err := manager.AddUser(userID, email)
```

This:
1. Adds user to `users` list in global config
2. Sets as `current_user` if none set
3. Creates `~/.sprites/users/<userID>-<hash>.json`
4. Loads the user config into memory

### Setting Current User

```go
// Sets the current user and loads their config
err := manager.SetActiveUser(userID)
```

This:
1. Sets `current_user` in global config
2. Loads the user's config file
3. All subsequent operations use this user's config

### Removing a User

```go
// Removes user and all their data
err := manager.RemoveUser(userID)
```

This:
1. Deletes all tokens from user's keyring
2. Deletes user config file (`~/.sprites/users/<userID>-<hash>.json`)
3. Deletes encrypted Fly token (`~/.sprites/users/<userID>-<hash>.token.enc`)
4. Removes user from global config users list
5. Clears `current_user` if it was this user

## Organization Resolution

###  Adding an Organization with User

```go
// Adds org to current user's config
err := manager.AddOrgWithUser(orgName, token, url, userID, userEmail)
```

This:
1. Ensures user exists in global config
2. Loads/creates user config
3. Adds org to user's config file
4. Stores token in user-scoped keyring: `sprites-cli:<userID>` / `sprite:<orgName>`
5. Saves both global and user configs

### Getting Current Org

Resolution order:
1. Check user config first
2. Fall back to global config
3. Return error if not found in either

### Getting All Orgs

Returns:
1. All orgs from user config (if loaded)
2. Plus all orgs from global config (no duplicates)

User orgs take precedence over global orgs.

## Token Storage

### Per-User Keyring Service

**Service Name**: `sprites-cli:<userID>`

**Keys Stored**:
- `fly-encryption-key:<userID>` → AES encryption key for Fly token
- `sprites:org:<orgName>` → Sprite org token

**Example** (User ID: user123):
```
Keyring Service: sprites-cli:user123
├─ fly-encryption-key:user123 → [AES key]
├─ sprites:org:org-alpha      → [Sprite token]
└─ sprites:org:org-beta       → [Sprite token]
```

### Encrypted Fly Tokens

**Location**: `~/.sprites/users/<userID>-<hash>.token.enc`

**Encryption**: AES-256-GCM with envelope encryption

**Key Storage**: Keyring service `sprites-cli:<userID>` / Key `fly-encryption-key:<userID>`

## Multi-User Example

### Scenario

Two users on the same machine:
- Alice (ID: alice123)
- Bob (ID: bob456)

### File Structure

```
~/.sprites/
├── sprites.json                      # Global config
│   └── users: [alice, bob]
│   └── current_user: "alice123"
│
├── users/
│   ├── alice123-a1b2c3d4e5f6a7b8.json   # Alice's orgs
│   └── bob456-9f8e7d6c5b4a3210.json     # Bob's orgs
│
└── users/
    ├── alice123-a1b2c3d4e5f6a7b8.enc    # Alice's Fly token
    └── bob456-9f8e7d6c5b4a3210.enc      # Bob's Fly token
```

### Keyring Structure

```
Keyring Service: sprites-cli:alice123
├─ fly-encryption-key:alice123 → [Alice's AES key]
├─ sprites:org:alice-org            → [Alice's sprite token]
└─ sprites:org:shared-org           → [Alice's sprite token]

Keyring Service: sprites-cli:bob456
├─ fly-encryption-key:bob456   → [Bob's AES key]
├─ sprites:org:bob-org              → [Bob's sprite token]
└─ sprites:org:shared-org           → [Bob's sprite token]
```

**Note**: Both users can have tokens for "shared-org", but they're isolated in separate keyring services.

## Benefits

### 1. **Complete User Isolation**
- Each user has their own config file
- Each user has their own keyring service
- No user data overlap

### 2. **Flexible Organization Access**
- User-specific orgs
- Global shared orgs
- User orgs override global orgs

### 3. **Simple Schema**
- Same v1 config format everywhere
- No complex nested structures
- Easy to understand and debug

### 4. **Case-Safe Filenames**
- Works on macOS (case-insensitive)
- Works on Linux (case-sensitive)
- Works on Windows (case-insensitive)

### 5. **Clean Separation**
- Global config: User list, current user, global orgs
- User config: User's personal orgs
- No config file bloat

## Implementation Details

### Manager Fields

```go
type Manager struct {
    configPath    string      // Path to global config
    config        *v1.Config  // Global config
    userConfig    *v1.Config  // Current user's config
    currentUserID string      // Cached current user ID
}
```

### Resolution Logic

Every `Get*` method follows this pattern:

```go
// 1. Check user config first
if m.userConfig != nil {
    if found in m.userConfig.URLs {
        return found
    }
}

// 2. Fall back to global config
if found in m.config.URLs {
    return found
}

// 3. Return not found
return error
```

### Save Logic

```go
func (m *Manager) Save() error {
    // Save global config
    save(m.config)
    
    // Also save user config if loaded
    if m.userConfig != nil {
        save(userConfig)
    }
}
```

## Migration

### From V0/V1 to Current

When migrating:
1. Global config stays as-is (v1 format)
2. No user configs created automatically
3. Users log in to create their config files

### User Login Flow

```
1. User runs: sprite login
2. System authenticates with Fly.io
3. System creates user entry in global config
4. System creates ~/.sprites/users/<userID>-<hash>.json
5. System adds org to user config
6. System stores token in user keyring
```

## Testing

All existing tests work with the new system:
- ✅ Global config operations
- ✅ User management
- ✅ User-scoped keyring
- ✅ Organization resolution
- ✅ Multi-user isolation

## Summary

This architecture provides:
- ✅ Clean separation of global and user-specific config
- ✅ Same simple v1 schema for all config files
- ✅ User config first, global fallback
- ✅ Complete user isolation
- ✅ Case-safe filenames
- ✅ No config file bloat
- ✅ Easy to understand and debug

The system is production-ready and all tests pass!

