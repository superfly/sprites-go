# Envelope Encryption for Fly.io Tokens

## Overview

Fly.io tokens (especially macaroons) can be very large (2KB-10KB+), exceeding system keyring limits. We use **envelope encryption** to securely store these large tokens.

## Architecture

### What is Envelope Encryption?

Envelope encryption is a two-layer encryption approach:

1. **Data Encryption**: The actual data (Fly token) is encrypted with a strong symmetric key (AES-256-GCM)
2. **Key Encryption**: The encryption key itself is stored in a secure keyring

This allows us to:
- Store arbitrarily large tokens on disk (encrypted)
- Keep only the small encryption key in the keyring
- Maintain strong security through OS-level key protection

## Implementation Details

### Cryptographic Specifications

- **Algorithm**: AES-256-GCM (Galois/Counter Mode)
- **Key Size**: 256 bits (32 bytes)
- **Nonce**: 12 bytes (standard GCM nonce size)
- **Authentication**: GCM provides both encryption and authentication

### Storage Locations

```
User's System:
├─ System Keyring
│  └─ Service: sprites-cli:userID
│     └─ Key: fly-encryption-key:userID
│        └─ Value: <base64-encoded 32-byte AES key>
│
└─ Filesystem: ~/.sprites/fly-auth/
   └─ <userID>-<hash>.enc
      └─ Encrypted token file (secure permissions: 0600)
      └─ Hash: SHA-256(userID), lowercase hex, 16 chars
      └─ Safe for case-insensitive filesystems
```

### File Structure

Each encrypted token file contains:
```
[Nonce (12 bytes)] + [Ciphertext + Auth Tag]
```

The nonce is prepended to the ciphertext for easy retrieval during decryption.

### Filename Format

**Format**: `<userID>-<hash>.enc`

**Example**: `NRbGVLQ8alN5-a1b2c3d4e5f6a7b8.enc`

**Hash Generation**:
- SHA-256 hash of the userID
- Converted to lowercase hexadecimal
- Truncated to 16 characters
- Only contains [0-9a-f] - safe for all filesystems

**Why This Format?**
- **Case-Insensitive FS Safety**: macOS (APFS) and Windows (NTFS) use case-insensitive filesystems by default
- **Collision Avoidance**: Different case userIDs (e.g., "UserABC" vs "userabc") get different filenames
- **Deterministic**: Same userID always produces the same hash
- **Readability**: UserID is visible in filename for debugging
- **Uniqueness**: Hash ensures no collisions on case-insensitive systems

## Security Properties

### Confidentiality
- Tokens are encrypted with AES-256-GCM
- Encryption keys are stored in OS keyring (encrypted at rest)
- Files have restrictive permissions (0600 - owner read/write only)
- Directory has restrictive permissions (0700 - owner rwx only)

### Integrity
- GCM mode provides authenticated encryption
- Any tampering with the encrypted file will be detected
- Decryption fails if ciphertext is modified

### Key Management
- Each user has a unique encryption key
- Keys are randomly generated using `crypto/rand`
- Keys are never written to disk in plaintext
- Keys are automatically generated on first use

## User Workflow

### Login Process

```
┌─────────────────────────────────────────────────────────────┐
│                    Login Process                             │
└─────────────────────────────────────────────────────────────┘

1. User runs: sprite login

2. System reads Fly token from ~/.fly/config.yml
   ├─ If not found → Run web login flow
   └─ If found → Use existing token

3. Get user info from Fly API
   └─ Returns: userID, email

4. Envelope Encryption Process:
   ┌────────────────────────────────────┐
   │ a. Get/Create encryption key       │
   │    - Check keyring for existing    │
   │    - If none, generate random key  │
   │    - Store in keyring              │
   └────────────────────────────────────┘
   ┌────────────────────────────────────┐
   │ b. Encrypt Fly token               │
   │    - Use AES-256-GCM               │
   │    - Generate random nonce         │
   │    - Encrypt token                 │
   └────────────────────────────────────┘
   ┌────────────────────────────────────┐
   │ c. Store encrypted file            │
   │    - Write to ~/.sprites/fly-auth/ │
   │    - Filename: <userID>.enc        │
   │    - Permissions: 0600             │
   └────────────────────────────────────┘

5. Continue with Sprite token creation...
```

### Token Retrieval Process

```
┌─────────────────────────────────────────────────────────────┐
│                Token Retrieval Process                       │
└─────────────────────────────────────────────────────────────┘

1. Application needs Fly token for userID

2. Retrieve encryption key from keyring
   └─ Service: sprites-cli:userID
   └─ Key: fly-encryption-key:userID

3. Read encrypted file
   └─ Path: ~/.sprites/fly-auth/<userID>-<hash>.enc

4. Decrypt token
   ┌────────────────────────────────────┐
   │ a. Extract nonce from file         │
   │ b. Extract ciphertext              │
   │ c. Decrypt using AES-256-GCM       │
   │ d. Verify authentication tag       │
   └────────────────────────────────────┘

5. Return plaintext Fly token
```

### Logout Process

```
┌─────────────────────────────────────────────────────────────┐
│                    Logout Process                            │
└─────────────────────────────────────────────────────────────┘

1. User runs: sprite logout

2. Get user info

3. Delete encrypted Fly token
   └─ Remove: ~/.sprites/fly-auth/<userID>-<hash>.enc

4. Delete encryption key
   └─ Remove from keyring: sprites-cli:userID / fly-encryption-key:userID

5. Delete Sprite tokens
   └─ Remove all: sprites-cli:userID / sprite:*

6. Remove user from config
```

## Multi-User Support

Each user has completely isolated storage:

### User Alice (ID: alice123)
```
Keyring:
  Service: sprites-cli:alice123
  ├─ fly-encryption-key:alice123 → <Alice's AES key>
  ├─ sprite:org-alpha            → <Alice's sprite token>
  └─ sprite:org-beta             → <Alice's sprite token>

Filesystem:
  ~/.sprites/fly-auth/alice123-a1b2c3d4e5f6a7b8.enc → <Alice's encrypted Fly token>
```

### User Bob (ID: bob456)
```
Keyring:
  Service: sprites-cli:bob456
  ├─ fly-encryption-key:bob456 → <Bob's AES key>
  ├─ sprite:org-alpha          → <Bob's sprite token>
  └─ sprite:org-gamma          → <Bob's sprite token>

Filesystem:
  ~/.sprites/fly-auth/bob456-9f8e7d6c5b4a3210.enc → <Bob's encrypted Fly token>
```

## Token Size Comparison

### Before (Attempted Keyring Storage)

| Token Type | Size | Keyring Limit | Result |
|------------|------|---------------|--------|
| Regular Fly Token | 200-500 bytes | 2-4KB | ✅ Fits |
| Single Macaroon | 1-2KB | 2-4KB | ⚠️ Tight fit |
| Multiple Macaroons | 5-10KB+ | 2-4KB | ❌ **Too large!** |

**Error**: `data passed to Set was too big`

### After (Envelope Encryption)

| Item | Size | Storage | Result |
|------|------|---------|--------|
| Fly Token (any size) | Unlimited | Encrypted file | ✅ Works |
| Encryption Key | 32 bytes (base64: ~44 chars) | Keyring | ✅ Tiny! |
| Sprite Tokens | ~500 bytes each | Keyring | ✅ Fits easily |

## Code Examples

### Storing a Fly Token

```go
import "github.com/superfly/sprite-env/client/fly"

userID := "user123"
flyToken := "FlyV1_fm1r_very_long_macaroon_token..."

err := fly.StoreFlyTokenEncrypted(userID, flyToken)
if err != nil {
    log.Fatalf("Failed to store token: %v", err)
}
```

### Reading a Fly Token

```go
import "github.com/superfly/sprite-env/client/fly"

userID := "user123"

token, err := fly.ReadFlyTokenEncrypted(userID)
if err != nil {
    log.Fatalf("Failed to read token: %v", err)
}

// Use token for Fly API calls
user, err := fly.GetCurrentUser(ctx, token)
```

### Deleting a User's Tokens

```go
import "github.com/superfly/sprite-env/client/fly"

userID := "user123"

// This deletes both the encrypted file and the encryption key
err := fly.DeleteFlyTokenEncrypted(userID)
if err != nil {
    log.Printf("Warning: Failed to delete token: %v", err)
}
```

## Security Considerations

### Threat Model

**What We Protect Against:**
- ✅ Unauthorized file access (file permissions: 0600)
- ✅ Token theft from disk (tokens are encrypted)
- ✅ Token modification (GCM authentication)
- ✅ Cross-user token access (user-scoped keys)
- ✅ Keyring size limits (only key in keyring)

**What We Don't Protect Against:**
- ❌ Root/admin access to system
- ❌ Memory dumps while token is in use
- ❌ Malware running as the same user
- ❌ Physical access to unlocked keyring

### Why This is Secure

1. **Encryption at Rest**: Tokens never stored in plaintext
2. **OS Keyring Security**: Encryption keys protected by OS
3. **Key Isolation**: Each user has unique encryption key
4. **File Permissions**: Unix permissions prevent cross-user access
5. **Authenticated Encryption**: GCM detects tampering
6. **No Key Derivation**: Keys are random, not derived from passwords

### Comparison to ~/.fly/config.yml

| Feature | ~/.fly/config.yml | Envelope Encryption |
|---------|-------------------|---------------------|
| Encryption | ❌ Plaintext YAML | ✅ AES-256-GCM |
| File Permissions | ⚠️ 0600 (if set) | ✅ 0600 (enforced) |
| Key Storage | N/A | ✅ OS Keyring |
| User Isolation | ❌ Shared file | ✅ Separate keys |
| Tampering Detection | ❌ None | ✅ GCM Auth Tag |
| Size Limit | ✅ Unlimited | ✅ Unlimited |

## Performance

Encryption/decryption is extremely fast:
- **Encryption**: ~0.1ms for 10KB token
- **Decryption**: ~0.1ms for 10KB token
- **Key Generation**: ~0.01ms (done once)

The performance impact is negligible compared to network operations.

## Backup and Recovery

### Key Loss Scenarios

If a user loses their encryption key (e.g., keyring cleared):
1. Encrypted token file becomes unreadable
2. User must re-authenticate with Fly.io
3. New key is generated automatically
4. New token is stored with new key

### Migration from Old Storage

The system automatically falls back to reading from `~/.fly/config.yml` if:
1. No encrypted token file exists
2. User hasn't logged in with new system yet

This provides seamless migration for existing users.

## Future Enhancements

Possible improvements:
- [ ] Key rotation support
- [ ] Backup key storage
- [ ] Hardware security module (HSM) integration
- [ ] Automatic token refresh
- [ ] Multi-device sync (with end-to-end encryption)

## References

- [NIST SP 800-38D: GCM Specification](https://csrc.nist.gov/publications/detail/sp/800-38d/final)
- [RFC 5084: Using AES-GCM](https://tools.ietf.org/html/rfc5084)
- [Go crypto/cipher Package](https://pkg.go.dev/crypto/cipher)
- [Envelope Encryption Best Practices](https://cloud.google.com/kms/docs/envelope-encryption)

