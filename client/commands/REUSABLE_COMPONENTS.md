# Reusable Authentication Components

## Overview

These components provide consistent authentication and organization selection across all commands.

## Components

### 1. `EnsureAuthenticated(ctx, orgOverride)` → (org, client, error)

**Purpose**: Ensures user is authenticated and returns org + configured client

**Flow**:
1. Checks if user is already authenticated
2. If not authenticated OR orgOverride is provided:
   - Runs login flow
   - Shows org selector
   - Stores credentials
3. Returns selected org and configured Sprites client

**Usage**:
```go
org, client, err := EnsureAuthenticated(ctx, ctx.OrgOverride)
if err != nil {
    return err
}
// Now you have authenticated org and client ready to use
```

**When to Use**:
- Commands that need an authenticated org and client
- Handles both first-time auth and re-auth scenarios
- Automatically handles org selection

### 2. `SelectOrganization(ctx)` → (org, client, error)

**Purpose**: Full authentication flow with org selection

**Flow**:
1. Gets/creates Fly token (web login if needed)
2. Gets user info from Fly API
3. Stores encrypted Fly token
4. Fetches organizations from Fly
5. Prompts user to select organization
6. Creates Sprite token for selected org
7. Stores in user-scoped keyring
8. Returns org and client

**Usage**:
```go
org, client, err := SelectOrganization(ctx)
if err != nil {
    return err
}
```

**When to Use**:
- When you explicitly want to show org selector
- First-time authentication
- Switching organizations

### 3. `PromptForSpriteName()` → (string, error)

**Purpose**: Prompts user for a sprite name

**Usage**:
```go
name, err := PromptForSpriteName()
if err != nil {
    return err
}
```

**When to Use**:
- Sprite name not provided as argument
- Interactive sprite creation

### 4. `GetOrgAndClient(ctx, orgOverride)` → (org, client, error)

**Purpose**: Gets org and client from existing config (with smart TTY-based auth)

**Behavior**:
- **With TTY** (interactive): Offers to authenticate if not found
- **Without TTY** (CI/scripts): Returns helpful error messages

**Usage**:
```go
org, client, err := GetOrgAndClient(ctx, orgOverride)
if err != nil {
    return err
}
```

**When to Use**:
- Most commands should use this
- Provides best UX (auto-prompts when interactive)
- Safe for non-interactive use (no hanging prompts)

**TTY Detection**:
- Detects if stdout is a terminal
- Interactive: Prompts "Would you like to authenticate now? (y/N)"
- Non-interactive: Returns "Run 'sprite login' to authenticate"

## Example: Sprite Create Command

```go
func CreateCommand(ctx *GlobalContext, args []string) {
    // 1. Get sprite name from args or prompt
    var spriteName string
    if len(args) == 1 {
        spriteName = args[0]
    } else {
        // 2. Prompt for sprite name if not provided
        spriteName, err = PromptForSpriteName()
        if err != nil {
            return err
        }
    }
    
    // 3. Get org and client (auto-prompts to authenticate if TTY)
    org, client, err := GetOrgAndClient(ctx, ctx.OrgOverride)
    if err != nil {
        return err  // Will have helpful message or user declined auth
    }
    
    // 4. Create the sprite
    err = CreateSpriteWithClient(client, spriteName)
    if err != nil {
        return err
    }
    
    fmt.Printf("✓ Sprite %s created!\n", spriteName)
}
```

**What happens**:
- If authenticated: Creates sprite immediately
- If not authenticated + TTY: Prompts "Would you like to authenticate now?"
  - User says yes → Login flow → Org selector → Create sprite
  - User says no → Error with helpful message
- If not authenticated + no TTY: Error "Run 'sprite login' to authenticate"

## Flow Diagrams

### EnsureAuthenticated Flow

```
┌─────────────────────────────────────────┐
│  EnsureAuthenticated(ctx, orgOverride)  │
└─────────────────────────────────────────┘
                   ↓
        ┌──────────────────────┐
        │ Has active user?     │
        └──────────────────────┘
         ↓ Yes           ↓ No
    ┌────────┐      ┌──────────┐
    │ Try to │      │  Login   │
    │ get org│      │  Flow    │
    └────────┘      └──────────┘
         ↓               ↓
    ┌────────┐      ┌──────────┐
    │Success?│      │  Show    │
    └────────┘      │Org Select│
     ↓ Yes          └──────────┘
  ┌──────┐              ↓
  │Return│         ┌──────────┐
  │org + │◄────────│ Authenticate│
  │client│         │with selected│
  └──────┘         │     org     │
                   └──────────┘
```

### SelectOrganization Flow

```
┌─────────────────────────────┐
│  SelectOrganization(ctx)    │
└─────────────────────────────┘
           ↓
    ┌──────────────┐
    │ Get Fly Token│
    │ (web login if│
    │   needed)    │
    └──────────────┘
           ↓
    ┌──────────────┐
    │  Get User    │
    │    Info      │
    └──────────────┘
           ↓
    ┌──────────────┐
    │ Store Fly    │
    │Token (encrypt│
    └──────────────┘
           ↓
    ┌──────────────┐
    │ Fetch Orgs   │
    │  from Fly    │
    └──────────────┘
           ↓
    ┌──────────────┐
    │  Prompt for  │
    │Org Selection │
    └──────────────┘
           ↓
    ┌──────────────┐
    │ Create Sprite│
    │    Token     │
    └──────────────┘
           ↓
    ┌──────────────┐
    │ Store in User│
    │Config+Keyring│
    └──────────────┘
           ↓
    ┌──────────────┐
    │ Return org + │
    │    client    │
    └──────────────┘
```

## Benefits

### 1. **Consistency**
All commands use the same authentication flow

### 2. **DRY** (Don't Repeat Yourself)
Authentication logic in one place

### 3. **Flexibility**
- Commands can require authentication
- Commands can work with/without authentication
- Easy to add authentication to new commands

### 4. **User Experience**
- Seamless login when needed
- No redundant prompts
- Clear error messages

## Usage Patterns

### Pattern 1: Require Authentication

```go
func MyCommand(ctx *GlobalContext, args []string) {
    org, client, err := EnsureAuthenticated(ctx, "")
    if err != nil {
        return err
    }
    // Use org and client
}
```

### Pattern 2: Try Existing, Fall Back to Auth

```go
func MyCommand(ctx *GlobalContext, args []string) {
    org, client, err := GetOrgAndClient(ctx, "")
    if err != nil {
        // Not authenticated, run auth flow
        org, client, err = EnsureAuthenticated(ctx, "")
        if err != nil {
            return err
        }
    }
    // Use org and client
}
```

### Pattern 3: Optional Sprite Name

```go
func MyCommand(ctx *GlobalContext, args []string) {
    var name string
    if len(args) > 0 {
        name = args[0]
    } else {
        name, err = PromptForSpriteName()
        if err != nil {
            return err
        }
    }
    // Use name
}
```

## Testing

All reusable components are testable:
- `EnsureAuthenticated` - Unit tests for auth logic
- `SelectOrganization` - Integration tests for full flow
- `PromptForSpriteName` - Can be mocked for testing

## Future Enhancements

Potential additions:
- `EnsureAuthenticatedWithSprite(ctx, orgOverride, spriteOverride)` - Also ensures sprite selection
- `PromptForOrganization(orgs)` - Generic org selector
- `RefreshToken(org)` - Token refresh helper
- `SwitchUser(userID)` - User switching helper

## Summary

These reusable components make it easy to:
- ✅ Add authentication to any command
- ✅ Provide consistent UX across commands
- ✅ Handle login flow automatically
- ✅ Reduce code duplication
- ✅ Simplify command implementation

Use `EnsureAuthenticated` as the primary entry point for most commands!

