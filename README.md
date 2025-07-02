# Sprite

A code container runtime to support interactive development.

## Configuration

Sprite uses two types of configuration files:

### Global Configuration (`~/.sprites/config.json`)

Stores your organizations, authentication tokens, and available sprites:
- Organization names, URLs, and API tokens
- List of sprites per organization
- Currently selected organization and sprite

This file is automatically created and managed when you run `sprite org auth`.

### Local Context (`.sprite`)

Each directory can have a `.sprite` file that remembers the last organization and sprite used in that directory:

```json
{
  "organization": "default-1735676400",
  "sprite": "my-app"
}
```

This file is automatically created when you run sprite commands. The client will look for `.sprite` files in the current directory and parent directories to determine context.

Add `.sprite` to your `.gitignore` as it contains user-specific context.

## Quick Start