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

These instructions assume you have Fly CLI installed and can deploy Fly apps.

1. Clone the repository and enter the directory:

   ```bash
   git clone --recurse-submodules https://github.com/superfly/sprite-env.git
   cd sprite-env
   ```

2. Create a `.envrc` file (or export environment variables) with the following
   values (replace placeholders as needed):

   ```bash
   export SPRITE_URL=https://tqbf-sprite.fly.dev
   export SPRITE_TOKEN=<your-sprite-token>
   export FLY_APP_NAME=tqbf-sprite
   export SPRITE_S3_BUCKET=tqbf-sprite-bucket
   ```

   If you use direnv, run `direnv allow` after creating `.envrc`.

3. Ensure you have created the Tigris bucket named by `$SPRITE_S3_BUCKET`.

4. Verify that `fly.toml` has the correct `app` name matching `$FLY_APP_NAME`.

5. Build the Sprite environment CLI:

   ```bash
   make build
   ```

6. Deploy the Sprite for the first time:

   ```bash
   cd tests
   make test-deploy
   ```

You are now ready to use Sprite in this directory.
