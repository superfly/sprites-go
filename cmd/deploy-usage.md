# Deploy Command Usage

The deploy command builds and deploys sprite-env to Fly.io machines.

## Basic Usage

```bash
# Deploy the main application
cd cmd
go run deploy.go -a your-app-name

# Skip building and just update the machine
go run deploy.go -a your-app-name --skip-build

# Replace entire machine config (not just image)
go run deploy.go -a your-app-name --replace-config
```

## Update Base Images

The `--update-base` flag builds and pushes the base Ubuntu and languages images that are mounted as volumes in the container:

```bash
# Build and deploy main app + base images
go run deploy.go -a your-app-name --update-base
```

This will:
1. Build and push the main application image as `registry.fly.io/your-app:TIMESTAMP`
2. Build and push the Ubuntu base image as `registry.fly.io/your-app:TIMESTAMP-ubuntu`
3. Build and push the languages image as `registry.fly.io/your-app:TIMESTAMP-languages`
4. Update the machine config to use these images in the volumes:
   - `system-base` volume → uses the `-ubuntu` image
   - `languages-image` volume → uses the `-languages` image

## Environment Variables

- `FLY_APP_NAME`: Alternative to `-a` flag
- `FLY_API_TOKEN`: Authentication token (retrieved from flyctl if not set)
- `SPRITE_HTTP_API_TOKEN`: Required for the sprite service

## Example Workflow

```bash
# First deployment with base images
export FLY_APP_NAME=my-sprite-app
export SPRITE_HTTP_API_TOKEN=my-secret-token
go run deploy.go --update-base

# Subsequent deployments (only update main app)
go run deploy.go

# Update only base images without changing config
go run deploy.go --update-base --skip-build
```
