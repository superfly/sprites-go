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

The deploy command provides separate flags for updating base images that are mounted as volumes:

### Update Ubuntu Base Image Only
```bash
go run deploy.go -a your-app-name --update-base
```
This builds and pushes the Ubuntu base image as `registry.fly.io/your-app:TIMESTAMP-ubuntu`

### Update Languages Image Only
```bash
go run deploy.go -a your-app-name --update-languages
```
This builds and pushes the languages image as `registry.fly.io/your-app:TIMESTAMP-languages`

### Update Both Base Images
```bash
go run deploy.go -a your-app-name --update-base --update-languages
```

### What These Flags Do
When using these flags (individually or together):
1. Build and push the requested images:
   - `--update-base`: Ubuntu base image from `base-env/images/ubuntu-devtools/Dockerfile`
   - `--update-languages`: Languages stage from the same Dockerfile
2. Update the machine config to use these images in the volumes:
   - `system-base` volume → uses the `-ubuntu` image (if `--update-base`)
   - `languages-image` volume → uses the `-languages` image (if `--update-languages`)
3. The main application image is built unless `--skip-build` is used

**Performance Note**: All requested images are built in parallel to minimize deployment time.

Note: The base image builds run from the `base-env/images/ubuntu-devtools/` directory to ensure the Docker context is correct for COPY operations.

## Environment Variables

- `FLY_APP_NAME`: Alternative to `-a` flag
- `FLY_API_TOKEN`: Authentication token (retrieved from flyctl if not set)
- `SPRITE_HTTP_API_TOKEN`: Required for the sprite service

## Example Workflow

```bash
# First deployment with all images
export FLY_APP_NAME=my-sprite-app
export SPRITE_HTTP_API_TOKEN=my-secret-token
go run deploy.go --update-base --update-languages

# Update only the main application
go run deploy.go

# Update only the Ubuntu base image
go run deploy.go --update-base --skip-build

# Update only the languages image
go run deploy.go --update-languages --skip-build

# Update both base images but not the main app
go run deploy.go --update-base --update-languages --skip-build

# Update everything
go run deploy.go --update-base --update-languages
```
