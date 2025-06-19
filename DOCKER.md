# Docker Images for sprite-env

This document describes how to use the pre-built Docker images for sprite-env from the GitHub Container Registry.

## Available Images

Multi-architecture Docker images are available for both `linux/amd64` and `linux/arm64` platforms. Docker will automatically pull the correct image for your architecture.

### Image Location

The images are hosted on GitHub Container Registry at:
```
ghcr.io/[owner]/[repository]
```

Replace `[owner]/[repository]` with the actual GitHub repository path.

## Pulling Images

### Latest version
```bash
docker pull ghcr.io/[owner]/[repository]:latest
```

### Specific version
```bash
docker pull ghcr.io/[owner]/[repository]:v1.0.0
```

## Running the Container

### Basic usage
```bash
docker run --rm ghcr.io/[owner]/[repository]:latest
```

### With configuration file
```bash
docker run --rm \
  -v $(pwd)/config.json:/app/config.json \
  ghcr.io/[owner]/[repository]:latest \
  --config /app/config.json
```

### With port mapping
```bash
docker run --rm \
  -p 8080:8080 \
  ghcr.io/[owner]/[repository]:latest
```

### Complete example with all options
```bash
docker run -d \
  --name sprite-env \
  -p 8080:8080 \
  -v $(pwd)/config.json:/app/config.json \
  -v $(pwd)/data:/app/data \
  --restart unless-stopped \
  ghcr.io/[owner]/[repository]:latest \
  --config /app/config.json
```

## Docker Compose

Create a `docker-compose.yml` file:

```yaml
version: '3.8'

services:
  sprite-env:
    image: ghcr.io/[owner]/[repository]:latest
    container_name: sprite-env
    ports:
      - "8080:8080"
    volumes:
      - ./config.json:/app/config.json
      - ./data:/app/data
    restart: unless-stopped
    command: ["--config", "/app/config.json"]
```

Then run:
```bash
docker-compose up -d
```

## Building Images Locally

If you want to build the images locally:

### For current architecture
```bash
cd server
docker build -t sprite-env:local .
```

### For multiple architectures (requires Docker Buildx)
```bash
cd server
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -t sprite-env:local \
  .
```

## Security Notes

- The container runs as a non-root user (UID 1000) for security
- Only necessary files are included in the image
- The base image is Alpine Linux for minimal attack surface

## Troubleshooting

### Permission issues
If you encounter permission issues with mounted volumes, ensure the files are readable by UID 1000:
```bash
chown -R 1000:1000 ./config.json ./data
```

### Architecture compatibility
To check which architectures are available for an image:
```bash
docker manifest inspect ghcr.io/[owner]/[repository]:latest
```

## GitHub Actions Workflow

The Docker images are built and published using GitHub Actions. To manually trigger a build:

1. Go to the Actions tab in the GitHub repository
2. Select "Docker Publish" workflow
3. Click "Run workflow"
4. Enter the version tag (default: latest)
5. Click "Run workflow"

The workflow will build multi-architecture images and push them to the GitHub Container Registry.