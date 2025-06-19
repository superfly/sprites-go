# flyio/app-storage

A Docker image for a high-performance, durable storage solution using JuiceFS with S3 backend and Litestream for SQLite replication.

## Description

This container image provides a complete storage solution that:
- Uses JuiceFS for filesystem operations
- Stores data in an S3-compatible backend
- Uses SQLite for metadata
- Replicates the SQLite database with Litestream for durability

## Required Environment Variables

The following environment variables **MUST** be set for the container to function:

| Variable | Description |
|----------|-------------|
| `S3_ACCESS_KEY` | S3 access key for storage access |
| `S3_SECRET_KEY` | S3 secret key for storage access |
| `S3_ENDPOINT` | S3 endpoint URL (without https:// prefix) |
| `BUCKET_NAME` | S3 bucket name for storage |
| `S3_REGION` | S3 region (if applicable) |

## Optional Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `META_URL` | SQLite database path for JuiceFS metadata | `sqlite3://dev/fly_vol/juicefs.db` |
| `MOUNT_POINT` | Where JuiceFS will be mounted | `/data` |
| `CACHE_DIR` | Directory for JuiceFS cache | `/dev/fly_vol/cache` |

## Requirements

### FUSE Access

**Important:** This container **requires FUSE privileges** to function properly. When running the container, you must:

1. Add the `--privileged` flag OR
2. Add `--device /dev/fuse --cap-add SYS_ADMIN` flags

### Example Docker Run Command

```bash
docker run -d \
  --name app-storage \
  --device /dev/fuse \
  --cap-add SYS_ADMIN \
  -e S3_ACCESS_KEY=your_access_key \
  -e S3_SECRET_KEY=your_secret_key \
  -e S3_ENDPOINT=your.s3.endpoint.com \
  -e BUCKET_NAME=your-bucket-name \
  -e S3_REGION=your-region \
  flyio/app-storage:latest
```

### Example Docker Compose

```yaml
version: '3'
services:
  storage:
    image: flyio/app-storage:latest
    privileged: true  # For FUSE access
    environment:
      - S3_ACCESS_KEY=your_access_key
      - S3_SECRET_KEY=your_secret_key
      - S3_ENDPOINT=your.s3.endpoint.com
      - BUCKET_NAME=your-bucket-name
      - S3_REGION=your-region
    volumes:
      - ./persistent_vol:/dev/fly_vol  # For caching and metadata persistence
```

## Usage

Once running, the container will:
1. Check for required environment variables
2. Restore the SQLite database from object storage if available
3. Format a JuiceFS filesystem if one doesn't exist
4. Mount the filesystem at the specified mount point (default: `/data`)
5. Begin replicating the SQLite database with Litestream

## Troubleshooting

If you encounter issues:

1. Check if all required environment variables are properly set
2. Ensure the container has proper FUSE privileges
3. Verify S3 credentials and endpoint are correct
4. Check container logs for specific error messages

## License

MIT 