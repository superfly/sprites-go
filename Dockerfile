# syntax=docker/dockerfile:1

# Build stage for AMD64
FROM golang:1.24-bookworm AS builder
ENV CGO_ENABLED=1

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive \
    apt-get install --no-install-recommends --assume-yes \
      build-essential \
      libsqlite3-dev
WORKDIR /build

# Copy go.work files first
COPY go.work go.work.sum ./

# Copy all go.mod files from each module
COPY server/go.mod server/go.sum* ./server/
COPY lib/go.mod lib/go.sum* ./lib/
COPY client/go.mod client/go.sum* ./client/
COPY packages/container/go.mod packages/container/go.sum* ./packages/container/
COPY packages/juicefs/go.mod packages/juicefs/go.sum* ./packages/juicefs/
COPY packages/supervisor/go.mod packages/supervisor/go.sum* ./packages/supervisor/
COPY packages/wsexec/go.mod packages/wsexec/go.sum* ./packages/wsexec/
COPY packages/leaser/go.mod packages/leaser/go.sum* ./packages/leaser/
COPY packages/api-docs/go.mod packages/api-docs/go.sum* ./packages/api-docs/
COPY pkg/terminal/go.mod pkg/terminal/go.sum* ./pkg/terminal/
COPY packages/port-watcher/go.mod packages/port-watcher/go.sum* ./packages/port-watcher/

# Download dependencies for all modules in the workspace
RUN go mod download -x

# Copy all source code
COPY . .

ARG VERSION=dev
RUN cd server && \
    CGO_ENABLED=1 GOOS=linux go build \
    -ldflags="-w -s -X main.version=${VERSION} -extldflags '-static'" \
    -tags 'netgo osusergo' \
    -o ../spritectl .

# Also build the client
RUN cd client && \
    CGO_ENABLED=0 GOOS=linux go build \
    -ldflags="-w -s" \
    -o ../sprite .


# Download crun binary
FROM alpine:latest AS crun
RUN apk add --no-cache curl
RUN curl -L https://github.com/containers/crun/releases/download/1.21/crun-1.21-linux-amd64-disable-systemd -o /crun && \
    chmod +x /crun

# Get litestream binary
FROM litestream/litestream:latest AS litestream

FROM ghcr.io/superfly/juicefs:fname as juicefs

# Final stage - based on juicedata/mount which includes juicefs
FROM ubuntu:25.04

RUN apt-get update && \
    apt-get install -y sqlite3 bash e2fsprogs fio jq nano coreutils \
    # Tools for dm-cache and storage management
    lvm2 thin-provisioning-tools \
    # Tools for DRBD
    drbd-utils \
    # Additional useful tools for disk management
    parted gdisk util-linux fdisk xfsprogs fuse3 \
    # Cleanup
    && apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Copy binaries from other stages
COPY --from=crun /crun /usr/local/bin/crun
COPY --from=litestream /usr/local/bin/litestream /usr/local/bin/litestream
COPY --from=juicefs /usr/local/bin/juicefs /usr/local/bin/juicefs

# Define environment variables for paths
ENV SPRITE_WRITE_DIR=/dev/fly_vol \
    SPRITE_HOME=/home/sprite

# Copy the appropriate binaries based on target platform
COPY --from=builder /build/spritectl /usr/local/bin/spritectl
COPY --from=builder /build/sprite /usr/local/bin/sprite

# Set working directory for spritectl components
WORKDIR ${SPRITE_HOME}

# Copy all base-env contents into the working directory
COPY base-env/ ./

# Set working directory to the writable volume
WORKDIR ${SPRITE_WRITE_DIR}

# Expose the API port
EXPOSE 7778

# Use spritectl as entrypoint with config file
# /usr/local/bin/spritectl -config /home/sprite/config.json -listen 0.0.0.0:7778
ENTRYPOINT ["/usr/local/bin/spritectl", "-config", "/home/sprite/config.json", "-listen", "0.0.0.0:7778"] 

# juicefs mount --no-usage-report -o writeback_cache -o fsname=SpriteFS --writeback --upload-delay=1m --cache-dir=/dev/fly_vol/  --no-syslog --cache-size=8192 --buffer-size=819  sqlite3://dev/fly_vol/juicefs/metadata.db /data
