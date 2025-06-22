# syntax=docker/dockerfile:1

# Build stage for AMD64
FROM --platform=linux/amd64 golang:1.24-alpine AS builder-amd64
RUN apk add --no-cache git
WORKDIR /build

# Copy go.work files first
COPY go.work go.work.sum ./

# Copy all go.mod files from each module
COPY server/go.mod server/go.sum* ./server/
COPY lib/go.mod lib/go.sum* ./lib/
COPY client/go.mod client/go.sum* ./client/
COPY packages/juicefs/go.mod packages/juicefs/go.sum* ./packages/juicefs/
COPY packages/supervisor/go.mod packages/supervisor/go.sum* ./packages/supervisor/

# Download dependencies for all modules in the workspace
RUN go mod download -x

# Copy all source code
COPY . .

ARG VERSION=dev
RUN cd server && \
    CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -ldflags="-w -s -X main.version=${VERSION}" \
    -o ../spritectl .

# Build stage for ARM64
FROM --platform=linux/arm64 golang:1.24-alpine AS builder-arm64
RUN apk add --no-cache git
WORKDIR /build

# Copy go.work files first
COPY go.work go.work.sum ./

# Copy all go.mod files from each module
COPY server/go.mod server/go.sum* ./server/
COPY lib/go.mod lib/go.sum* ./lib/
COPY client/go.mod client/go.sum* ./client/
COPY packages/juicefs/go.mod packages/juicefs/go.sum* ./packages/juicefs/
COPY packages/supervisor/go.mod packages/supervisor/go.sum* ./packages/supervisor/

# Download dependencies for all modules in the workspace
RUN go mod download -x

# Copy all source code
COPY . .

ARG VERSION=dev
RUN cd server && \
    CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build \
    -ldflags="-w -s -X main.version=${VERSION}" \
    -o ../spritectl .

# Download crun binary
FROM alpine:latest AS crun
RUN apk add --no-cache curl
RUN curl -L https://github.com/containers/crun/releases/download/1.21/crun-1.21-linux-amd64 -o /crun && \
    chmod +x /crun

# Get litestream binary
FROM litestream/litestream:latest AS litestream

# Final stage - based on juicedata/mount which includes juicefs
FROM juicedata/mount:latest

RUN apt-get update && \
    apt-get install -y sqlite3 bash e2fsprogs fio jq nano coreutils \
    # Tools for dm-cache and storage management
    lvm2 thin-provisioning-tools \
    # Tools for DRBD
    drbd-utils \
    # Additional useful tools for disk management
    parted gdisk util-linux fdisk xfsprogs \
    # Cleanup
    && apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Copy binaries from other stages
COPY --from=crun /crun /usr/local/bin/crun
COPY --from=litestream /usr/local/bin/litestream /usr/local/bin/litestream

# Copy the appropriate binary based on target platform
ARG TARGETPLATFORM
COPY --from=builder-amd64 /build/spritectl /usr/local/bin/spritectl.amd64
COPY --from=builder-arm64 /build/spritectl /usr/local/bin/spritectl.arm64
RUN if [ "$TARGETPLATFORM" = "linux/amd64" ]; then \
        mv /usr/local/bin/spritectl.amd64 /usr/local/bin/spritectl && rm -f /usr/local/bin/spritectl.arm64; \
    else \
        mv /usr/local/bin/spritectl.arm64 /usr/local/bin/spritectl && rm -f /usr/local/bin/spritectl.amd64; \
    fi

# Define environment variables for paths
ENV SPRITE_WRITE_DIR=/dev/fly_vol \
    SPRITE_HOME=/home/sprite

# Set working directory for spritectl components
WORKDIR ${SPRITE_HOME}

# Copy all base-env contents into the working directory
COPY base-env/ ./

# Set working directory to the writable volume
WORKDIR ${SPRITE_WRITE_DIR}

# Expose the API port
EXPOSE 7778

RUN which juicefs
# Use spritectl as entrypoint with config file
# /usr/local/bin/spritectl -config /home/sprite/config.json -listen 0.0.0.0:7778
ENTRYPOINT ["/usr/local/bin/spritectl", "-config", "/home/sprite/config.json", "-listen", "0.0.0.0:7778"] 