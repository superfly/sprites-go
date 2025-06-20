# syntax=docker/dockerfile:1

# Build stage for AMD64
FROM --platform=linux/amd64 golang:1.24-alpine AS builder-amd64
RUN apk add --no-cache git
WORKDIR /build
COPY server/go.mod server/go.sum ./
RUN go mod download
COPY server/. .
ARG VERSION=dev
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -ldflags="-w -s -X main.version=${VERSION}" \
    -o sprite-env .

# Build stage for ARM64
FROM --platform=linux/arm64 golang:1.24-alpine AS builder-arm64
RUN apk add --no-cache git
WORKDIR /build
COPY server/go.mod server/go.sum ./
RUN go mod download
COPY server/. .
ARG VERSION=dev
RUN CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build \
    -ldflags="-w -s -X main.version=${VERSION}" \
    -o sprite-env .

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
COPY --from=builder-amd64 /build/sprite-env /usr/local/bin/sprite-env.amd64
COPY --from=builder-arm64 /build/sprite-env /usr/local/bin/sprite-env.arm64
RUN if [ "$TARGETPLATFORM" = "linux/amd64" ]; then \
        mv /usr/local/bin/sprite-env.amd64 /usr/local/bin/sprite-env && rm -f /usr/local/bin/sprite-env.arm64; \
    else \
        mv /usr/local/bin/sprite-env.arm64 /usr/local/bin/sprite-env && rm -f /usr/local/bin/sprite-env.amd64; \
    fi

# Define environment variables for paths
ENV SPRITE_WRITE_DIR=/dev/fly_vol \
    SPRITE_HOME=/home/sprite

# Set working directory for sprite-env components
WORKDIR ${SPRITE_HOME}

# Copy all base-env contents into the working directory
COPY base-env/ ./

# Set working directory to the writable volume
WORKDIR ${SPRITE_WRITE_DIR}

# Expose the API port
EXPOSE 7778

# Use sprite-env as entrypoint with config file
# /usr/local/bin/sprite-env -config /home/sprite/config.json -listen 0.0.0.0:7778
ENTRYPOINT ["/usr/local/bin/sprite-env", "-config", "/home/sprite/config.json", "-listen", "0.0.0.0:7778"] 