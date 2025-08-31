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

# Copy go.mod files
COPY go.mod go.sum* ./
COPY cmd/go.mod cmd/go.sum* ./cmd/

# Download dependencies
RUN go mod download -x && cd cmd && go mod download -x

# Copy all source code
COPY . .

FROM builder as builder-server

ARG VERSION=dev
RUN cd server && \
    CGO_ENABLED=1 GOOS=linux go build \
    -ldflags="-w -s -X main.version=${VERSION} -extldflags '-static'" \
    -tags 'netgo osusergo' \
    -o ../spritectl .


FROM builder as builder-client

ARG VERSION=dev
# Also build the client
RUN cd client && \
    CGO_ENABLED=0 GOOS=linux go build \
    -ldflags="-w -s" \
    -o ../sprite .


# Download crun binary
FROM alpine:latest AS crun
ARG TARGETARCH
RUN apk add --no-cache curl
# Map Docker's TARGETARCH to crun's naming convention
RUN case ${TARGETARCH} in \
        amd64) CRUN_ARCH="amd64" ;; \
        arm64) CRUN_ARCH="aarch64" ;; \
        *) echo "Unsupported architecture: ${TARGETARCH}" && exit 1 ;; \
    esac && \
    curl -L https://github.com/containers/crun/releases/download/1.21/crun-1.21-linux-${CRUN_ARCH}-disable-systemd -o /crun && \
    chmod +x /crun

# Get litestream binary
FROM litestream/litestream:latest AS litestream

FROM ghcr.io/superfly/juicefs:748b889 as juicefs

# ---- build stage for statically linked tmux ----
FROM alpine:3.20 AS utility-builder

RUN apk add --no-cache \
      build-base \
      musl-dev \
      ncurses-static \
      ncurses-dev \
      libevent-static \
      libevent-dev \
      git \
      autoconf \
      automake \
      pkgconfig \
      bison

WORKDIR /src

# Fetch tmux source
RUN git clone --depth 1 --branch 3.5a https://github.com/tmux/tmux.git .

# Bootstrap & configure
RUN sh autogen.sh && \
    ./configure LDFLAGS="-static" CFLAGS="-O2" && \
    make -j$(nproc)

# Create the sprite bin directory and copy tmux
RUN mkdir -p /.sprite/bin && \
    cp tmux /.sprite/bin/

# Final stage - based on juicedata/mount which includes juicefs
FROM ubuntu:25.04

RUN apt-get update && \
    apt-get install -y sqlite3 bash e2fsprogs fio jq nano coreutils \
    # Tools for dm-cache and storage management
    lvm2 thin-provisioning-tools \
    # Tools for DRBD
    drbd-utils \
    # Additional useful tools for disk management
    parted gdisk util-linux fdisk xfsprogs fuse3 curl iproute2 nftables iputils-ping vim rsync \
    # Cleanup
    && apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Copy binaries from other stages
COPY --from=crun /crun /usr/local/bin/crun
COPY --from=litestream /usr/local/bin/litestream /usr/local/bin/litestream
COPY --from=juicefs /usr/local/bin/juicefs /usr/local/bin/juicefs

# Copy statically linked tmux
COPY --from=utility-builder /.sprite/bin/ /.sprite/bin/

# Define environment variables for paths
ENV SPRITE_WRITE_DIR=/dev/fly_vol \
    SPRITE_HOME=/home/sprite

# Copy the appropriate binaries based on target platform
COPY --from=builder-server /build/spritectl /usr/local/bin/spritectl
COPY --from=builder-client /build/sprite /usr/local/bin/sprite

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
ENTRYPOINT ["/usr/local/bin/spritectl", "-config", "/home/sprite/config.json", "-listen", "0.0.0.0:7778", "-debug"] 

# juicefs mount --no-usage-report -o writeback_cache -o fsname=SpriteFS --writeback --upload-delay=1m --cache-dir=/dev/fly_vol/  --no-syslog --cache-size=8192 --buffer-size=819  sqlite3://dev/fly_vol/juicefs/metadata.db /data
