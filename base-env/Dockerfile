# Download crun binary
FROM alpine:latest AS crun
RUN apk add --no-cache curl
RUN curl -L https://github.com/containers/crun/releases/download/1.21/crun-1.21-linux-amd64 -o /crun && \
    chmod +x /crun

FROM litestream/litestream:latest AS litestream
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

# Copy crun binary to final image
COPY --from=crun /crun /usr/local/bin/crun

COPY --from=litestream /usr/local/bin/litestream /usr/local/bin/litestream
COPY config/litestream.yml /etc/litestream.yml

# Copy mount script
COPY scripts/* /usr/local/bin/
RUN chmod +x /usr/local/bin/*.sh

# Set working directory
WORKDIR /

# Default command will be overridden by Fly machine config
CMD ["/usr/local/bin/mount.sh"] 