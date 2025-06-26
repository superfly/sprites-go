# Builder stage - compile OpenRC from source
FROM ubuntu:25.04 AS builder

RUN apt-get update && \
    apt-get install -y \
    build-essential \
    git \
    meson \
    ninja-build \
    pkg-config \
    libcap-dev \
    libaudit-dev \
    libpam0g-dev \
    && apt-get clean && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /build
RUN git clone https://github.com/OpenRC/openrc.git && \
    cd openrc && \
    meson setup build --prefix=/usr --sysconfdir=/etc --localstatedir=/var && \
    meson compile -C build && \
    DESTDIR=/build/openrc-install meson install -C build

# Main image
FROM ubuntu:25.04
ARG TARGETARCH

# Install dependencies and mise
RUN apt-get update && \
    apt-get install -y xz-utils vim gpg wget curl git \
    build-essential libssl-dev zlib1g-dev \
    libreadline-dev libyaml-dev libffi-dev libgdbm-dev \
    libncurses5-dev automake libtool bison pkg-config && \
    install -dm 755 /etc/apt/keyrings && \
    wget -qO - https://mise.jdx.dev/gpg-key.pub | gpg --dearmor | tee /etc/apt/keyrings/mise-archive-keyring.gpg > /dev/null && \
    echo "deb [signed-by=/etc/apt/keyrings/mise-archive-keyring.gpg arch=$(dpkg --print-architecture)] https://mise.jdx.dev/deb stable main" | tee /etc/apt/sources.list.d/mise.list && \
    apt-get update && \
    apt-get install -y mise && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Copy OpenRC from builder
COPY --from=builder /build/openrc-install/usr /usr/
COPY --from=builder /build/openrc-install/etc /etc/
COPY --from=builder /build/openrc-install/sbin /sbin/
COPY --from=builder /build/openrc-install/bin /bin/

# Configure OpenRC
RUN mkdir -p /run/openrc && \
    touch /run/openrc/softlevel && \
    mkdir -p /etc/init.d && \
    mkdir -p /etc/runlevels/default && \
    mkdir -p /etc/runlevels/boot && \
    mkdir -p /etc/runlevels/shutdown && \
    mkdir -p /etc/conf.d

# Create systemd redirect script
RUN echo '#!/bin/sh\necho "This system uses openrc for services, not systemd. See /llm.txt"\nexit 1' > /usr/local/bin/systemd-redirect && \
    chmod +x /usr/local/bin/systemd-redirect && \
    ln -sf /usr/local/bin/systemd-redirect /usr/bin/systemctl && \
    ln -sf /usr/local/bin/systemd-redirect /usr/bin/systemd && \
    ln -sf /usr/local/bin/systemd-redirect /usr/sbin/systemd && \
    ln -sf /usr/local/bin/systemd-redirect /bin/systemctl || true && \
    ln -sf /usr/local/bin/systemd-redirect /sbin/systemctl || true

# Create deb-systemd-helper wrapper to handle package installations gracefully
RUN if [ -f /usr/bin/deb-systemd-helper ]; then \
        mv /usr/bin/deb-systemd-helper /usr/bin/deb-systemd-helper.real && \
        echo '#!/bin/bash\n\
# Wrapper for deb-systemd-helper to handle systemd operations gracefully\n\
if [[ "$*" == *"systemctl"* ]] || [[ "$*" == *".service"* ]] || [[ "$*" == *".socket"* ]]; then\n\
    # For systemd operations, print info if verbose, otherwise silent success\n\
    if [[ "${DEBIAN_FRONTEND}" != "noninteractive" ]] && [[ "${DEBCONF_NONINTERACTIVE_SEEN}" != "true" ]]; then\n\
        echo "Note: Skipping systemd service setup (using openrc instead). See /llm.txt" >&2\n\
    fi\n\
    exit 0\n\
else\n\
    # Pass through to the real helper for non-systemd operations\n\
    exec /usr/bin/deb-systemd-helper.real "$@"\n\
fi' > /usr/bin/deb-systemd-helper && \
        chmod +x /usr/bin/deb-systemd-helper; \
    fi

# Create invoke-rc.d wrapper to handle service operations gracefully
RUN if [ -f /usr/sbin/invoke-rc.d ]; then \
        mv /usr/sbin/invoke-rc.d /usr/sbin/invoke-rc.d.real && \
        echo '#!/bin/bash\n\
# Wrapper for invoke-rc.d to handle init script operations gracefully\n\
# Since we use openrc, skip traditional init script operations\n\
if [[ "${DEBIAN_FRONTEND}" != "noninteractive" ]] && [[ "${DEBCONF_NONINTERACTIVE_SEEN}" != "true" ]]; then\n\
    echo "Note: Skipping init script $2 (using openrc instead). See /llm.txt" >&2\n\
fi\n\
exit 0' > /usr/sbin/invoke-rc.d && \
        chmod +x /usr/sbin/invoke-rc.d; \
    fi

# Create OpenRC init script
RUN echo '#!/sbin/openrc-run\n\
\n\
name="container-init"\n\
description="Container initialization service"\n\
\n\
depend() {\n\
    after localmount\n\
    before *\n\
}\n\
\n\
start() {\n\
    ebegin "Starting container initialization"\n\
    # Add any container-specific initialization here\n\
    eend $?\n\
}' > /etc/init.d/container-init && \
    chmod +x /etc/init.d/container-init

# Copy documentation
COPY llm.txt /llm.txt
COPY docs /docs

ENTRYPOINT ["/usr/sbin/openrc-init"]
CMD []