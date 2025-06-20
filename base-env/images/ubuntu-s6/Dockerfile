# Use your favorite image
FROM ubuntu:25.04
ARG S6_OVERLAY_VERSION=3.2.1.0
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

ADD https://github.com/just-containers/s6-overlay/releases/download/v${S6_OVERLAY_VERSION}/s6-overlay-noarch.tar.xz /tmp
RUN tar -C / -Jxpf /tmp/s6-overlay-noarch.tar.xz
ADD https://github.com/just-containers/s6-overlay/releases/download/v${S6_OVERLAY_VERSION}/s6-overlay-x86_64.tar.xz /tmp
RUN tar -C / -Jxpf /tmp/s6-overlay-x86_64.tar.xz

# Create systemd redirect script
RUN echo '#!/bin/sh\necho "This system uses s6-overlay for services, not systemd. See /llm.txt"\nexit 1' > /usr/local/bin/systemd-redirect && \
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
        echo "Note: Skipping systemd service setup (using s6-overlay instead). See /llm.txt" >&2\n\
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
# Since we use s6-overlay, skip traditional init script operations\n\
if [[ "${DEBIAN_FRONTEND}" != "noninteractive" ]] && [[ "${DEBCONF_NONINTERACTIVE_SEEN}" != "true" ]]; then\n\
    echo "Note: Skipping init script $2 (using s6-overlay instead). See /llm.txt" >&2\n\
fi\n\
exit 0' > /usr/sbin/invoke-rc.d && \
        chmod +x /usr/sbin/invoke-rc.d; \
    fi

# Copy documentation
COPY llm.txt /llm.txt
COPY docs /docs

ENTRYPOINT ["/init"]
CMD ["tail", "-f", "/dev/null"]