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

# Copy documentation
COPY llm.txt /llm.txt
COPY docs /docs

ENTRYPOINT ["/init"]
CMD ["tail", "-f", "/dev/null"]