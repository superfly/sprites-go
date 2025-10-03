############################
# STAGE 0 – tool‑chain    #
############################
ARG USER=sprite UID=1001
FROM ubuntu:25.04 AS base
ARG USER UID
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential clang sudo inotify-tools \
        curl git ca-certificates gnupg dirmngr \
        autoconf automake libtool pkg-config xz-utils \
        libssl-dev zlib1g-dev libreadline-dev libsqlite3-dev \
        unzip wget tar \
        coreutils util-linux findutils grep sed gawk \
        file which less nano vim-tiny \
        procps htop tree \
        zip gzip bzip2 locales iproute2 \
        libffi-dev libyaml-dev gosu xdg-utils \
        tmux rsync zsh fish tcsh ksh \
    && locale-gen en_US.UTF-8 \
    && apt-get clean \
    && curl -L https://sw.kovidgoyal.net/kitty/installer.sh | sh /dev/stdin launch=n dest=/.sprite/bin/
# we are keeping indexes for future apts
# Note: kitty wrapper script is provided in root/.sprite/bin/kitty

# --- setup environment ---
ENV LANG=en_US.UTF-8 \
    PATH="/.sprite/bin:${PATH}"

############################
# Languages (one per layer)
# (built separately)
############################
FROM base AS languages-split

ARG USER UID

# Install each language in separate layers for better errors
COPY languages/nodejs.sh /tmp/
RUN chmod +x /tmp/nodejs.sh && /tmp/nodejs.sh /.sprite && rm /tmp/nodejs.sh

COPY languages/erlang.sh /tmp/
RUN chmod +x /tmp/erlang.sh && /tmp/erlang.sh /.sprite && rm /tmp/erlang.sh

COPY languages/elixir.sh /tmp/
RUN chmod +x /tmp/elixir.sh && /tmp/elixir.sh /.sprite && rm /tmp/elixir.sh

COPY languages/golang.sh /tmp/
RUN chmod +x /tmp/golang.sh && /tmp/golang.sh /.sprite && rm /tmp/golang.sh

COPY languages/ruby.sh /tmp/
RUN chmod +x /tmp/ruby.sh && /tmp/ruby.sh /.sprite && rm /tmp/ruby.sh

COPY languages/rust.sh /tmp/
RUN chmod +x /tmp/rust.sh && /tmp/rust.sh /.sprite && rm /tmp/rust.sh

COPY languages/bun.sh /tmp/
RUN chmod +x /tmp/bun.sh && /tmp/bun.sh /.sprite && rm /tmp/bun.sh

COPY languages/deno.sh /tmp/
RUN chmod +x /tmp/deno.sh && /tmp/deno.sh /.sprite && rm /tmp/deno.sh

COPY languages/java.sh /tmp/
RUN chmod +x /tmp/java.sh && /tmp/java.sh /.sprite && rm /tmp/java.sh

COPY languages/python.sh /tmp/
RUN chmod +x /tmp/python.sh && /tmp/python.sh /.sprite && rm /tmp/python.sh

# Install agents (depends on Node.js being installed)
COPY languages/agents.sh /tmp/
RUN chmod +x /tmp/agents.sh && /tmp/agents.sh /.sprite && rm /tmp/agents.sh


############################
# Languages ONLY
############################
FROM scratch AS languages
ARG UID

COPY --chown=$UID:$UID --from=languages-split /.sprite/languages /.sprite/languages
COPY --chown=$UID:$UID --from=languages-split /.sprite/bin /.sprite/bin
COPY --chown=$UID:$UID --from=languages-split /.sprite/etc/profile.d /.sprite/etc/profile.d

####################################################
# STAGE 1 – final runtime
# does not include languages
# need to assemble overlay at runtime
####################################################
FROM base
ARG USER UID

# Create sprite scripts directory and languages directory
RUN mkdir -p /.sprite/languages /.sprite/bin /.sprite/etc/profile.d

# Copy our stuff
COPY root/ /

# Set proper permissions on shell configurations
# The shell config files are copied from root/etc/skel/* during COPY root/ /
RUN chmod 644 /etc/skel/.* 2>/dev/null || true

# Make language dependency installer executable if it exists
RUN chmod +x /.sprite/bin/install-language-deps 2>/dev/null || true

# Source sprite scripts in /etc/profile for login shells
RUN echo '' >> /etc/profile && \
    echo '# Source sprite environment' >> /etc/profile && \
    echo '[ -r /.sprite/etc/profile.d/sprite.sh ] && . /.sprite/etc/profile.d/sprite.sh' >> /etc/profile

# Copy the sudoers file and user skeleton, then fix ownership
RUN useradd -ms /bin/bash -u $UID $USER \
&& echo "$USER ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/$USER \
&& chmod 0440 /etc/sudoers.d/$USER \
&& usermod -aG sudo,users $USER

USER sprite

# --- global environment ---
ENV LANG=en_US.UTF-8

# --- user env ---
ENV BROWSER="/.sprite/bin/sprite-browser" \
    HOME="/home/sprite"

WORKDIR /home/sprite

ENTRYPOINT ["/.sprite/entrypoint.sh"]
CMD ["tail", "-f", "/dev/null"]