############################
# STAGE 0 – tool‑chain    #
############################
ARG USER=sprite UID=1001
FROM ubuntu:25.04 AS base
ARG USER UID
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential sudo \
        curl git ca-certificates gnupg dirmngr \
        autoconf automake libtool pkg-config xz-utils \
        libssl-dev zlib1g-dev libreadline-dev libsqlite3-dev \
        unzip wget tar \
        coreutils util-linux findutils grep sed gawk \
        file which less nano vim-tiny \
        procps htop tree \
        zip gzip bzip2 \
        libffi-dev libyaml-dev gosu \
    && apt-get clean
# we are keeping indexes for future apts

# --- global asdf ---
ENV ASDF_DIR=/opt/asdf \
    ASDF_DATA_DIR=/opt/asdf \
    PATH="/opt/asdf/bin:/opt/asdf/shims:${PATH}"

RUN git clone https://github.com/asdf-vm/asdf.git --branch v0.14.0 --depth 1 "$ASDF_DIR" \
 && echo '. /opt/asdf/asdf.sh'                 >  /etc/profile.d/asdf.sh \
 && echo '. /opt/asdf/completions/asdf.bash'  >> /etc/profile.d/asdf.sh

# Copy the sudoers file and user skeleton, then fix ownership

RUN useradd -ms /bin/bash -u $UID $USER \
 && echo "$USER ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/$USER \
 && chmod 0440 /etc/sudoers.d/$USER \
 && usermod -aG sudo,users $USER \
 && chown -R $USER:$USER /opt/asdf


############################
# asdf Languages (one per layer)
# (built separately)
############################
FROM base AS languages-split

# Install each language in separate layers for better errors
COPY languages/erlang.sh /tmp/
RUN chmod +x /tmp/erlang.sh && /tmp/erlang.sh && rm /tmp/erlang.sh

COPY languages/elixir.sh /tmp/
RUN chmod +x /tmp/elixir.sh && /tmp/elixir.sh && rm /tmp/elixir.sh

COPY languages/nodejs.sh /tmp/
RUN chmod +x /tmp/nodejs.sh && /tmp/nodejs.sh && rm /tmp/nodejs.sh

COPY languages/golang.sh /tmp/
RUN chmod +x /tmp/golang.sh && /tmp/golang.sh && rm /tmp/golang.sh

COPY languages/ruby.sh /tmp/
RUN chmod +x /tmp/ruby.sh && /tmp/ruby.sh && rm /tmp/ruby.sh

COPY languages/rust.sh /tmp/
RUN chmod +x /tmp/rust.sh && /tmp/rust.sh && rm /tmp/rust.sh

COPY languages/bun.sh /tmp/
RUN chmod +x /tmp/bun.sh && /tmp/bun.sh && rm /tmp/bun.sh

COPY languages/deno.sh /tmp/
RUN chmod +x /tmp/deno.sh && /tmp/deno.sh && rm /tmp/deno.sh

COPY languages/java.sh /tmp/
RUN chmod +x /tmp/java.sh && /tmp/java.sh && rm /tmp/java.sh

############################
# asdf Languages Combined
############################
FROM base AS languages
ARG USER UID

COPY --chown=$USER:$USER --from=languages-split /opt/asdf /opt/asdf


####################################################
# STAGE 1 – final runtime
# does not include languages
# need to assemble overlay at runtime
####################################################
FROM base
ARG USER UID

ENV ASDF_DIR=/opt/asdf \
    ASDF_DATA_DIR=/opt/asdf \
    PATH="/opt/asdf/bin:/opt/asdf/shims:${PATH}" \
    HOME="/home/sprite"

# Create sprite scripts directory
RUN mkdir -p /.sprite

# Copy our stuff
COPY root/ /

USER sprite
WORKDIR /home/sprite

ENTRYPOINT ["/.sprite/entrypoint.sh"]
CMD ["tail", "-f", "/dev/null"]