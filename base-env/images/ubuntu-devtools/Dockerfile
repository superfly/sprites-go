############################
# STAGE 0 – tool‑chain    #
############################
FROM ubuntu:25.04 AS buildbase
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
    && apt-get clean && rm -rf /var/cache/apt/archives/partial

# --- global asdf ---
ENV ASDF_DIR=/opt/asdf \
    ASDF_DATA_DIR=/opt/asdf \
    PATH="/opt/asdf/bin:/opt/asdf/shims:${PATH}"
RUN git clone https://github.com/asdf-vm/asdf.git --branch v0.14.0 --depth 1 "$ASDF_DIR" \
 && echo '. /opt/asdf/asdf.sh'                 >  /etc/profile.d/asdf.sh \
 && echo '. /opt/asdf/completions/asdf.bash'  >> /etc/profile.d/asdf.sh

# --- sprite user (uid can be overridden at build time) ---
ARG USER=sprite UID=1001
RUN useradd -ms /bin/bash -u $UID $USER \
 && echo "$USER ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/$USER \
 && chmod 0440 /etc/sudoers.d/$USER

 # Don't chown /opt/asdf yet – we'll do that in the runtime stage
 
####################################################
# STAGE 1 – install all the languages (langbuilder)
####################################################
FROM buildbase AS langbuilder

# Switch to root (already root) and source asdf to install plugins & latest versions
RUN bash -lc ". /opt/asdf/asdf.sh && \
    asdf plugin-add erlang    https://github.com/asdf-vm/asdf-erlang.git && \
    asdf plugin-add elixir    https://github.com/asdf-vm/asdf-elixir.git && \
    asdf plugin-add nodejs    https://github.com/asdf-vm/asdf-nodejs.git && \
    asdf plugin-add golang    https://github.com/kennyp/asdf-golang.git && \
    asdf plugin-add ruby      https://github.com/asdf-vm/asdf-ruby.git && \
    asdf plugin-add rust      https://github.com/code-lever/asdf-rust.git && \
    asdf install erlang    latest && asdf global erlang    latest && \
    asdf install elixir    latest && asdf global elixir    latest && \
    asdf install nodejs    latest && asdf global nodejs    latest && \
    asdf install golang    latest && asdf global golang    latest && \
    asdf install ruby      latest && asdf global ruby      latest && \
    asdf install rust      latest && asdf global rust      latest"

####################################################
# STAGE 2 – final runtime
####################################################
FROM ubuntu:25.04 AS runtime

# Install the same dev-packages (so no missing deps at runtime)
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
    && apt-get clean

# Bring in asdf + your pre-built languages
COPY --from=langbuilder /opt/asdf          /opt/asdf
COPY --from=langbuilder /etc/profile.d/asdf.sh /etc/profile.d/asdf.sh


# Copy the sudoers file and user skeleton, then fix ownership
COPY --from=buildbase /etc/sudoers.d/sprite /etc/sudoers.d/sprite
RUN useradd -ms /bin/bash -u 1001 sprite \
 && usermod -aG sudo,users sprite \
 && chown -R sprite:sprite /opt/asdf \
 && chmod 0440 /etc/sudoers.d/sprite

ENV ASDF_DIR=/opt/asdf \
    ASDF_DATA_DIR=/opt/asdf \
    PATH="/opt/asdf/bin:/opt/asdf/shims:${PATH}"

# Create sprite scripts directory
RUN mkdir -p /.sprite

# Copy scripts and documentation
COPY setup-mounts.sh /.sprite/setup-mounts.sh
COPY entrypoint.sh /.sprite/entrypoint.sh
COPY llm.txt /llm.txt

# Make scripts executable
RUN chmod +x /.sprite/setup-mounts.sh /.sprite/entrypoint.sh

USER sprite
WORKDIR /home/sprite

ENTRYPOINT ["/.sprite/entrypoint.sh"]
CMD ["/bin/bash"]