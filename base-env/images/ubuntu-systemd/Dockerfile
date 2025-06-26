FROM ubuntu:25.04

# Install systemd
RUN apt-get update && \
    apt-get install -y systemd systemd-sysv && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Ensure systemd is properly linked as init
RUN ln -sf /lib/systemd/systemd /sbin/init
RUN systemctl mask systemd-networkd.service

# Set container=docker to enable systemd support
ENV container=docker
ENV HOSTNAME=sprite-systemd
ENV TERM=xterm
ENV HOME=/root

# Set systemd as the init system
CMD ["/lib/systemd/systemd", "--unit=basic.target", "--no-cgroups"]