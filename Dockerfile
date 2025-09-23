FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt -y update && \
    apt install -y build-essential wget unzip git bash-completion && \
    rm -rf /var/lib/apt/lists/*

RUN apt -y update && \
    apt install -y cmake && \
    apt install -y llvm-14 llvm-14-dev llvm-14-tools clang-14 libclang-14-dev && \
    rm -rf /var/lib/apt/lists/*

# Detect architecture and install the appropriate version of CBMC
RUN ARCH=$(dpkg --print-architecture) && \
    if [ "$ARCH" = "arm64" ]; then \
        CBMC_URL="https://github.com/diffblue/cbmc/releases/download/cbmc-6.7.1/ubuntu-24.04-arm64-cbmc-6.7.1-Linux.deb"; \
        CBMC_DEB="ubuntu-24.04-arm64-cbmc-6.7.1-Linux.deb"; \
    elif [ "$ARCH" = "amd64" ]; then \
        CBMC_URL="https://github.com/diffblue/cbmc/releases/download/cbmc-6.7.1/ubuntu-24.04-cbmc-6.7.1-Linux.deb"; \
        CBMC_DEB="ubuntu-24.04-cbmc-6.7.1-Linux.deb"; \
    else \
        echo "Unsupported architecture: $ARCH" && exit 1; \
    fi && \
    wget "$CBMC_URL" && \
    dpkg -i "$CBMC_DEB" && \
    rm "$CBMC_DEB"

RUN apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Add a non-root user with the same UID and GID as the host user
ARG USER_ID
ARG GROUP_ID
RUN if ! getent group ${GROUP_ID}; then \
    groupadd -g ${GROUP_ID} appuser; \
    fi

RUN if ! getent passwd ${USER_ID}; then \
    useradd -m -u ${USER_ID} -g ${GROUP_ID} appuser; \
    fi

RUN mkdir -p /opt/miniconda3 && \
    chown -R ${USER_ID}:${GROUP_ID} /opt/miniconda3

# Set the non-root user as the owner of the /app directory
RUN mkdir -p /app && \
    chown -R ${USER_ID}:${GROUP_ID} /app

# Detect architecture and download the correct z3 binary
RUN ARCH=$(dpkg --print-architecture) && \
    if [ "$ARCH" = "arm64" ]; then \
        Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-arm64-glibc-2.34.zip"; \
        Z3_FOLDER="z3-4.15.2-arm64-glibc-2.34"; \
    elif [ "$ARCH" = "amd64" ]; then \
        Z3_URL="https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/z3-4.15.2-x64-glibc-2.39.zip"; \
        Z3_FOLDER="z3-4.15.2-x64-glibc-2.39"; \
    else \
        echo "Unsupported architecture: $ARCH" && exit 1; \
    fi && \
    wget "$Z3_URL" -O z3.zip && \
    unzip z3.zip -d /opt/z3 && \
    rm z3.zip && \
    chmod +x /opt/z3/$Z3_FOLDER/bin/z3 && \
    ln -s /opt/z3/$Z3_FOLDER/bin/z3 /usr/local/bin/z3

# Switch to the non-root user
USER ${USER_ID}:${GROUP_ID}

WORKDIR /app

ENV PATH="/opt/miniconda3/bin:${PATH}"

# Install Miniconda on x86 or ARM platforms
RUN arch=$(uname -m) && \
    if [ "$arch" = "x86_64" ]; then \
    MINICONDA_URL="https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh"; \
    elif [ "$arch" = "aarch64" ]; then \
    MINICONDA_URL="https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-aarch64.sh"; \
    else \
    echo "Unsupported architecture: $arch"; \
    exit 1; \
    fi && \
    cd /app && wget $MINICONDA_URL -O miniconda.sh && \
    mkdir -p /opt/miniconda3 && \
    bash miniconda.sh -b -u -p /opt/miniconda3 && \
    rm -f miniconda.sh

RUN conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/main
RUN conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/r

RUN conda install -y python=3.10 pip
COPY --chown=${USER_ID}:${GROUP_ID} requirements.txt /app/requirements.txt
RUN pip install -r /app/requirements.txt

COPY --chown=${USER_ID}:${GROUP_ID} parsec /app/parsec
RUN cd /app/parsec && \
    rm -rf build && \
    mkdir build && \
    cd build && \
    cmake .. && \
    make -j 4
ENV PARSEC_BUILD_DIR=/app/parsec/build