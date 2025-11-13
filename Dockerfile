FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt -yqq update && \
    apt install -y build-essential wget unzip curl git bash-completion && \
    rm -rf /var/lib/apt/lists/*

RUN apt -yqq update && \
    apt install -yqq cmake && \
    apt install -yqq llvm-14 llvm-14-dev llvm-14-tools clang-14 libclang-14-dev && \
    rm -rf /var/lib/apt/lists/*

# Detect architecture and install the appropriate version of CBMC
RUN ARCH=$(dpkg --print-architecture) && \
    if [ "$ARCH" = "arm64" ]; then \
        CBMC_DEB="ubuntu-24.04-arm64-cbmc-6.7.1-Linux.deb"; \
    elif [ "$ARCH" = "amd64" ]; then \
        CBMC_DEB="ubuntu-24.04-cbmc-6.7.1-Linux.deb"; \
    else \
        echo "Unsupported architecture: $ARCH" && exit 1; \
    fi && \
    wget "https://github.com/diffblue/cbmc/releases/download/cbmc-6.7.1/$CBMC_DEB" && \
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
        Z3_FOLDER="z3-4.15.2-arm64-glibc-2.34"; \
    elif [ "$ARCH" = "amd64" ]; then \
        Z3_FOLDER="z3-4.15.2-x64-glibc-2.39"; \
    else \
        echo "Unsupported architecture: $ARCH" && exit 1; \
    fi && \
    wget "https://github.com/Z3Prover/z3/releases/download/z3-4.15.2/${Z3_FOLDER}.zip" -O z3.zip && \
    unzip z3.zip -d /opt/z3 && \
    rm z3.zip && \
    chmod +x /opt/z3/$Z3_FOLDER/bin/z3 && \
    ln -s /opt/z3/$Z3_FOLDER/bin/z3 /usr/local/bin/z3

WORKDIR /app

# Switch to the non-root user
USER ${USER_ID}:${GROUP_ID}

ENV PATH="/opt/miniconda3/bin:${PATH}"

# Install Miniconda on x86 or ARM platforms
RUN arch=$(uname -m) && \
    cd /app && wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-$arch.sh -O miniconda.sh && \
    mkdir -p /opt/miniconda3 && \
    bash miniconda.sh -b -u -p /opt/miniconda3 && \
    rm -f miniconda.sh

RUN conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/main
RUN conda tos accept --override-channels --channel https://repo.anaconda.com/pkgs/r

RUN conda install -y python=3.13 pip
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

ENV CARGO_HOME="/app/.cargo"
ENV RUSTUP_HOME="/app/.rustup"
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/app/.cargo/bin:${PATH}"
RUN rustup default 1.90.0
RUN cargo install --locked kani-verifier && cargo kani setup
