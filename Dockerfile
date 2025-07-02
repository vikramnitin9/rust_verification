FROM ubuntu:24.10

RUN apt-get update && apt-get install -y \
    build-essential \
    clang \
    && rm -rf /var/lib/apt/lists/*

RUN apt-get install cbmc