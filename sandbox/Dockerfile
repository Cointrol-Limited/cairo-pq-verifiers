# Sandbox for building and testing third-party patches (other participants' records).
# Pinned toolchain. sandbox/run.sh warms the Scarb/snforge cache once into a volume, so
# later test runs start with --network none.
FROM ubuntu:24.04

ARG SCARB=2.18.0
ARG SNFORGE=0.59.0
ARG USC=2.10.2
ARG PROFILER=0.16.0
ARG TRIPLE=aarch64-unknown-linux-gnu

RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git python3 && rm -rf /var/lib/apt/lists/*

RUN set -eux; mkdir -p /opt/tools; cd /opt/tools; \
    curl -fsSL https://github.com/software-mansion/scarb/releases/download/v${SCARB}/scarb-v${SCARB}-${TRIPLE}.tar.gz | tar -xz; \
    curl -fsSL https://github.com/foundry-rs/starknet-foundry/releases/download/v${SNFORGE}/starknet-foundry-v${SNFORGE}-${TRIPLE}.tar.gz | tar -xz; \
    curl -fsSL https://github.com/software-mansion/universal-sierra-compiler/releases/download/v${USC}/universal-sierra-compiler-v${USC}-${TRIPLE}.tar.gz | tar -xz; \
    curl -fsSL https://github.com/software-mansion/cairo-profiler/releases/download/v${PROFILER}/cairo-profiler-v${PROFILER}-${TRIPLE}.tar.gz | tar -xz; \
    mkdir -p /opt/tools/usc/bin; find /opt/tools -name universal-sierra-compiler -type f -exec mv {} /opt/tools/usc/bin/ \;; \
    ls /opt/tools /opt/tools/*/bin

ENV PATH=/opt/tools/scarb-v${SCARB}-${TRIPLE}/bin:/opt/tools/starknet-foundry-v${SNFORGE}-${TRIPLE}/bin:/opt/tools/usc/bin:/opt/tools/cairo-profiler-v${PROFILER}-${TRIPLE}/bin:${PATH}

RUN useradd -m runner
USER runner
ENV HOME=/home/runner
RUN mkdir -p /home/runner/.cache
WORKDIR /work
