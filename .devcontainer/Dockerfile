FROM mcr.microsoft.com/devcontainers/base:jammy

USER vscode
WORKDIR /home/vscode

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

ENV PATH="/home/vscode/.elan/bin:${PATH}"

# Pre-install the pinned Lean toolchain at image-build time so it becomes a
# cached layer instead of a ~300 MB download on the first `lake` invocation.
# (Build context is the repo root; see .dockerignore.)
COPY --chown=vscode:vscode lean-toolchain ./lean-toolchain
RUN elan toolchain install "$(cat ./lean-toolchain)" && rm ./lean-toolchain
