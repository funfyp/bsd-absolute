# Base image with micromamba (fast conda) for conda-forge packages
FROM mambaorg/micromamba:1.4.0

# Create a working environment
ENV MAMBA_DOCKERFILE_ACTIVATE=1
WORKDIR /workspace

# Create a small environment and install essentials, Sage and node
RUN micromamba install -y -n base -c conda-forge \
    python=3.10 nodejs git openssh mpmath sympy \
    && micromamba clean --all -y

# Defer heavy installs (Sage, arb) to post_create script to avoid long build time in some runners
COPY .devcontainer/post_create.sh /workspace/.devcontainer/post_create.sh
RUN chmod +x /workspace/.devcontainer/post_create.sh

# Set default user
ARG USER=vscode
ARG USER_ID=1000
RUN useradd -m -u ${USER_ID} ${USER} || true
USER ${USER}
ENV PATH=/opt/conda/bin:$PATH
