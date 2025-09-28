#!/usr/bin/env bash
set -e
# Run in container after Codespace created. Installs Sage and Arb from conda-forge.
echo "Post-create: installing heavy packages (may take several minutes)..."
micromamba install -y -n base -c conda-forge sage arb pyarb || echo "Try installing arb from source if not available"
# Install node deps if any
if [ -f package.json ]; then
  npm install
fi
echo "Post-create: done. You can run python scripts or node stress harness."
