#!/bin/bash
# Ensure jq is installed (micromamba install jq or apt)
# Canonicalize JSON and compute SHA256 digest
jq -c -S '.' cert_E1.json > cert_E1_canonical.json
sha256sum cert_E1_canonical.json
# Copy the hex digest into the provenance.sha256 field (update file)
