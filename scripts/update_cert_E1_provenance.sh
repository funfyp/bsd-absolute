#!/bin/bash
# Canonicalize cert_E1.json, compute SHA256 hash, sign, and update provenance fields

set -e

# Canonicalize JSON
jq -c -S '.' cert_E1.json > cert_E1_canonical.json

# Compute SHA256 hash
HASH=$(sha256sum cert_E1_canonical.json | awk '{print $1}')
echo "SHA256: $HASH"

# Generate ECDSA key if not present
if [ ! -f ecdsa_priv.pem ]; then
    openssl ecparam -genkey -name prime256v1 -noout -out ecdsa_priv.pem
fi
openssl ec -in ecdsa_priv.pem -pubout -out ecdsa_pub.pem

# Sign canonical JSON
openssl dgst -sha256 -sign ecdsa_priv.pem -out cert_E1.sig cert_E1_canonical.json
xxd -p cert_E1.sig > cert_E1.sig.hex
SIG=$(cat cert_E1.sig.hex)

# Update provenance fields in cert_E1.json
jq --arg hash "$HASH" --arg sig "$SIG" \
   '.provenance.sha256 = $hash | .provenance.signature = $sig' \
   cert_E1.json > cert_E1.json.tmp && mv cert_E1.json.tmp cert_E1.json

echo "Updated cert_E1.json with hash and signature."
