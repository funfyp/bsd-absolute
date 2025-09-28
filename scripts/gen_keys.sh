#!/bin/bash
# Generate ECDSA key pair
openssl ecparam -genkey -name prime256v1 -noout -out ecdsa_priv.pem
openssl ec -in ecdsa_priv.pem -pubout -out ecdsa_pub.pem

# Sign (DER signature)
openssl dgst -sha256 -sign ecdsa_priv.pem -out cert_E1.sig cert_E1_canonical.json
xxd -p cert_E1.sig > cert_E1.sig.hex
# Put the hex into "provenance.signature" and distribute the public key cert_E1.pub = ecdsa_pub.pem for verifiers
