#!/bin/sh
# Build the whole proof and print the receipts. Exit 0 only if every headline receipt is clean.
set -eu
cd "$(dirname "$0")/.."
lake exe cache get
lake build Zeta2
lake env lean src/Receipts.lean | tee receipts/this-machine.txt
python3 scripts/check_receipts.py receipts/this-machine.txt
