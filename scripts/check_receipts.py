#!/usr/bin/env python3
"""Reads the output of `lake env lean src/Receipts.lean` and refuses anything but the allowlist."""
import re, sys
ALLOW = "[propext, Classical.choice, Quot.sound]"
HEADLINES = ["Zeta2Target.zeta2_not_liouvilleWith", "Zeta2Target.zeta2_irrationality_measure_le",
             "Zeta2Unconditional.zeta2_rational_approximation", "Zeta2Hpsi.hψ", "MediumPNT"]
text = open(sys.argv[1], encoding="utf-8").read()
bad = 0
for name in HEADLINES:
    m = re.search(rf"^'{re.escape(name)}' depends on axioms: (\[.*?\])", text, re.M | re.S)
    axioms = " ".join(m.group(1).split()) if m else None
    ok = axioms == ALLOW
    print(("OK   " if ok else "FAIL ") + name + " -> " + (axioms or "NO RECEIPT"))
    bad += 0 if ok else 1
if "sorryAx" in text: print("FAIL sorryAx appears in the output"); bad += 1
if re.search(r"^error", text, re.M): print("FAIL a Lean error appears in the output"); bad += 1
print("RECEIPTS " + ("CLEAN" if bad == 0 else f"RED ({bad})"))
sys.exit(1 if bad else 0)
