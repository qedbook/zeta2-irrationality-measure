#!/usr/bin/env python3
"""Check what `lake env lean src/Receipts.lean` printed, as scripts/verify.sh records it.

    python3 scripts/check_receipts.py <file>

RECEIPTS CLEAN and exit 0 only when all of these hold, RECEIPTS RED and exit 1 otherwise:
  - every `#print axioms` line of the file (`'<name>' depends on axioms: [...]`, or `'<name>' does
    not depend on any axioms`) is for one of THEOREMS, the theorems src/Receipts.lean prints, and
    reads exactly [propext, Classical.choice, Quot.sound];
  - each of THEOREMS has such a line, and a second line for it reads the same as the first;
  - each of THEOREMS has its type printed by its `#check` line. The type is printed for a reader
    to read; this script does not judge it;
  - no `sorryAx` appears;
  - no Lean error appears anywhere on any line, in any case: `x.lean:9:0: error: ...`,
    `error: ...`, `Error: ...` and `error(<code>): ...` alike;
  - when the file carries the stamp scripts/verify.sh writes, the exit status it records for lean
    is 0.
Exit 2 when the file cannot be read. The last line says what was checked.
"""
import re
import sys

ALLOW = "[propext, Classical.choice, Quot.sound]"
THEOREMS = [
    "Zeta2Target.zeta2_not_liouvilleWith",
    "Zeta2Target.zeta2_irrationality_measure_le",
    "Zeta2Unconditional.zeta2_rational_approximation",
    "Zeta2Hpsi.hψ",
    "MediumPNT",
    "Zeta2Final.zeta2_eq_riemannZeta_two",
    "Zeta2Final.zeta2_eq_tsum_from_one",
]
# The name runs to the first quote followed by a space: Lean prints a name's primes inside the quotes,
# as in `'Zeta2MomC.momI_control_one'' depends on axioms: [...]`.
AXIOMS = re.compile(r"^'(.+?)' (?:depends on axioms: (\[[^\]]*\])|does not depend on any axioms)", re.M)
ERROR = re.compile(r"(?<![\w.])error(?:\([^()\n]*\))?:", re.I)
STAMP = re.compile(r"^# scripts/verify\.sh, commit: ", re.M)
STATUS = re.compile(r"^# lean exit status: (-?\d+)\s*$", re.M)


def main(argv):
    if len(argv) != 2:
        print("usage: check_receipts.py <file>")
        return 2
    path = argv[1]
    try:
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
    except (OSError, UnicodeDecodeError) as e:
        print(f"RECEIPTS NOT CHECKED: cannot read {path}: {e}")
        return 2
    bad = 0
    read = {}                                  # name -> what each of its axioms lines reads, in order
    for m in AXIOMS.finditer(text):
        read.setdefault(m.group(1), []).append(" ".join(m.group(2).split()) if m.group(2) else "[]")
    for name in THEOREMS:
        lines = read.get(name, [])
        typed = re.search(rf"^@?{re.escape(name)} :", text, re.M) is not None
        axioms = ("NO AXIOMS LINE" if not lines else lines[0] if len(set(lines)) == 1 else
                  f"{len(lines)} axioms lines that differ: " + " / ".join(lines))
        ok = axioms == ALLOW and typed
        print(("OK   " if ok else "FAIL ") + name + " -> " + axioms
              + ("" if typed else "; NO TYPE PRINTED (its #check line is missing)"))
        bad += 0 if ok else 1
    others = [name for name in read if name not in THEOREMS]
    if others:
        print(f"FAIL axioms printed for a theorem src/Receipts.lean does not print: {', '.join(others)}")
        bad += 1
    if "sorryAx" in text:
        print("FAIL sorryAx appears in the output")
        bad += 1
    errors = [n for n, line in enumerate(text.splitlines(), 1) if ERROR.search(line)]
    if errors:
        print(f"FAIL a Lean error appears in the output, on line(s) {', '.join(map(str, errors))}")
        bad += 1
    statuses = STATUS.findall(text)
    if statuses:
        status = f"lean's exit status {statuses[-1]}, as stamped"
        if statuses[-1] != "0":
            print(f"FAIL lean exited with status {statuses[-1]}")
            bad += 1
    elif STAMP.search(text):
        status = "lean's exit status missing from the stamp"
        print("FAIL the file carries the stamp of scripts/verify.sh but no exit status for lean")
        bad += 1
    else:
        status = "lean's exit status not recorded in this file"
    print(f"RECEIPTS {'CLEAN' if bad == 0 else f'RED ({bad})'} -- checked in {path}: that each of the "
          f"{len(THEOREMS)} theorems src/Receipts.lean prints depends on exactly {ALLOW}, on every line that "
          f"prints its axioms, and has its type printed, that no other theorem's axioms are printed, that "
          f"sorryAx is absent, that no line holds a Lean error in any case; {status}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
