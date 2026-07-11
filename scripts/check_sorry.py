#!/usr/bin/env python3
"""Fail the build if any *undocumented* `sorry` is present.

Lean emits the warning `declaration uses 'sorry'` for every declaration whose
proof term still contains `sorry`.  We parse the build log for that warning.

The repository currently has exactly one honestly-documented open gap:

    card_W_H4 : Nat.card W_H4 = 14400     (RGF/Math/Algebra/CoxeterFiveFold.lean)

Determining the order of the 14400-element non-crystallographic Coxeter group
H4 by the covering-set / complete-rewriting-system method that we use for
A3 (24), B3 (48) and H3 (120) requires an enumeration that is prohibitively
large, and Mathlib presently has no finiteness/cardinality theory for Coxeter
groups (nor the parabolic-subgroup machinery that would allow a smaller proof).
So this single gap is allow-listed *by file*.

Policy:
  * ANY `sorry` warning outside the allow-listed file fails the build.
  * The allow-listed file may contain AT MOST ONE `sorry` warning; a second
    (i.e. a *new* undocumented gap) also fails the build.
  * If the allow-listed gap is eventually closed (zero warnings), the build
    still passes; please then delete this allowance.
"""

import re
import sys

ALLOWED_FILE = "RGF/Math/Algebra/CoxeterFiveFold.lean"
ALLOWED_MAX = 1  # at most the single documented card_W_H4 gap

# Lean has printed this warning with different quoting over versions:
#   Lean ≤ 4.2x (older):  declaration uses 'sorry'
#   Lean 4.28.0:          declaration uses `sorry`
# Match either quote style so the audit keeps working across toolchains.
MARKER = re.compile(r"declaration uses [`']sorry[`']")


def main() -> int:
    path = sys.argv[1] if len(sys.argv) > 1 else "build.log"
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        lines = [ln.rstrip("\n") for ln in fh if MARKER.search(ln)]

    allowed = [ln for ln in lines if ALLOWED_FILE in ln]
    disallowed = [ln for ln in lines if ALLOWED_FILE not in ln]

    ok = True

    if disallowed:
        ok = False
        print("::error::Undocumented 'sorry' detected in the build:")
        for ln in disallowed:
            print("  " + ln)

    if len(allowed) > ALLOWED_MAX:
        ok = False
        print(
            f"::error::Too many 'sorry' warnings in the allow-listed file "
            f"{ALLOWED_FILE}: found {len(allowed)}, allowed at most {ALLOWED_MAX}."
        )
        for ln in allowed:
            print("  " + ln)

    if not ok:
        return 1

    if allowed:
        print(
            f"OK: no undocumented 'sorry'. "
            f"{len(allowed)} allow-listed open gap in {ALLOWED_FILE} (card_W_H4)."
        )
    else:
        print("OK: the build is completely free of 'sorry'.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
