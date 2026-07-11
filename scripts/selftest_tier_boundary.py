#!/usr/bin/env python3
"""Negative (counterexample) self-test for `check_tier_boundary.py`.

A gate/guard tool is only trustworthy if it has been shown to *fail* on a known
bad input, not merely to *pass* on the current (clean) tree. `check_tier_boundary.py`
by itself only demonstrates the latter ("no violation right now"). This script
demonstrates the former: it injects a deliberate Tier-1 -> Tier-3 illegal import
into a real Tier-1 file, runs the checker, and asserts that the checker

  * exits non-zero, and
  * names the injected offending edge in its output,

then restores the file to its original bytes (even on error). This is the
minimal "does the gate actually catch a violation?" test that must pass before
the gate can be relied on.

Exit code 0 == the checker correctly detected the injected violation (self-test
PASSED); nonzero == the checker FAILED to behave as a gate (or the harness could
not run), which is itself a CI failure.
"""
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CHECKER = os.path.join(ROOT, "scripts", "check_tier_boundary.py")

# A real Tier-1 file (RGF.Generative.Core.*) and a real Tier-3 module to import.
TIER1_FILE = os.path.join(ROOT, "RGF", "Generative", "Core", "Basic.lean")
ILLEGAL_IMPORT = "import RGF.Applications.BabaiWeak"
OFFENDER_MODULE = "RGF.Applications.BabaiWeak"


def run_checker():
    return subprocess.run(
        [sys.executable, CHECKER],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )


def main() -> int:
    # 0. Sanity: the clean tree must currently PASS, otherwise the negative
    #    test would be meaningless (we could not attribute a failure to us).
    baseline = run_checker()
    if baseline.returncode != 0:
        print("SELF-TEST ABORTED: checker already reports a violation on the "
              "current tree; cannot run a clean negative test.")
        print(baseline.stdout)
        print(baseline.stderr, file=sys.stderr)
        return 2

    if not os.path.isfile(TIER1_FILE):
        print(f"SELF-TEST ABORTED: expected Tier-1 file not found: {TIER1_FILE}")
        return 2

    with open(TIER1_FILE, "rb") as fh:
        original = fh.read()

    try:
        # 1. Inject the illegal import right after the first `import` line.
        text = original.decode("utf-8")
        lines = text.split("\n")
        insert_at = None
        for i, ln in enumerate(lines):
            if ln.startswith("import "):
                insert_at = i + 1
                break
        if insert_at is None:
            insert_at = 0
        lines.insert(insert_at, ILLEGAL_IMPORT)
        with open(TIER1_FILE, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))

        # 2. Run the checker; it MUST fail now.
        result = run_checker()
    finally:
        # 3. Always restore the original bytes.
        with open(TIER1_FILE, "wb") as fh:
            fh.write(original)

    ok = True
    if result.returncode == 0:
        print("SELF-TEST FAILED: checker exited 0 despite an injected "
              "Tier-1 -> Tier-3 illegal import. The gate does NOT catch "
              "violations.")
        ok = False
    if OFFENDER_MODULE not in result.stdout:
        print("SELF-TEST FAILED: checker output did not mention the injected "
              f"offender {OFFENDER_MODULE}.")
        ok = False

    # 4. Confirm the restore left the tree clean again.
    restored = run_checker()
    if restored.returncode != 0:
        print("SELF-TEST FAILED: tree not clean after restore (harness bug).")
        print(restored.stdout)
        ok = False

    if ok:
        print("Tier-boundary gate self-test PASSED: the checker exits non-zero "
              "and reports the offending edge when a Tier-1 -> Tier-3 illegal "
              f"import ({OFFENDER_MODULE}) is injected, and the tree is clean "
              "again after restore.")
        print("\n--- checker output on the injected violation ---")
        print(result.stdout.rstrip())
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
