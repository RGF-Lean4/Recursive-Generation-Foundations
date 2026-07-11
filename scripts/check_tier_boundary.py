#!/usr/bin/env python3
"""Mechanical Tier-1 isolation check for the RGF project.

This script turns the architectural claim "Tier 1 (the neutral generative core
plus the mathematical foundations) does not depend on Tier 2/3 (the locking /
RCD layer and the physical / phenomenological applications)" into a machine
regression check, rather than a documentation-level assertion.

Tier assignment (by module namespace):

  Tier 1  — foundations, must be import-closed:
      RGF.Generative.Core.*      (neutral generative core: step / GenSys, ...)
      RGF.Math.*                 (internal number systems, internal set theory
                                  RGF2/*, analysis, algebra, topology, ...)

  Tier 2  — conditional physical-selection hypothesis (RCD / locking):
      RGF.Generative.Locking.*
      RGF.Generative.Uniqueness.*
      RGF.Generative.Assembly.*  (assemblies that wire Tier 1 into Tier 2/3)

  Tier 3  — phenomenological / physical applications (some falsified):
      RGF.Physics.*
      RGF.Phenomenology.*
      RGF.Applications.*
      RGF.Generative.Bridge.*    (portable kernel demos; currently consume
                                  physics, so kept out of the isolated Tier 1)
      RGF.Generative.Meta.*      (metamathematical corroboration)

The invariant enforced: the transitive `import` closure of every Tier-1 module
contains only Tier-1 modules (and Mathlib / Lean core, which are ignored here).

Exit code 0 == invariant holds; nonzero == at least one violation, printed.
"""
import re
import glob
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def module_of(path: str) -> str:
    rel = os.path.relpath(path, ROOT)
    return rel[:-5].replace(os.sep, ".")


def is_tier1(mod: str) -> bool:
    return mod.startswith("RGF.Generative.Core.") or mod.startswith("RGF.Math.")


def load_imports():
    imports = {}
    for f in glob.glob(os.path.join(ROOT, "RGF", "**", "*.lean"), recursive=True):
        mod = module_of(f)
        deps = []
        with open(f, encoding="utf-8") as fh:
            for line in fh:
                m = re.match(r"^import (RGF\.\S+)", line)
                if m:
                    deps.append(m.group(1))
        imports[mod] = deps
    return imports


def main() -> int:
    imports = load_imports()
    violations = []  # (tier1_root, direct_offender, chain)

    for root in imports:
        if not is_tier1(root):
            continue
        # BFS over the transitive import closure of this Tier-1 root.
        seen = set()
        stack = [(root, [root])]
        while stack:
            cur, chain = stack.pop()
            for dep in imports.get(cur, []):
                if dep in seen:
                    continue
                seen.add(dep)
                if not is_tier1(dep):
                    violations.append((root, dep, chain + [dep]))
                else:
                    stack.append((dep, chain + [dep]))

    if violations:
        print("TIER-1 ISOLATION VIOLATION(S) FOUND:\n")
        for root, dep in sorted(set((v[0], v[1]) for v in violations)):
            print(f"  Tier-1 module {root}")
            print(f"    reaches non-Tier-1 module {dep}")
        print("\nExample dependency chains:")
        shown = set()
        for root, dep, chain in violations:
            key = (root, dep)
            if key in shown:
                continue
            shown.add(key)
            print("  " + " -> ".join(chain))
        print(f"\nTotal distinct violating (Tier-1 -> non-Tier-1) edges: "
              f"{len(set((v[0], v[1]) for v in violations))}")
        return 1

    n1 = sum(1 for m in imports if is_tier1(m))
    print(f"Tier-1 isolation check PASSED: {n1} Tier-1 modules; their transitive "
          f"import closure contains no Tier-2/3 module.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
