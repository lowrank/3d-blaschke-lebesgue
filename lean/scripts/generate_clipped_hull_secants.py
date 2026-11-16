#!/usr/bin/env python3
"""Generate the 512 proposed kernel secant checks in 32 groups."""
from pathlib import Path
import argparse


def source(i):
    namespace = f"BlaschkeLebesgue.Certificates.ClippedHull.SecantKernel.Strip{i:02d}"
    header = f'''module

public import BlaschkeLebesgue.Certificates.ClippedHullSecantComputation

/-! # Kernel secant checks for buckets {16*i} through {16*i+15} -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace {namespace}

'''
    for j in range(16*i, 16*i+16):
        header += f"theorem bucket{j:03d} : secantCheck 128 64 {j} 512 = true := by decide +kernel\n"
    return header + f"\nend {namespace}\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1] / "BlaschkeLebesgue/Certificates/Generated/ClippedHullSecantKernel"
    root.mkdir(parents=True, exist_ok=True)
    for i in range(32):
        path = root / f"Strip{i:02d}.lean"
        expected = source(i)
        if args.check:
            if not path.exists() or path.read_text() != expected:
                raise SystemExit(f"Stale generated source: {path}")
        else:
            path.write_text(expected)


if __name__ == "__main__":
    main()
