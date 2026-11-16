#!/usr/bin/env python3
"""Generate the proposed kernel sign checks; compilation supplies the proof."""
from pathlib import Path
import argparse


def source(i):
    namespace = f"BlaschkeLebesgue.Certificates.ClippedHull.Kernel.Strip{i:02d}"
    header = f'''module

public import BlaschkeLebesgue.Certificates.ClippedHullCheckComputation

/-! # Kernel sign checks for clipped-hull radius strip {i} -/

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace {namespace}

'''
    header += f"theorem baseline : baselineSignCheck 128 64 {i} 32 = true := by decide +kernel\n\n"
    for j in range(100):
        header += f"theorem cell{j:03d} : edgeSignCheck 128 64 {i} {j} 32 100 = true := by decide +kernel\n"
    return header + f"\nend {namespace}\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1] / "BlaschkeLebesgue/Certificates/Generated/ClippedHullKernel"
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
