#!/usr/bin/env python3
"""Assemble the final theorem, refusing to repeat missing kernel computations."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def main():
    modules = [f'BlaschkeLebesgue.Certificates.Generated.ProjectiveKernel.Box{i:03d}' for i in range(584)]
    for kind in ['ClippedHullKernel', 'ClippedHullSecantKernel']:
        modules += [f'BlaschkeLebesgue.Certificates.Generated.{kind}.Strip{i:02d}' for i in range(32)]
    run('lake', '--no-build', 'build', *modules)
    run('lake', 'build', 'BlaschkeLebesgue', 'BlaschkeLebesgue.Final')
    run('lake', 'env', 'lean', 'FinalAxiomAudit.lean')


if __name__ == '__main__':
    main()
