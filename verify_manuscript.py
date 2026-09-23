#!/usr/bin/env python3
"""Audit the manuscript's compressed constants and packaged report provenance.

This is NOT a replacement for verification/verify.py: it reads recorded reports.
The full numerical certificates must be recomputed with that program.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def require(value: bool, message: str) -> None:
    if not value:
        raise RuntimeError(message)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'manuscript_audit.json')
    args = parser.parse_args()
    target = F(259, 625)
    compressed = F(4144109, 10000000)
    require(compressed > target, 'The compressed bound does not exceed the target.')
    runs = []
    for name, cb, ib in [('run_48_128', 48, 128), ('run_52_192', 52, 192)]:
        report = json.loads((ROOT / 'verification/reports' / name / 'complete_report.json').read_text())
        require(report['status'] == 'PASS', 'Recorded run did not pass.')
        require(report['cpp_precision'] == cb and report['interval_precision'] == ib,
                'Unexpected arithmetic precision.')
        require(report['projective']['leaves'] == 584, 'Unexpected integral cover size.')
        require(report['cover']['certified_leaves'] == 584, 'Unexpected independent cover count.')
        require(F(report['projective']['least_margin']) > 0, 'Nonpositive margin.')
        require(F(report['hull_lower']) > F(4144467, 10000000), 'Hull display not conservative.')
        require(F(report['global_lower']) > compressed, 'Compressed lower bound is not justified.')
        for relative, expected in report['source_sha256'].items():
            actual = hashlib.sha256((ROOT / 'verification' / relative).read_bytes()).hexdigest()
            require(actual == expected, f'Source hash mismatch: {relative}')
        runs.append({'name': name, 'precisions': [cb, ib],
                     'exact_global_lower': report['global_lower'],
                     'compressed_lower': str(compressed),
                     'hashed_inputs': len(report['source_sha256']), 'status': 'PASS'})
    source = (ROOT / 'volume_bound_04144.tex').read_text()
    require('\\cite{Previous}' not in source and '\\bibitem{Previous}' not in source,
            'Working-note dependency present.')
    require(all(ord(c) >= 32 or c in '\n\r\t' for c in source), 'Unexpected control character.')
    result = {'status': 'PASS', 'scope': 'Recorded report provenance and manuscript constants only; '
              'not a new numerical integration run.', 'target': str(target),
              'conservative_margin_above_target': str(compressed - target), 'runs': runs}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
