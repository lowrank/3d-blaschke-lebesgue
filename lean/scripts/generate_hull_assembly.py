#!/usr/bin/env python3
"""Assemble checked hull declarations without recomputing certificate arithmetic."""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1] / 'BlaschkeLebesgue/Certificates/Generated'


def cases(terms):
    term = 'fun j ↦ Fin.elim0 j'
    for entry in reversed(terms):
        term = f'Fin.cases {entry} ({term})'
    return term


def sources():
    result = {}
    for kind, folder, namespace, count in [
        ('Sign', 'ClippedHullKernel', 'Kernel', 100),
        ('Secant', 'ClippedHullSecantKernel', 'SecantKernel', 16),
    ]:
        for i in range(32):
            module = f'BlaschkeLebesgue.Certificates.ClippedHull.Assembly.{kind}{i:02d}'
            proposition = (f'∀ j : Fin 100, edgeSignCheck 128 64 {i} j 32 100 = true' if kind == 'Sign'
                else f'∀ j : Fin 16, secantCheck 128 64 ({16*i} + j) 512 = true')
            terms = ([f'{namespace}.Strip{i:02d}.cell{j:03d}' for j in range(100)] if kind == 'Sign'
                else [f'{namespace}.Strip{i:02d}.bucket{16*i+j:03d}' for j in range(16)])
            result[ROOT / f'ClippedHullAssembly/{kind}{i:02d}.lean'] = f'''module
public import BlaschkeLebesgue.Certificates.Generated.{folder}.Strip{i:02d}
public section
namespace {module}
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem verified : {proposition} :=
  {cases(terms)}
end {module}
'''
    imports = '\n'.join(f'public import BlaschkeLebesgue.Certificates.Generated.ClippedHullAssembly.Sign{i:02d}' for i in range(32))
    result[ROOT / 'HullSignSuite.lean'] = f'''module
{imports}
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem all_edge_checks : ∀ i : Fin 32, ∀ j : Fin 100, edgeSignCheck 128 64 i j 32 100 = true :=
  {cases([f'Assembly.Sign{i:02d}.verified' for i in range(32)])}
theorem all_baseline_checks : ∀ i : Fin 32, baselineSignCheck 128 64 i 32 = true :=
  {cases([f'Kernel.Strip{i:02d}.baseline' for i in range(32)])}
end BlaschkeLebesgue.Certificates.ClippedHull
'''
    # A direct 512-case eliminator avoids an extra quotient/remainder index theorem.
    imports = '\n'.join(f'public import BlaschkeLebesgue.Certificates.Generated.ClippedHullSecantKernel.Strip{i:02d}' for i in range(32))
    result[ROOT / 'HullSecantSuite.lean'] = f'''module
{imports}
public section
namespace BlaschkeLebesgue.Certificates.ClippedHull
set_option maxRecDepth 20000
set_option maxHeartbeats 0
theorem all_secant_checks : ∀ i : Fin 512, secantCheck 128 64 i 512 = true :=
  {cases([f'SecantKernel.Strip{i//16:02d}.bucket{i:03d}' for i in range(512)])}
end BlaschkeLebesgue.Certificates.ClippedHull
'''
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for path, text in sources().items():
        if args.check:
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f'Stale assembly source: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
