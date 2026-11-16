#!/usr/bin/env python3
"""Collect live certificate artifacts and assemble only complete verified suites.

This watcher never restarts a CI computation or builds missing kernel modules.
It exits on a failed CI run or a failed restore/build/audit. It makes no commits.
"""
import argparse
import json
import os
import shutil
import subprocess
import time
from collections import Counter
from pathlib import Path

import assemble_final
import projective_ci
import restore_hull_artifacts

ROOT = Path(__file__).resolve().parents[1]
REPO = 'lowrank/3d-blaschke-lebesgue'
RUNS = {'projective': '43884585133', 'signs': '43923248067', 'secants': '43924066736'}
PREFIXES = {'projective': 'projective-', 'signs': 'clipped-hull-strip-',
            'secants': 'clipped-hull-secants-strip-'}


def gh_json(*args):
    return json.loads(subprocess.check_output(['gh', *args], cwd=ROOT, text=True))


def run(*args):
    subprocess.run(args, cwd=ROOT, check=True)


def collect(kind, run_id, destination, restored):
    data = gh_json('api', f'repos/{REPO}/actions/runs/{run_id}/artifacts?per_page=100')
    archives = []
    for item in data['artifacts']:
        name = item['name']
        if not name.startswith(PREFIXES[kind]) or item['expired']:
            continue
        if name in restored[kind]:
            continue
        target = destination / kind / name
        if not target.exists():
            temporary = target.with_name('.partial-' + name)
            if temporary.exists():
                shutil.rmtree(temporary)
            temporary.parent.mkdir(parents=True, exist_ok=True)
            run('gh', 'run', 'download', run_id, '-R', REPO, '-n', name, '-D', str(temporary))
            temporary.replace(target)
        if kind == 'projective':
            contents = list(target.glob('shard-*.tar.gz'))
            if len(contents) != 1:
                raise RuntimeError(f'Expected one projective shard archive in {target}')
            archives.extend(contents)
        else:
            restore_hull_artifacts.restore(target)
        restored[kind].add(name)
    if archives:
        projective_ci.unpack(archives)
        plan = json.loads(projective_ci.PLAN.read_text())
        indices = []
        for archive in archives:
            shard_id = archive.name.removeprefix('shard-').removesuffix('.tar.gz')
            shard = next(item for item in plan if item['id'] == shard_id)
            indices.extend(shard['boxes'])
        indices = sorted(set(indices))
        print(f'Assembling {len(indices)} restored projective boxes independently', flush=True)
        kernels = [f'BlaschkeLebesgue.Certificates.Generated.ProjectiveKernel.Box{i:03d}' for i in indices]
        modules = [f'BlaschkeLebesgue.Certificates.Generated.ProjectiveBoxes.Box{i:03d}' for i in indices]
        run('lake', '--no-build', 'build', *kernels)
        run('lake', 'build', *modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--downloads', type=Path, required=True)
    parser.add_argument('--interval', type=int, default=60)
    parser.add_argument('--once', action='store_true')
    args = parser.parse_args()
    if args.interval < 15:
        parser.error('--interval must be at least 15 seconds')
    os.environ.setdefault('LEAN_NUM_THREADS', '2')
    restored = {kind: set() for kind in RUNS}
    audited = set()
    last = {}
    while True:
        results = {}
        for kind, run_id in RUNS.items():
            result = gh_json('run', 'view', run_id, '-R', REPO, '--json', 'status,conclusion,jobs')
            counts = dict(Counter((j['status'] + ':' + (j['conclusion'] or '')) for j in result['jobs']))
            state = (result['status'], result['conclusion'], counts)
            if state != last.get(kind):
                print(kind, run_id, state, flush=True)
                last[kind] = state
            if result['status'] == 'completed' and result['conclusion'] != 'success':
                raise RuntimeError(f'{kind} run {run_id} ended with {result["conclusion"]}')
            results[kind] = result
            collect(kind, run_id, args.downloads.resolve(), restored)
        for kind, suite, audit in [('signs', 'HullSignSuite', 'HullSignAxiomAudit.lean'),
                                    ('secants', 'HullSecantSuite', 'HullSecantAxiomAudit.lean')]:
            if results[kind]['conclusion'] == 'success' and kind not in audited:
                folder = 'ClippedHullKernel' if kind == 'signs' else 'ClippedHullSecantKernel'
                modules = [f'BlaschkeLebesgue.Certificates.Generated.{folder}.Strip{i:02d}' for i in range(32)]
                run('lake', '--no-build', 'build', *modules)
                run('lake', 'build', f'BlaschkeLebesgue.Certificates.Generated.{suite}')
                run('lake', 'env', 'lean', audit)
                audited.add(kind)
        if all(result['conclusion'] == 'success' for result in results.values()):
            assemble_final.main()
            print('All certificate suites and the final local theorem audit passed.', flush=True)
            return
        if args.once:
            return
        time.sleep(args.interval)


if __name__ == '__main__':
    main()
