#!/usr/bin/env python3
"""Restore downloaded hull build artifacts without truncating shared cache files."""
import argparse
import functools
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def atomic_copy(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as output:
        temp = Path(output.name)
        try:
            with source.open('rb') as stream:
                shutil.copyfileobj(stream, output)
        except BaseException:
            temp.unlink(missing_ok=True)
            raise
    shutil.copystat(source, temp)
    temp.replace(target)


def output_names(obj):
    if isinstance(obj, str) and re.fullmatch(r'[0-9a-f]{16}\.[A-Za-z.]+', obj):
        yield obj
    elif isinstance(obj, dict):
        for item in obj.values():
            yield from output_names(item)
    elif isinstance(obj, list):
        for item in obj:
            yield from output_names(item)


@functools.cache
def artifact_cache():
    cache = os.environ.get('LAKE_CACHE_DIR')
    if not cache:
        cache = subprocess.check_output(['lake', 'env', 'printenv', 'LAKE_CACHE_DIR'], cwd=ROOT, text=True).strip()
    if not cache:
        raise RuntimeError('Lake artifact cache is required')
    return Path(cache) / 'artifacts'


def restore(source):
    cache = artifact_cache()
    count = 0
    for kind in ['ClippedHullKernel', 'ClippedHullSecantKernel']:
        folder = source / 'lib/lean/BlaschkeLebesgue/Certificates/Generated' / kind
        for trace in sorted(folder.glob('Strip*.trace')):
            stem = trace.stem
            data = json.loads(trace.read_text())
            for name in output_names(data['outputs']):
                suffix = name.split('.', 1)[1]
                candidate = trace.parent / (stem + '.' + suffix)
                if not candidate.is_file():
                    candidate = source / 'ir/BlaschkeLebesgue/Certificates/Generated' / kind / (stem + '.' + suffix)
                if not candidate.is_file():
                    raise RuntimeError(f'Missing checked output {name}')
                if not (cache / name).exists():
                    atomic_copy(candidate, cache / name)
            for area in ['lib/lean', 'ir']:
                relative = Path(area) / 'BlaschkeLebesgue/Certificates/Generated' / kind
                for path in (source / relative).glob(stem + '.*'):
                    if path.is_file():
                        atomic_copy(path, ROOT / '.lake/build' / relative / path.name)
            count += 1
    if not count:
        raise RuntimeError(f'No hull modules found in {source}')
    print(f'Restored {count} checked hull modules from {source}', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directories', type=Path, nargs='+')
    for directory in parser.parse_args().directories:
        restore(directory.resolve())
