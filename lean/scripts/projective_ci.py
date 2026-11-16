#!/usr/bin/env python3
"""Build certificate shards serially and transfer their checked Lake artifacts."""

import argparse
import json
import os
import re
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
PLAN = ROOT / "data/projective_shards.json"
MODULE = "BlaschkeLebesgue.Certificates.Generated.ProjectiveKernel"
REL = Path("BlaschkeLebesgue/Certificates/Generated/ProjectiveKernel")
LIB = Path(".lake/build/lib/lean") / REL
IR = Path(".lake/build/ir") / REL
CACHE_PREFIX = Path(".lake/artifact-cache/artifacts")


def run(*args):
    subprocess.run(args,cwd=ROOT,check=True)


def cache_dir():
    configured = os.environ.get("LAKE_CACHE_DIR")
    if configured:
        return Path(configured).resolve()
    value = subprocess.check_output(["lake","env","printenv","LAKE_CACHE_DIR"],cwd=ROOT,text=True).strip()
    if not value:
        raise RuntimeError("Lake's artifact cache must be enabled")
    return Path(value)


def output_names(value):
    if isinstance(value,str) and re.fullmatch(r"[0-9a-f]{16}\.[A-Za-z.]+",value):
        yield value
    elif isinstance(value,list):
        for entry in value:
            yield from output_names(entry)
    elif isinstance(value,dict):
        for entry in value.values():
            yield from output_names(entry)


def pack(shard, destination):
    cache = cache_dir()
    paths = {}
    complete = []
    for index in shard["boxes"]:
        name = f"Box{index:03d}"
        trace = ROOT / LIB / f"{name}.trace"
        if not trace.exists():
            continue
        info = json.loads(trace.read_text())
        # A trace is written only after Lean finishes checking the module.
        for folder in (LIB,IR):
            for path in (ROOT/folder).glob(name+".*"):
                if path.is_file():
                    paths[str(path.relative_to(ROOT))] = path
        for artifact in output_names(info["outputs"]):
            path = cache / "artifacts" / artifact
            if not path.is_file():
                raise RuntimeError(f"Missing compiled output: {path}")
            paths[str(CACHE_PREFIX/artifact)] = path
        complete.append(index)
    destination.parent.mkdir(parents=True,exist_ok=True)
    temporary = destination.with_suffix(destination.suffix+".tmp")
    with tarfile.open(temporary,"w:gz",dereference=True) as archive:
        for name,path in sorted(paths.items()):
            archive.add(path,arcname=name,recursive=False)
    temporary.replace(destination)
    print(f"Packed {len(complete)}/{len(shard['boxes'])} completed kernel modules into {destination}",flush=True)


def unpack(archives):
    cache = cache_dir()
    for source in archives:
        with tarfile.open(source,"r:gz") as archive:
            for member in archive:
                name = PurePosixPath(member.name)
                if name.is_absolute() or ".." in name.parts or not member.isfile():
                    raise RuntimeError(f"Unexpected archive member: {name}")
                path = Path(name)
                if path.is_relative_to(CACHE_PREFIX):
                    target = cache / "artifacts" / path.relative_to(CACHE_PREFIX)
                    if target.exists():
                        continue
                elif path.is_relative_to(LIB) or path.is_relative_to(IR):
                    target = ROOT / path
                else:
                    raise RuntimeError(f"Unexpected archive path: {name}")
                target.parent.mkdir(parents=True,exist_ok=True)
                # Replace rather than truncate files that may share a cache inode.
                with tempfile.NamedTemporaryFile(dir=target.parent,delete=False) as output:
                    temp = Path(output.name)
                    try:
                        stream = archive.extractfile(member)
                        assert stream is not None
                        with stream:
                            shutil.copyfileobj(stream,output)
                    except BaseException:
                        temp.unlink(missing_ok=True)
                        raise
                temp.chmod(member.mode)
                os.utime(temp,(member.mtime,member.mtime))
                temp.replace(target)
        print(f"Restored {source}",flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command",required=True)
    commands.add_parser("matrix")
    build = commands.add_parser("build")
    build.add_argument("shard")
    packing = commands.add_parser("pack")
    packing.add_argument("shard")
    packing.add_argument("destination",type=Path)
    unpacking = commands.add_parser("unpack")
    unpacking.add_argument("archives",nargs="+",type=Path)
    commands.add_parser("assemble")
    args = parser.parse_args()
    plan = json.loads(PLAN.read_text())
    if args.command == "matrix":
        print(json.dumps({"shard":[x["id"] for x in plan]},separators=(",",":")))
    elif args.command == "unpack":
        unpack(args.archives)
    elif args.command == "assemble":
        modules = [f"{MODULE}.Box{i:03d}" for i in range(584)]
        # Fail promptly if a shard is missing or stale; do not accidentally
        # start hundreds of expensive kernel jobs in the assembly runner.
        run("lake","--no-build","build",*modules)
        run("lake","build","BlaschkeLebesgue.Certificates.Generated.ProjectiveSuite")
        run("lake","env","lean","ProjectiveAxiomAudit.lean")
    else:
        shard = next(x for x in plan if x["id"] == args.shard)
        if args.command == "pack":
            pack(shard,args.destination)
        else:
            for index in shard["boxes"]:
                print(f"Checking projective box {index} in shard {args.shard}",flush=True)
                run("lake","build",f"{MODULE}.Box{index:03d}")


if __name__ == "__main__":
    main()
