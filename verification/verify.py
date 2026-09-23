#!/usr/bin/env python3
"""Recompute every finite premise of the 0.4144 bound.
Requires Python 3 and a C++17 compiler with signed 128-bit integers (g++).
No stored numerical bound is trusted. See README.md and the mathematical note.
"""
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path

def main():
 if not __debug__:raise RuntimeError('Do not use python -O for verification.')
 p=argparse.ArgumentParser();p.add_argument('--cpp-bits',type=int,choices=[48,52],default=48);p.add_argument('--interval-bits',type=int,choices=[128,192],default=128);p.add_argument('--output');args=p.parse_args()
 root=Path(__file__).resolve().parent;os.chdir(root)
 out=Path(args.output or f'recheck_{args.cpp_bits}_{args.interval_bits}').resolve();out.mkdir(parents=True,exist_ok=True)
 os.environ['BLASCHKE_BITS']=str(args.interval_bits)
 start=time.time();exe=out/'projective_verifier';src=root/'projective_certificate.cpp'
 cmd=['g++','-std=c++17','-O2','-fno-fast-math','-Wall','-Wextra',f'-DPRECISION={args.cpp_bits}',str(src),'-o',str(exe)]
 subprocess.run(cmd,check=True)
 leaves=out/'projective_leaves.txt'
 with (out/'projective_report.json').open('w') as stdout,(out/'projective_progress.log').open('w') as stderr:
  subprocess.run([str(exe),'verify',str(leaves),'192','64'],stdout=stdout,stderr=stderr,check=True)
 proj=json.loads((out/'projective_report.json').read_text());assert proj['status']=='PASS'
 from verify_auxiliary import constants,check_cover,radial
 const=constants();cover=check_cover(leaves)
 assert cover['certified_leaves']==proj['leaves'] and cover['outside_leaves']==proj['outside_leaves']
 (out/'geometry_and_cover.json').write_text(json.dumps({'constants':const,'cover':cover},indent=2))
 from verify_weighted_hull import check
 hull=check(out)
 rad=radial(root/'data/radial_candidates.json',out)
 from verify_regular_endpoint import check as check_regular
 regular=check_regular(out)
 files=['projective_certificate.cpp','verify.py','verify_auxiliary.py','verify_weighted_hull.py','verify_regular_endpoint.py','combined_hull.py','interval.py','analytic_functions.py','clipped_hull.py','cap_certificate.py','data/radial_candidates.json']
 hashes={f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files}
 from fractions import Fraction as Q
 lower=min(Q(hull['lower_bound']),Q(rad['minimum']),Q(rad['analytic_small_radius_bound']))
 assert lower>Q(259,625)
 report={'status':'PASS','target':'259/625','target_display':0.4144,'projective':proj,'geometry':const,'cover':cover,'hull_lower':hull['lower_bound'],'radial_lower':rad['minimum'],'global_lower':str(lower),'global_lower_display':float(lower),'regular_tetrahedron_bound':regular['regular_lower_bound'],'cpp_precision':args.cpp_bits,'interval_precision':args.interval_bits,'source_sha256':hashes,'elapsed_seconds':time.time()-start,'scope':'This certifies 0.4144, not the sharp Meissner conjecture.'}
 (out/'complete_report.json').write_text(json.dumps(report,indent=2));print(json.dumps({k:v for k,v in report.items() if k not in ['source_sha256','geometry','projective']},indent=2))
 # Executables are disposable build products, not certificate inputs.
 exe.unlink()
if __name__=='__main__':main()
