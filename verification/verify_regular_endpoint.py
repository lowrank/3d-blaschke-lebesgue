"""Exact-interval check of the regular-tetrahedron corollary and diagnostics."""
from pathlib import Path
import json
from interval import I,J,Q
from analytic_functions import PI
from clipped_hull import acos

def check(out):
 alpha=acos(J(Q(1,3))).v
 vm=PI/12*(8-3*I(3).sqrt()*alpha)
 vr=8*PI/3+I(2).sqrt()/4-27*alpha/4
 vd=2*vm-vr
 lower=(47*vd-vr)/46+Q(459,287500)
 assert (lower-Q(4190589,10000000)).lo>0
 assert (vm-lower).lo>0
 hyra=PI*Q(130838246407123,10**15)
 rel=(vm-Q(259,625))/vm*100
 removed=(I(Q(259,625))-Q(207,500))/(vm-Q(207,500))*100
 cumul=(I(Q(259,625))-hyra)/(vm-hyra)*100
 result={'status':'PASS','bits':__import__('interval').BITS,'Meissner_volume':vm.bounds(),'regular_outer_volume':vr.bounds(),'regular_inner_volume':vd.bounds(),'regular_lower_bound':lower.bounds(),'regular_lower_bound_display':lower.show(),'regular_missing_volume':(vm-lower).bounds(),'global_relative_gap_percent':rel.show(),'previous_remaining_gap_removed_percent':removed.show(),'Hyra_remaining_gap_removed_percent':cumul.show()}
 out=Path(out);out.mkdir(parents=True,exist_ok=True);(out/'regular_endpoint_report.json').write_text(json.dumps(result,indent=2));return result
if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--output',default='reports128');a=p.parse_args();print(check(a.output))
