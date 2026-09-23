"""Exact-interval assembly of the clipped-hull and affine completion bound."""
from combined_hull import *
from pathlib import Path
import json,time,argparse
CUTOFF=Q(60849,100000)
ZLO=CUTOFF**2;ZHI=Q(3,8);AMAX=Q(2,25);TARGET=Q(259,625)
C0=Q(153,100000);CA=Q(-601,100000);CB=Q(317,20000)

def check(out,nr=32,ne=100,nlevels=512):
 if not __debug__:raise RuntimeError('Do not use python -O.')
 out=Path(out);out.mkdir(parents=True,exist_ok=True);start=time.time();boxes=[]
 for i in range(nr):
  z0=ZLO+(ZHI-ZLO)*Q(i,nr);z1=ZLO+(ZHI-ZLO)*Q(i+1,nr);R=I(z0,z1).sqrt()
  bas=combined_baseline(J(R,1));assert bas.d.lo>0,('baseline derivative',i,bas.d.show())
  for j in range(ne):
   x=I(1-AMAX*Q(j+1,ne),1-AMAX*Q(j,ne))
   dx=combined_dx(J(R),J(x,1));dxR=combined_dx(J(R,1),J(x))
   assert dx.v.hi<0,('edge monotone',i,j,dx.v.show())
   assert dx.d.hi<0,('edge concave',i,j,dx.d.show())
   assert dxR.d.lo>0,('decreases in radius',i,j,dxR.d.show())
   boxes.append({'i':i,'j':j,'dx':dx.v.bounds(),'dxx':dx.d.bounds(),'dxR':dxR.d.bounds()})
  if i%8==0:print('derivative strips',i+1,'/',nr,flush=True)
 levels=[]
 for i in range(nlevels):
  z0=ZLO+(ZHI-ZLO)*Q(i,nlevels);z1=ZLO+(ZHI-ZLO)*Q(i+1,nlevels)
  d0=ZHI-z0;d1=ZHI-z1;amax=16*d0/(1-8*d0);assert 0<amax<AMAX
  r0=I(z0).sqrt();r1=I(z1).sqrt()
  slope=(combined_edge(r1,amax).v-combined_edge(r1,0).v)/amax;assert slope.lo>0
  base=combined_baseline(r0).v+16*d1*slope
  completion=I(Q(8,23))*(3*C0+(CA+2*CB)*16*d1)
  val=base+completion
  assert (val-TARGET).lo>0,('global near-bound',i,val.show())
  levels.append({'index':i,'R2lo':str(z0),'R2hi':str(z1),'edge_budget':str(amax),'base':base.bounds(),'bound':val.bounds()})
 low=min(Q(l['bound'][0]) for l in levels)
 report={'status':'PASS','bits':__import__('interval').BITS,'cutoff':str(CUTOFF),'target':str(TARGET),'AMAX':str(AMAX),'derivative_boxes':nr*ne,'radius_intervals':nlevels,'lower_bound':str(low),'lower_bound_display':float(low),'elapsed_seconds':time.time()-start,'boxes':boxes,'levels':levels}
 (out/'weighted_hull_report.json').write_text(json.dumps(report,indent=2))
 print({k:v for k,v in report.items() if k not in ['boxes','levels']},flush=True)
 return report
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',default='reports128');p.add_argument('--nr',type=int,default=32);p.add_argument('--ne',type=int,default=100);p.add_argument('--nlevels',type=int,default=512);a=p.parse_args();check(a.output,a.nr,a.ne,a.nlevels)
