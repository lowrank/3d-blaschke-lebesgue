"""Exact geometric constants, convexity inequalities and partition verification."""
from fractions import Fraction as Q
from pathlib import Path
import json

def constants():
 from interval import I
 A=Q(2,25);c=Q(1,25)
 etasq=A*A/(16*(1-A)*(1-c*c)*(Q(1,8)-A/16))
 assert etasq<Q(1,256)
 # T_min is tan(arccos(5/6)-arcsin(1/16)).
 s11=I(11).sqrt();s255=I(255).sqrt()
 tlo=(s11*s255-5)/(5*s255+s11)
 assert (tlo-Q(1,2)).lo>0
 assert (I(Q(3,4))-1/I(2).sqrt()).lo>0
 assert 3*A*A<4*(1-A)**2
 circ=(I(Q(3,8)).sqrt()*I(1+A/2).sqrt()+A/(4*I(2).sqrt()*I(1-A).sqrt()))
 assert circ.hi<I(1).lo
 assert 2-6*Q(3,8)+Q(3,8)*(1-A)>0
 # Polynomial proof of the convexity lemma: B1 is bilinear.
 B1=lambda u,v:6-Q(15,4)*(u+v)+2*u*v
 assert min(B1(u,v) for u in [0,1] for v in [0,1])==Q(1,2)
 # The u-coefficient of B1/2-B2 decreases in v and is negative at 4/5.
 coef=lambda v:Q(15,8)-3*v+Q(3,4)*v*v
 assert coef(Q(4,5))<0
 assert -3+Q(3,2)<0
 rem=lambda v:(-9+21*v-10*v*v)/8
 assert min(rem(Q(4,5)),rem(Q(1)))==Q(7,40)
 assert Q(47,32)-4*Q(1,5)>0
 assert Q(47,32)-1>0
 # Feasibility of the circumradius split and its deficit budget.
 cutoff=Q(60849,100000);d=Q(3,8)-cutoff**2
 assert 16*d/(1-8*d)<A and cutoff**2>Q(1,3)
 assert Q(-601,100000)+2*Q(317,20000)==Q(2569,100000)>0
 return {'status':'PASS','Amax':str(A),'eta_squared_upper':str(etasq),'projective_T_lower':tlo.bounds(),'circumradius_upper':circ.bounds(),'convexity_B1_min':str(Q(1,2)),'convexity_remainder_min':str(Q(7,40)),'cutoff':str(cutoff)}

def check_cover(path):
 rows=[]
 for line in Path(path).read_text().splitlines():
  r=list(map(int,line.split()));assert len(r)==10 and r[4]>0;rows.append(r)
 keys={(r[0],r[1],r[2],r[3]) for r in rows};assert len(keys)==len(rows)
 used=set();outside=0
 def visit(i,j,da,db):
  nonlocal outside
  if i*(1<<db)+j*(1<<da)>(1<<(da+db)):
   outside+=1;return
  key=(i,j,da,db)
  if key in keys:used.add(key);return
  assert max(da,db)<=17,('missing region',key)
  if da<=db:visit(2*i,j,da+1,db);visit(2*i+1,j,da+1,db)
  else:visit(i,2*j,da,db+1);visit(i,2*j+1,da,db+1)
 for i in range(32):
  for j in range(32):visit(i,j,5,5)
 assert keys==used
 return {'status':'PASS','certified_leaves':len(rows),'outside_leaves':outside,'maximum_a_depth':max(r[2] for r in rows),'maximum_b_depth':max(r[3] for r in rows)}

def radial(data_path,out):
 from cap_certificate import verify
 from math import comb
 pi40=6*sum((Q(comb(2*k,k),(2*k+1)*2**(4*k+1)) for k in range(40)),Q(0))
 data=json.loads(Path(data_path).read_text());rows=[];target=Q(259,625)
 assert Q(data[0]['lo'])==Q(3,5) and Q(data[-1]['hi'])==Q(60849,100000)
 for a,b in zip(data,data[1:]):assert Q(a['hi'])==Q(b['lo'])
 for d in data:
  report=verify(d);bound=Q(report['coefficient'])*pi40;assert bound>target
  report['exact_lower_bound']=str(bound);rows.append(report)
 analytic=Q(76439431,575385750)*pi40;assert analytic>target
 low=min(Q(r['exact_lower_bound']) for r in rows)
 result={'status':'PASS','rows':rows,'minimum':str(low),'minimum_display':float(low),'analytic_small_radius_bound':str(analytic),'target':str(target)}
 Path(out).mkdir(parents=True,exist_ok=True);(Path(out)/'radial_report.json').write_text(json.dumps(result,indent=2));return result

if __name__=='__main__':
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--output',default='reports128');p.add_argument('--cover',default='reports/projective_leaves48.txt');a=p.parse_args();out=Path(a.output);out.mkdir(exist_ok=True,parents=True)
 res={'constants':constants(),'cover':check_cover(a.cover)};rad=radial('data/radial_candidates.json',out);res['radial_minimum']=rad['minimum'];(out/'auxiliary_report.json').write_text(json.dumps(res,indent=2));print(res)
