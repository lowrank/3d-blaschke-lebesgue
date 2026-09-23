"""Rational eight-cap certificates (geometry and inequalities of Hyra).
Float arithmetic proposes integers only. Every accepted inequality and the
volume bound is checked using Fraction or integers. No proposal is trusted.
"""
from fractions import Fraction as Q
from math import sqrt,floor,ceil,comb
from pathlib import Path
import json,time
DEN=10**12
ROUND=10**18

def frac(x):return Q(str(x))
def angle(k,N):return Q(N*N-k*k,N*N+k*k),Q(2*N*k,N*N+k*k)
def step_angle(k,N):
 a=N*N+k*(k-1);return Q(a*a-N*N,a*a+N*N),Q(2*N*a,a*a+N*N)
def step_ok(X,Y,m,cd,sd):
 T=X*X+m;D=4*X*X-T*T;B=Y*cd-X
 return D>=0 and B>0 and Y*Y*D*sd*sd<=T*T*B*B

def gap(w,m,a,b):return a*w**3+b-2*w**3/(w*w+m)
def downward(x):return Q(x.numerator*ROUND//x.denominator,ROUND)
def generate(lo,hi,s0,N=4096):
 lo,hi,s0=map(frac,[lo,hi,s0]);m=1-hi*hi
 eta=1/(2*lo*lo)-1;Tstar=4*eta*eta/(1-eta)-1
 a=2*(s0*s0+3*m)/(3*(s0*s0+m)**2)
 b=2*s0**3/(s0*s0+m)-a*s0**3
 assert m>=Q(5,8) and lo> s0>1-lo and lo*lo>Q(1,3)
 # Candidate search followed by exact validation.
 Y=lo;verts=[];antis=[];cp=Q(1);sp=Q(0);sv=Q(0);sa=Q(0)
 for k in range(1,N):
  ck,sk=angle(k,N)
  if ck*ck-sk*sk<=Tstar:break
  cd,sd=step_angle(k,N);yf=float(Y);mf=float(m);cd_f=float(cd);sd_f=float(sd)
  T=yf*yf+mf;qq=max(0,4*yf*yf-T*T)
  x=yf-yf*sqrt(qq)/T*sd_f
  for _ in range(4):
   T=x*x+mf;qq=4*x*x-T*T
   if qq<=0:break
   z=sqrt(qq);d=T*cd_f-z*sd_f;V=x*T/d
   dp=2*x*cd_f-2*x*(2-T)/z*sd_f
   vp=V*(1/x+2*x/T-dp/d)
   x-=(V-yf)/vp
  num=floor(x*DEN)-1;X=Q(num,DEN)
  if X<=s0:break
  while not step_ok(X,Y,m,cd,sd):
   num-=1;X=Q(num,DEN)
   if X<=s0:break
  if X<=s0:break
  assert X<Y and step_ok(X,Y,m,cd,sd)
  sv=downward(sv+(cp-ck)*gap(X,m,a,b));verts.append(num);Y=X;cp=ck
 cp=Q(1)
 for k in range(1,N):
  ck,sk=angle(k,N)
  if ck*ck-sk*sk<=Tstar:break
  z=-float(lo*ck)+sqrt(float(1-lo*lo*sk*sk));num=ceil(z*DEN)+1;Z=Q(num,DEN)
  while Z+lo*ck<0 or (Z+lo*ck)**2<1-lo*lo*sk*sk:num+=1;Z=Q(num,DEN)
  if Z>s0:break
  sa=downward(sa+(cp-ck)*gap(Z,m,a,b));antis.append(num);cp=ck
 Delta=4*(sv+sa)
 coefficient=(Q(2,3)-4*b+2*Delta)/(3*a-2)
 return dict(lo=str(lo),hi=str(hi),s0=str(s0),N=N,denominator=DEN,w=verts,z=antis,coefficient=str(coefficient))

def verify(data):
 if not __debug__:raise RuntimeError("Verification requires assertions; do not use python -O.")
 lo,hi,s0=map(Q,[data['lo'],data['hi'],data['s0']]);N=data['N'];D=data['denominator'];m=1-hi*hi
 eta=1/(2*lo*lo)-1;Tstar=4*eta*eta/(1-eta)-1
 a=2*(s0*s0+3*m)/(3*(s0*s0+m)**2);b=2*s0**3/(s0*s0+m)-a*s0**3
 assert Q(5,8)<=m and lo> s0>1-lo and lo*lo>Q(1,3) and 3*a-2>0
 sv=Q(0);Y=lo;cp=Q(1)
 assert 0<len(data['w'])<N and 0<len(data['z'])<N
 for k,num in enumerate(data['w'],1):
  ck,sk=angle(k,N);cd,sd=step_angle(k,N);X=Q(num,D)
  assert s0<X<Y and ck*ck-sk*sk>Tstar and step_ok(X,Y,m,cd,sd)
  sv=downward(sv+(cp-ck)*gap(X,m,a,b));cp=ck;Y=X
 sa=Q(0);cp=Q(1);last=Q(0)
 for k,num in enumerate(data['z'],1):
  ck,sk=angle(k,N);Z=Q(num,D)
  assert last<=Z<=s0 and ck*ck-sk*sk>Tstar
  assert Z+lo*ck>=0 and (Z+lo*ck)**2>=1-lo*lo*sk*sk
  sa=downward(sa+(cp-ck)*gap(Z,m,a,b));cp=ck;last=Z
 co=(Q(2,3)-4*b+8*(sv+sa))/(3*a-2)
 assert co==Q(data['coefficient'])
 pi_lower=6*sum((Q(comb(2*k,k),(2*k+1)*2**(4*k+1)) for k in range(40)),Q(0))
 assert co*pi_lower>Q(207,500)
 return dict(lo=str(lo),hi=str(hi),s0=str(s0),N=N,nv=len(data['w']),na=len(data['z']),bound=float(co*pi_lower),coefficient=str(co))

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--generate',action='store_true');ap.add_argument('--output',default=str(Path(__file__).parent/'data'/'cap_data.json'));args=ap.parse_args()
 specs=[('.6','.605','.479322'),('.605','.608','.484581'),('.608','.6085','.4912'),('.6085','.60875','.4928'),('.60875','.60885','.4933'),('.60885','.6089','.4936'),('.6089','.608925','.4937'),('.608925','.60894','.4938'),('.60894','.60895','.4938')]
 start=time.time()
 if args.generate:
  data=[]
  for lo,hi,s in specs:
   v=generate(lo,hi,s);data.append(v);print(verify(v),flush=True)
  Path(args.output).write_text(json.dumps(data,separators=(',',':')))
 else:data=json.loads(Path(args.output).read_text())
 reports=[verify(v) for v in data]
 assert Q(data[0]['lo'])==Q(3,5) and Q(data[-1]['hi'])==Q(12179,20000)
 for a,b in zip(data[:-1],data[1:]):assert Q(a['hi'])==Q(b['lo'])
 Path(args.output).with_name('cap_report.json').write_text(json.dumps(dict(status='PASS',seconds=time.time()-start,rows=reports),indent=2))
 print('PASS all',len(reports),'seconds',time.time()-start)
