"""Fixed-dyadic outward interval arithmetic and scalar derivative jets.
Only Python integer arithmetic and exact Fraction comparisons support bounds.
"""
from fractions import Fraction as Q
from math import isqrt,comb,factorial
import json,time,os
from pathlib import Path
import hashlib
BITS=int(os.environ.get('BLASCHKE_BITS','128'))
if BITS < 64:
 raise ValueError('BLASCHKE_BITS must be at least 64')
SCALE=1<<BITS

def flq(x):return x.numerator*SCALE//x.denominator
def ceq(x):return -((-x.numerator*SCALE)//x.denominator)
class I:
 __slots__=('lo','hi')
 def __init__(self,a=0,b=None,raw=False):
  if raw:self.lo,self.hi=a,b
  else:
   a=Q(a);b=a if b is None else Q(b);self.lo,self.hi=flq(a),ceq(b)
  if self.lo>self.hi:raise ArithmeticError('empty interval')
 @staticmethod
 def cv(a):return a if isinstance(a,I) else I(a)
 def __add__(self,b):
  b=I.cv(b);return I(self.lo+b.lo,self.hi+b.hi,True)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo,True)
 def __sub__(self,b):return self+-I.cv(b)
 def __rsub__(self,b):return I.cv(b)+-self
 def __mul__(self,b):
  b=I.cv(b);t=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
  return I(min(t)//SCALE,-((-max(t))//SCALE),True)
 __rmul__=__mul__
 def inv(self):
  if self.lo<=0<=self.hi:raise ArithmeticError('zero denominator')
  # reciprocal is decreasing on either sign interval
  return I(SCALE*SCALE//self.hi,-((-SCALE*SCALE)//self.lo),True)
 def __truediv__(self,b):return self*I.cv(b).inv()
 def __rtruediv__(self,b):return I.cv(b)*self.inv()
 def sqrt(self):
  if self.lo<0:raise ArithmeticError('negative radicand')
  a=isqrt(self.lo*SCALE);b=isqrt(self.hi*SCALE)
  if b*b<self.hi*SCALE:b+=1
  return I(a,b,True)
 def sq(self):
  if self.lo>=0:return self*self
  if self.hi<=0:return (-self)*(-self)
  return I(0,-((-max(self.lo*self.lo,self.hi*self.hi))//SCALE),True)
 def __pow__(self,n):
  if n<0:return (self.inv())**(-n)
  r=I(1);x=self
  while n:
   if n&1:r=r*x
   x=x.sq();n>>=1
  return r
 def bounds(self):return [str(Q(self.lo,SCALE)),str(Q(self.hi,SCALE))]
 def show(self):return [float(Q(self.lo,SCALE)),float(Q(self.hi,SCALE))]

class J:
 __slots__=('v','d','dd')
 def __init__(self,v,d=0,dd=0):self.v,self.d,self.dd=I.cv(v),I.cv(d),I.cv(dd)
 @staticmethod
 def cv(a):return a if isinstance(a,J) else J(a)
 def __add__(self,b):
  b=J.cv(b);return J(self.v+b.v,self.d+b.d,self.dd+b.dd)
 __radd__=__add__
 def __neg__(self):return J(-self.v,-self.d,-self.dd)
 def __sub__(self,b):return self+-J.cv(b)
 def __rsub__(self,b):return J.cv(b)+-self
 def __mul__(self,b):
  b=J.cv(b);return J(self.v*b.v,self.d*b.v+self.v*b.d,self.dd*b.v+2*self.d*b.d+self.v*b.dd)
 __rmul__=__mul__
 def comp(self,f,fp,fpp):return J(f,fp*self.d,fpp*self.d.sq()+fp*self.dd)
 def inv(self):
  v=1/self.v;return self.comp(v,-v.sq(),2*v**3)
 def __truediv__(self,b):return self*J.cv(b).inv()
 def __rtruediv__(self,b):return J.cv(b)*self.inv()
 def sqrt(self):
  v=self.v.sqrt();return self.comp(v,1/(2*v),-1/(4*v**3))
 def sq(self):return J(self.v.sq(),2*self.v*self.d,2*(self.d.sq()+self.v*self.dd))
