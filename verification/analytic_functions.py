"""Certified elementary functions and a cancellation-free edge function.
No numerical quadrature or floating-point transcendental functions are used.
"""
from interval import I,J,Q,SCALE
from math import comb
from itertools import combinations
PAIRS=list(combinations(range(4),2))

def atan_value(x):
    if x.lo<0 or x.hi>=SCALE//2: raise ArithmeticError('atan range')
    # Alternating power series, interval endpoints evaluated monotonically.
    def endpoint(a):
        a=I(a);w=a.sq();v=I(Q((-1)**40,81))
        for n in range(39,-1,-1):v=v*w+Q((-1)**n,2*n+1)
        rem=a*w**41/83
        return a*v+I(-rem.hi,0,True)
    lo=endpoint(Q(x.lo,SCALE));hi=endpoint(Q(x.hi,SCALE))
    return I(lo.lo,hi.hi,True)

def atan(x):
    x=J.cv(x);w=1+x.v.sq()
    return x.comp(atan_value(x.v),1/w,-2*x.v/w**2)

def asin_value(x):
    if x.lo<0 or x.hi>=SCALE*7//10:raise ArithmeticError('asin range')
    cf=[Q(comb(2*n,n),4**n*(2*n+1)) for n in range(49)]
    def endpoint(a):
        a=I(a);w=a.sq();v=I(cf[-1])
        for c in reversed(cf[:-1]):v=v*w+c
        tail=cf[-1]*a*w**49/(1-w)
        return a*v+I(0,tail.hi,True)
    lo=endpoint(Q(x.lo,SCALE));hi=endpoint(Q(x.hi,SCALE))
    return I(lo.lo,hi.hi,True)

PI=4*(4*atan_value(I(Q(1,5)))-atan_value(I(Q(1,239))))
def asin(x):
    x=J.cv(x);r=(1-x.v.sq()).sqrt()
    return x.comp(asin_value(x.v),1/r,x.v/r**3)
def acos(x):return J(PI/2)-asin(x)

def smallF(d):
    # d/2-d^3/24-sqrt(1-d^2/4)*asin(d/2); positive series.
    if d.v.lo <= 0 or d.v.hi > SCALE: raise ArithmeticError("edge range")
    x=d/2;w=x.sq();coeff=[];beta=Q(1)
    for n in range(1,35):
        beta*=Q(2*n,2*n+1)
        coeff.append(beta/Q(2*n+3))
    s=J(coeff[-1])
    for c in reversed(coeff[:-1]):s=s*w+c
    val=x*w.sq()*s
    # Tail and its first two d-derivatives: positive geometric bounds.
    # Leading omitted power d^(73), coefficient beta_35/73 / 2^73.
    beta*=Q(70,71);power=73;c=beta/73/2**73
    up=I(Q(d.v.hi,SCALE));r=up.sq()/4
    add=[]
    for j in range(3):
        factor=1 if j==0 else power if j==1 else power*(power-1)
        first=I(c*factor)*up**(power-j)
        # coefficient decrease in x basis; derivative ratios at most (p+2)^2/(p-1)^2
        ratio=r*Q((power+2)*(power+1),power*(power-1))
        if (1-ratio).lo <= 0: raise ArithmeticError("tail ratio")
        tail=first/(1-ratio)
        add.append(I(0,tail.hi,True))
    # Retain exact jet chain contributions for series remainder with respect to d.
    return J(val.v+add[0],val.d+add[1]*d.d,val.dd+add[2]*d.d.sq()+add[1]*d.dd)
