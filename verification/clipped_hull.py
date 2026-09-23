"""Exact-interval edge formula for the dual of a circumsphere-clipped ball hull.
All sign decisions use fixed-dyadic integer intervals. See the accompanying note.
"""
from interval import I,J,Q,SCALE
from analytic_functions import PI,asin,atan,smallF


def acos(x):
    x=J.cv(x)
    if x.v.lo>=SCALE*3//5:
        return 2*atan(((1-x)/(1+x)).sqrt())
    if x.v.hi<=0:
        return J(PI/2)+asin(-x)
    return J(PI/2)-asin(x)


def parameters(R):
    R=J.cv(R)
    k=(1-1/(4*R.sq())).sqrt()
    ga=acos(1/(2*R))
    z=R.sq()-R-R.sq()*R/3
    b=Q(1,2)-3/(8*R)-k*ga/2-z
    base=8*J(PI)/3-3*J(PI)/R-4*J(PI)*k*ga
    return k,ga,z,b,base


def edge(R,e,pars=None):
    R=J.cv(R); e=J.cv(e)
    k,ga,z,b,base=parameters(R) if pars is None else pars
    s=(1-e).sqrt(); r=(1-s.sq()/4).sqrt(); m=(R.sq()-s.sq()/4).sqrt()
    ph=2*acos((1-s.sq()/2)/(2*r*m))
    U=acos(s/(4*R*r*k))
    V=acos(1-s.sq()/(2*k.sq()))
    ps=acos((1-2*R.sq())*s/(4*R*k*m))
    tr=s*(4*r.sq()*m.sq()-(1-s.sq()/2).sq()).sqrt()
    return 4*U/3-2*z*V+ph*smallF(s)-tr/6-4*b*ps


def baseline(R):
    R=J.cv(R); pars=parameters(R)
    return pars[-1]+6*edge(R,0,pars)


def edge_dx(R,x):
    """Analytically simplified partial derivative with respect to squared edge x."""
    R=J.cv(R);x=J.cv(x);t=R.sq();s=x.sqrt();r=(1-x/4).sqrt()
    Qr=(t*(4-x)-1).sqrt();D=4*t-x
    ph=2*acos((2-x)/((4-x)*(4*t-x)).sqrt())
    th=asin(s/2); ga=acos(1/(2*R));
    Fx=-s/16+th/(8*r)
    return ph*Fx+(x+6-8*R)*Qr/(4*s*D)-(6*t-t*x-2)*th/((4-x).sqrt()*Qr*D)-(4*t-1).sqrt()*(1-2*t)*ga/(s*Qr*D)
