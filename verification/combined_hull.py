"""Clipped outer volume and weighted inner/outer combination, exact intervals."""
from interval import I,J,Q
from analytic_functions import PI
from clipped_hull import acos, parameters, edge, baseline

def outer_base(R):
 R=J.cv(R)
 return 8*J(PI)/3-J(PI)/R

def outer_edge(R,e):
 R=J.cv(R);e=J.cv(e);s=(1-e).sqrt();r=(1-s.sq()/4).sqrt();m=(R.sq()-s.sq()/4).sqrt();k=(1-1/(4*R.sq())).sqrt()
 ph=2*acos((1-s.sq()/2)/(2*r*m));U=acos(s/(4*R*r*k));V=acos(1-s.sq()/(2*k.sq()));ps=acos((1-2*R.sq())*s/(4*R*k*m));T=s*(R.sq()*(4-s.sq())-1).sqrt()
 return (-4*U-2*R*R.sq()*V+ph*(-3*s/2+s*s.sq()/8)+T/2+(4*R*R.sq()+3/(2*R))*ps)/3

def combined_edge(R,e):
 return (47*edge(R,e)-outer_edge(R,e))/46

def combined_baseline(R):
 return (47*baseline(R)-outer_base(R)-6*outer_edge(R,0))/46


def outer_edge_dx(R,x):
 R=J.cv(R);x=J.cv(x);s=x.sqrt();QQ=(R.sq()*(4-x)-1).sqrt();den=4*R.sq()-x
 phi=2*acos((2-x)/((4-x)*den).sqrt())
 return (2-x)*QQ/(4*s*den)-(4-x)*phi/(16*s)

def combined_dx(R,x):
 from clipped_hull import edge_dx
 return (47*edge_dx(R,x)-outer_edge_dx(R,x))/46
