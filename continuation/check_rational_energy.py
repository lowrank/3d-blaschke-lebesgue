#!/usr/bin/env python3
"""Exact checks for the rational support-energy formulation.

No floating arithmetic, numerical convex-hull library, or optimizer is used.
The finite energies are evaluations at a test body, NOT global minima.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import hashlib
import json
from pathlib import Path


def require(test, msg):
    if not test:
        raise RuntimeError(msg)


def add(a, b): return tuple(x + y for x, y in zip(a, b))
def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def scale(a, t): return tuple(t*x for x in a)
def dot(a, b): return sum(x*y for x, y in zip(a, b))
def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def norm2(a): return dot(a, a)
def neg(a): return tuple(-x for x in a)
def det(a, b, c): return dot(a, cross(b, c))


def normal_net(m):
    result = set()
    for i in range(-m, m+1):
        for j in range(-m, m+1):
            d = m*m+i*i+j*j
            n = (F(2*m*i, d), F(2*m*j, d), F(m*m-i*i-j*j, d))
            result.update([n, neg(n)])
    return sorted(result)


def facets_exact(points):
    facets = {}
    for i, j, k in combinations(range(len(points)), 3):
        nu = cross(sub(points[j], points[i]), sub(points[k], points[i]))
        if norm2(nu) == 0:
            continue
        d = dot(nu, points[i])
        # The origin is inside because the array spans and is antipodal.
        if d == 0:
            continue
        if d < 0:
            nu, d = neg(nu), -d
        offsets = [dot(nu, p) - d for p in points]
        if any(t > 0 for t in offsets):
            continue
        ids = tuple(i for i, t in enumerate(offsets) if t == 0)
        facets[ids] = nu
    return facets


def polygon_order(ids, points, normal):
    drop = max(range(3), key=lambda i: abs(normal[i]))
    keep = [i for i in range(3) if i != drop]
    coords = {i: (points[i][keep[0]], points[i][keep[1]]) for i in ids}
    order = sorted(ids, key=lambda i: coords[i])
    def orient(i, j, k):
        a, b, c = coords[i], coords[j], coords[k]
        return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    lower, upper = [], []
    for seq, out in [(order, lower), (reversed(order), upper)]:
        for i in seq:
            while len(out) >= 2 and orient(out[-2], out[-1], i) <= 0:
                out.pop()
            out.append(i)
    result = lower[:-1] + upper[:-1]
    require(set(result) == set(ids), 'Unexpected nonvertex point in a facet.')
    a, b, c = [points[i] for i in result[:3]]
    if dot(cross(sub(b, a), sub(c, a)), normal) < 0:
        result.reverse()
    start = result.index(min(result))
    return result[start:] + result[:start]


def triangulate(points):
    index = {p: i for i, p in enumerate(points)}
    anti = [index[neg(p)] for p in points]
    facets = facets_exact(points)
    visited, triangles = set(), []
    for ids in sorted(facets):
        if ids in visited:
            continue
        opposite = tuple(sorted(anti[i] for i in ids))
        require(opposite in facets, 'Facet is missing its antipode.')
        poly = polygon_order(ids, points, facets[ids])
        for j in range(1, len(poly)-1):
            tri = (poly[0], poly[j], poly[j+1])
            require(det(*(points[i] for i in tri)) > 0, 'Wrong orientation.')
            triangles += [tri, (anti[tri[0]], anti[tri[2]], anti[tri[1]])]
        visited.update([ids, opposite])
    edges = Counter()
    used = set()
    for tri in triangles:
        used.update(tri)
        a, b, c = [points[i] for i in tri]
        nu = cross(sub(b, a), sub(c, a))
        d = dot(nu, a)
        require(d > 0 and all(dot(nu, p) <= d for p in points), 'Invalid supporting triangle.')
        for i, j in zip(tri, tri[1:]+tri[:1]):
            edges[i, j] += 1
    require(len(used) == len(points), 'Unused vertex.')
    require(all(count == 1 and edges[j, i] == 1 for (i, j), count in edges.items()),
            'Oriented edges do not cancel exactly.')
    nedges = len(edges)//2
    require(len(points)-nedges+len(triangles) == 2, 'Euler identity failed.')
    return anti, triangles, len(facets), nedges


def local_matrix(vertices):
    a, b, c = vertices
    determinant = det(a, b, c)
    require(determinant > 0, 'Nonpositive face determinant.')
    # Columns of the inverse of the row matrix N.
    cols = [scale(cross(b, c), 1/determinant), scale(cross(c, a), 1/determinant),
            scale(cross(a, b), 1/determinant)]
    T = [[F(0) for _ in range(3)] for _ in range(3)]
    for p, q in [(a,b), (b,c), (c,a)]:
        s, t = cross(p,q), add(p,q)
        denom = 2*(1+dot(p,q))
        require(denom > 0, 'Antipodal face edge.')
        for i in range(3):
            for j in range(3):
                T[i][j] -= (s[i]*t[j]+t[i]*s[j])/denom
    def bilinear(x,y): return sum(x[i]*T[i][j]*y[j] for i in range(3) for j in range(3))
    return [[bilinear(x,y) for y in cols] for x in cols]


def psd_rank(matrix):
    """Exact symmetric elimination; zero diagonal forces a zero residual row."""
    B = [row[:] for row in matrix]
    n, rank = len(B), 0
    for k in range(n):
        require(B[k][k] >= 0, 'Negative semidefinite pivot.')
        if B[k][k] == 0:
            require(all(B[k][j] == 0 for j in range(k,n)), 'Nonzero row at zero PSD pivot.')
            continue
        pivot = B[k][k]
        rank += 1
        for i in range(k+1,n):
            for j in range(i,n):
                B[i][j] -= B[i][k]*B[k][j]/pivot
                B[j][i] = B[i][j]
    return rank


def matvec(M,x): return [sum(a*b for a,b in zip(row,x)) for row in M]
def quad(M,x): return dot(x,matvec(M,x))


def atan_interval(x, n=80):
    require(n%2 == 0 and 0 < x < 1, 'Invalid alternating-series parameters.')
    s = sum(((-1)**j)*x**(2*j+1)/F(2*j+1) for j in range(n))
    return s, s+x**(2*n+1)/F(2*n+1)


def analyze(m, out):
    points = normal_net(m)
    require(all(norm2(n)==1 for n in points), 'Nonunit rational normal.')
    anti, triangles, nfacets, nedges = triangulate(points)
    size = len(points)
    E = [[F(0) for _ in range(size)] for _ in range(size)]
    eps, beta2 = F(0), F(0)
    for tri in triangles:
        ns = [points[i] for i in tri]
        M = local_matrix(ns)
        for i in range(3):
            for j in range(3): E[tri[i]][tri[j]] += M[i][j]
        n0,n1,n2 = ns
        d2 = max(norm2(sub(a,b)) for a,b in combinations(ns,2))
        dt = det(*ns)
        cp = cross(sub(n1,n0), sub(n2,n0))
        c2 = dt*dt/norm2(cp)
        require(0 < c2 <= 1, 'Invalid plane distance.')
        eps = max(eps,(1-c2)/(4*c2))
        beta2 = max(beta2,F(9)*d2**3/(8*c2*dt**2))
    representatives = [i for i in range(size) if i < anti[i]]
    O = [[E[i][j]-E[i][anti[j]]-E[anti[i]][j]+E[anti[i]][anti[j]]
          for j in representatives] for i in representatives]
    require(all(O[i][j]==O[j][i] for i in range(len(O)) for j in range(len(O))), 'Not symmetric.')
    rank = psd_rank(O)
    require(rank == len(representatives)-3, 'Unexpected translation kernel dimension.')
    for k in range(3):
        v = [points[i][k] for i in representatives]
        require(all(t==0 for t in matvec(O,v)), 'Translation has nonzero energy.')
    amplitude = F(1,10)
    values, support = [], []
    for n in points:
        P = n[0]*n[1]*n[2]
        grad = (n[1]*n[2],n[0]*n[2],n[0]*n[1])
        values.append(amplitude*P)
        support.append(add(scale(n,F(1,2)-2*amplitude*P),scale(grad,amplitude)))
    comparisons = 0
    for i in range(size):
        require(sub(support[i],support[anti[i]]) == points[i], 'Antipodal support identity failed.')
        require(dot(support[i],points[i])-F(1,2) == values[i], 'Nodal support value failed.')
        for j in range(i):
            require(norm2(sub(support[i],support[j])) <= 1, 'Finite diameter constraint failed.')
            comparisons += 1
    v = [values[i] for i in representatives]
    energy = quad(O,v)
    require(energy == quad(E,values), 'Full and antipodal energy disagree.')
    # The analytic support has E=8*pi*(amplitude^2)/21.
    a0,a1=atan_interval(F(1,5));b0,b1=atan_interval(F(1,239))
    pi0,pi1=16*a0-4*b1,16*a1-4*b0
    require(3 < pi0 < pi1 < F(22,7), 'Pi enclosure failed.')
    # V(actual)-V(interpolant) = E_interpolant/4 - 2*pi*amplitude^2/21.
    delta0=energy/4-2*pi1*amplitude**2/21
    delta1=energy/4-2*pi0*amplitude**2/21
    require(delta0 >= -2*pi1*eps, 'Lower interpolation test failed.')
    require(delta1 <= 2*pi1*eps+pi1*beta2, 'Upper interpolation test failed.')
    data={'normals':[[str(x) for x in n] for n in points], 'triangles':triangles,
          'antipodal_representatives':representatives,
          'odd_energy_matrix':[[str(x) for x in row] for row in O]}
    path = out/f'matrix_m{m}.json'
    path.write_text(json.dumps(data,indent=2)+'\n')
    return {'m':m,'vertices':size,'supporting_facets':nfacets,'triangles':len(triangles),
            'undirected_edges':nedges,'odd_dimension':len(O),'energy_rank':rank,
            'translation_kernel_dimension':len(O)-rank,'diameter_comparisons':comparisons,
            'test_energy':str(energy),'epsilon_upper':str(eps),'gradient_error_squared_upper':str(beta2),
            'matrix_data_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'status':'PASS', 'scope':'Matrix and feasible test evaluation; not an optimized bound.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'reports')
    args=p.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    axes=[(F(1),F(0),F(0)),(F(0),F(1),F(0)),(F(0),F(0),F(1))]
    octant=local_matrix(axes)
    require(octant==[[F(0) if i==j else F(-1) for j in range(3)] for i in range(3)],
            'Octant edge-integral identity failed.')
    runs=[]
    for m in [1,2]:
        result=analyze(m,args.output);runs.append(result);print(json.dumps(result,indent=2),flush=True)
    report={'status':'PASS','scope':'Exact finite matrix and interpolation sanity checks; no global optimization.',
            'octant_boundary_formula':'PASS','runs':runs,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (args.output/'rational_energy_report.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__': main()
