// Propose row outputs for Lean's independent kernel checks.
// This executable is not part of the mathematical trusted base.
#define PRECISION 52
#define main manuscript_projective_main
#include "../../verification/projective_certificate.cpp"
#undef main
#include <sstream>

I centered_row(I a, I b, int n, int i) {
  auto pi = pars<I>(a, b);
  Params<J> pj{J(pi.ra), J(pi.w), J(pi.c), J(pi.T)};
  I total(0), half = I::rat(1, 2*n), errorFactor = sq(half)/I(6);
  I area = I::rat(1, i64(n)*n);
  for (int j = 0; j < n; ++j) {
    I u = I::span(I::rat(i,n), I::rat(i+1,n));
    I v = I::span(I::rat(j,n), I::rat(j+1,n));
    auto box = integrand<J>(pj, J::var(u,0), J::var(v,1));
    auto mid = integrand<I>(pi, I::rat(2*i+1,2*n), I::rat(2*j+1,2*n));
    I gSlope = I::raw(absmax(box.G.d[0]), absmax(box.G.d[0])) +
      I::raw(absmax(box.G.d[1]), absmax(box.G.d[1]));
    I dSlope = I::raw(absmax(box.D.d[0]), absmax(box.D.d[0])) +
      I::raw(absmax(box.D.d[1]), absmax(box.D.d[1]));
    if ((box.G.v.l <= 0 || box.D.v.l <= 0) &&
        ((mid.G-half*gSlope).l <= 0 || (mid.D-half*dSlope).l <= 0)) continue;
    I error = I::raw(absmax(box.V.dd[0]), absmax(box.V.dd[0])) +
      I::raw(absmax(box.V.dd[1]), absmax(box.V.dd[1]));
    I value = mid.V-errorFactor*error;
    total = total + pos(I::raw(value.l,value.l))*area;
  }
  return total;
}

std::array<I,2> gradient_row(I a, I b, int n, int i) {
  auto p = pars<J>(J::var(a,0), J::var(b,1));
  std::array<I,2> total{I(0), I(0)};
  I area = I::rat(1, i64(n)*n);
  for (int j = 0; j < n; ++j) {
    I u = I::span(I::rat(i,n), I::rat(i+1,n));
    I v = I::span(I::rat(j,n), I::rat(j+1,n));
    auto box = integrand<J>(p, J(u), J(v));
    if (box.G.v.h <= 0 || box.D.v.h <= 0) continue;
    bool active = box.G.v.l > 0 && box.D.v.l > 0;
    for (int k = 0; k < 2; ++k)
      total[k] = total[k] + (active ? box.V.d[k] : hullzero(box.V.d[k]))*area;
  }
  return total;
}

void print_interval(I x) { std::cout << '[' << x.l << ',' << x.h << ']'; }

int main(int argc, char** argv) { try {
  if (argc != 2) throw std::runtime_error("expected a grid-choice file");
  std::ifstream choices(argv[1]);
  if (!choices) throw std::runtime_error("cannot open grid-choice file");
  std::cout << "{\"precision\":52,\"boxes\":[\n";
  std::string line; bool first = true;
  while (std::getline(choices,line)) {
    std::istringstream row(line); int i,j,da,db,np,ng;
    if (!(row >> i >> j >> da >> db >> np >> ng))
      throw std::runtime_error("invalid grid-choice record");
    if (i < 0 || j < 0 || da < 0 || db < 0 || da > 17 || db > 17 ||
        np <= 0 || ng <= 0 || np > 192 || ng > 192)
      throw std::runtime_error("grid-choice record outside supported range");
    i64 na=25LL*(1LL<<da), nb=25LL*(1LL<<db);
    I a=I::rat(2*i+1,na), b=I::rat(2*j+1,nb);
    I ar=I::span(I::rat(2*i,na), I::rat(2*i+2,na));
    I br=I::span(I::rat(2*j,nb), I::rat(2*j+2,nb));
    auto p=pars<I>(a,b); auto g=pars<J>(J::var(ar,0),J::var(br,1));
    if (!first) std::cout << ",\n"; first=false;
    std::cout << "{\"box\":[" << i << ',' << j << ',' << da << ',' << db <<
      "],\"point_grid\":" << np << ",\"gradient_grid\":" << ng << ",\"parameters\":[";
    bool comma=false;
    for (auto x : {p.ra,p.w,p.c,p.T}) {
      if (comma) std::cout << ','; comma=true; print_interval(x);
    }
    std::cout << "],\"parameter_jets\":["; comma=false;
    for (int k=0; k<2; ++k) for (auto x : {g.ra,g.w,g.c,g.T}) {
      if (comma) std::cout << ','; comma=true;
      std::cout << '[' << x.v.l << ',' << x.v.h << ',' << x.d[k].l << ',' <<
        x.d[k].h << ',' << x.dd[k].l << ',' << x.dd[k].h << ']';
    }
    std::cout << "],\"point_rows\":[";
    for (int k=0; k<np; ++k) {
      if (k) std::cout << ','; std::cout << centered_row(a,b,np,k).l;
    }
    std::cout << "],\"gradient_rows\":[";
    for (int k=0; k<ng; ++k) {
      if (k) std::cout << ','; auto z=gradient_row(ar,br,ng,k);
      std::cout << '[' << z[0].l << ',' << z[0].h << ',' << z[1].l << ',' << z[1].h << ']';
    }
    std::cout << "]}";
  }
  std::cout << "\n]}\n";
  return 0;
} catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 1; } }
