// Fixed-dyadic interval proof. All accepted bounds use integer arithmetic.
// Floating sqrt is a proposal only: exact integer inequalities repair/check it.
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
#ifndef PRECISION
#define PRECISION 48
#endif
using i128=__int128_t; using i64=int64_t;
constexpr int BITS=PRECISION; constexpr i64 S=i64(1)<<BITS;
i64 cv(i128 a){if(a<std::numeric_limits<i64>::min()||a>std::numeric_limits<i64>::max())throw std::runtime_error("integer overflow"); return (i64)a;}
i128 fd(i128 a,i128 b){if(!b)throw std::runtime_error("division by zero");if(b<0){a=-a;b=-b;} i128 q=a/b,r=a%b;return q-(r<0);}
i128 cd(i128 a,i128 b){return -fd(-a,b);}
struct I{
 i64 l,h;
 I():l(0),h(0){} I(int a):l(cv(i128(a)*S)),h(l){}
 static I raw(i64 l,i64 h){if(l>h)throw std::runtime_error("empty interval"); I z;z.l=l;z.h=h;return z;}
 static I rat(i64 a,i64 b=1){return raw(cv(fd(i128(a)*S,b)),cv(cd(i128(a)*S,b)));}
 static I span(I a,I b){return raw(a.l,b.h);}
 I operator-()const{return raw(cv(-i128(h)),cv(-i128(l)));}
};
I operator+(I a,I b){return I::raw(cv(i128(a.l)+b.l),cv(i128(a.h)+b.h));}
I operator-(I a,I b){return a+-b;}
I operator*(I a,I b){std::array<i128,4> t={i128(a.l)*b.l,i128(a.l)*b.h,i128(a.h)*b.l,i128(a.h)*b.h};auto m=std::minmax_element(t.begin(),t.end());return I::raw(cv(fd(*m.first,S)),cv(cd(*m.second,S)));}
I inv(I a){if(a.l<=0&&a.h>=0)throw std::runtime_error("zero interval denominator");return I::raw(cv(fd(i128(S)*S,a.h)),cv(cd(i128(S)*S,a.l)));}
I operator/(I a,I b){return a*inv(b);}
I sq(I a){if(a.l>=0)return a*a;if(a.h<=0)return (-a)*(-a);return I::raw(0,cv(cd(std::max(i128(a.l)*a.l,i128(a.h)*a.h),S)));}
i64 isqrt128(i128 a){if(a<0)throw std::runtime_error("negative radicand");i64 q=(i64)std::sqrt((long double)a);while(i128(q)*q>a)--q;while(i128(q+1)*(q+1)<=a)++q;return q;}
I rt(I a){if(a.l<0)throw std::runtime_error("negative interval radicand");i64 l=isqrt128(i128(a.l)*S),h=isqrt128(i128(a.h)*S);if(i128(h)*h<i128(a.h)*S)++h;return I::raw(l,h);}
I pos(I a){return I::raw(std::max<i64>(0,a.l),std::max<i64>(0,a.h));}
I hullzero(I a){return I::raw(std::min<i64>(0,a.l),std::max<i64>(0,a.h));}
i64 absmax(I a){return std::max(cv(-i128(a.l)),a.h);}
std::string fraction(i64 a){return std::to_string(a)+"/"+std::to_string(S);}
long double view(I a){return ((long double)a.l+a.h)/(2*S);}
// Two independent second-order jets, no mixed derivative needed.
struct J{
 I v;std::array<I,2>d,dd;
 J():v(0),d{I(0),I(0)},dd{I(0),I(0)}{}
 J(int a):v(a),d{I(0),I(0)},dd{I(0),I(0)}{}
 J(I a):v(a),d{I(0),I(0)},dd{I(0),I(0)}{}
 static J var(I a,int k){J z(a);z.d[k]=I(1);return z;}
 J operator-()const{J z;z.v=-v;for(int k=0;k<2;k++){z.d[k]=-d[k];z.dd[k]=-dd[k];}return z;}
};
J operator+(const J&a,const J&b){J z;z.v=a.v+b.v;for(int k=0;k<2;k++){z.d[k]=a.d[k]+b.d[k];z.dd[k]=a.dd[k]+b.dd[k];}return z;}
J operator-(const J&a,const J&b){return a+-b;}
J operator*(const J&a,const J&b){J z;z.v=a.v*b.v;for(int k=0;k<2;k++){z.d[k]=a.d[k]*b.v+a.v*b.d[k];z.dd[k]=a.dd[k]*b.v+I(2)*a.d[k]*b.d[k]+a.v*b.dd[k];}return z;}
J comp(const J&a,I f,I fp,I fpp){J z(f);for(int k=0;k<2;k++){z.d[k]=fp*a.d[k];z.dd[k]=fpp*sq(a.d[k])+fp*a.dd[k];}return z;}
J inv(const J&a){I v=inv(a.v);return comp(a,v,-sq(v),I(2)*v*sq(v));}
J operator/(const J&a,const J&b){return a*inv(b);}
J sq(const J&a){J z;z.v=sq(a.v);for(int k=0;k<2;k++){z.d[k]=I(2)*a.v*a.d[k];z.dd[k]=I(2)*(sq(a.d[k])+a.v*a.dd[k]);}return z;}
J rt(const J&a){I v=rt(a.v);return comp(a,v,I(1)/(I(2)*v),-I(1)/(I(4)*sq(v)*v));}

template<class Z>struct Params{Z ra,w,c,T;};
template<class Z>Params<Z> pars(Z a,Z b){
 Z A=a+b,c=b/(Z(2)*(Z(1)-a));
 Z eta=b/(Z(4)*rt(Z(1)-a)*rt(Z(1)-sq(c))*rt(Z(I::rat(1,8))-A/Z(16)));
 Z cb=rt(Z(4)/(Z(3)*(Z(2)-A))),sb=rt(Z(1)-sq(cb)),ee=rt(Z(1)-sq(eta));
 Z T=(sb*ee-cb*eta)/(cb*ee+sb*eta);
 return {rt(Z(I::rat(3,4))+a/Z(4)),rt(Z(I::rat(1,2))+(a-b)/Z(4)),c,T};
}
template<class Z>struct Eval{Z G,D,V;};
template<class Z>Eval<Z> integrand(const Params<Z>&p,Z u,Z v){
 Z x=p.T*u,y=x*v,xx=sq(x),yy=sq(y),W=Z(1)+(xx+yy)/(Z(1)-sq(p.c)),rw=rt(W);
 Z N=Z(rt(I::rat(3,4)))*rt(Z(1)+xx)+p.ra*rt(Z(1)+yy)-p.w;
 Z G=N/rw-Z(1),D=Z(1)-p.ra*rw/rt(Z(1)+yy);
 Z qq=Z(I::rat(47,32))*D-Z(2)*sq(D);
 return {G,D,Z(8)*sq(p.T)*u*G*qq/(W*rw)};
}
struct Bounds{I value,da,db;int excluded=0;};
// Point-parameter integral lower bound. Positive-part boundary cells are omitted.
I point_integral(I a,I b,int n){
 auto pi=pars<I>(a,b); Params<J>pj{J(pi.ra),J(pi.w),J(pi.c),J(pi.T)};
 I total(0),hh=I::rat(1,2*n),errfact=sq(hh)/I(6),area=I::rat(1,i64(n)*n);
 for(int i=0;i<n;i++)for(int j=0;j<n;j++){
  I ur=I::span(I::rat(i,n),I::rat(i+1,n)),vr=I::span(I::rat(j,n),I::rat(j+1,n));
  auto box=integrand<J>(pj,J::var(ur,0),J::var(vr,1));
  if(box.G.v.l<=0||box.D.v.l<=0)continue;
  auto mid=integrand<I>(pi,I::rat(2*i+1,2*n),I::rat(2*j+1,2*n));
  I err=I::raw(absmax(box.V.dd[0]),absmax(box.V.dd[0]))+I::raw(absmax(box.V.dd[1]),absmax(box.V.dd[1]));
  I val=mid.V-errfact*err;
  total=total+pos(I::raw(val.l,val.l))*area;
 }
 return total;
}
// Valid first-derivative enclosures on a parameter rectangle, including cutoffs.
std::array<I,2> gradient_integral(I a,I b,int n){
 auto p=pars<J>(J::var(a,0),J::var(b,1));
 std::array<I,2> sum={I(0),I(0)};I area=I::rat(1,i64(n)*n);
 for(int i=0;i<n;i++)for(int j=0;j<n;j++){
  I ur=I::span(I::rat(i,n),I::rat(i+1,n)),vr=I::span(I::rat(j,n),I::rat(j+1,n));
  auto r=integrand<J>(p,J(ur),J(vr));
  if(r.G.v.h<=0||r.D.v.h<=0)continue;
  bool interior=r.G.v.l>0&&r.D.v.l>0;
  for(int k=0;k<2;k++)sum[k]=sum[k]+(interior?r.V.d[k]:hullzero(r.V.d[k]))*area;
 }
 return sum;
}

struct Box{int i,j,da,db;};
struct Certifier {
 int npoint=192,ngrad=64; size_t attempted=0,passed=0,skipped=0; i64 margin=std::numeric_limits<i64>::max();
 std::ofstream output;
 Certifier(std::string name,int np,int ng):npoint(np),ngrad(ng),output(name){if(!output)throw std::runtime_error("cannot create report");}
 void visit(Box b){
  i64 na=i64(1)<<b.da,nb=i64(1)<<b.db;
  if(i128(b.i)*nb+i128(b.j)*na>i128(na)*nb){++skipped;return;}
  if(std::max(b.da,b.db)>17)throw std::runtime_error("unresolved parameter leaf");
  ++attempted;
  I al=I::rat(2*b.i,25*na),ah=I::rat(2*(b.i+1),25*na);
  I bl=I::rat(2*b.j,25*nb),bh=I::rat(2*(b.j+1),25*nb);
  I ar=I::span(al,ah),br=I::span(bl,bh);
  I am=I::rat(2*b.i+1,25*na),bm=I::rat(2*b.j+1,25*nb);
  I ha=I::rat(1,25*na),hb=I::rat(1,25*nb);
  I c0=I::rat(153,100000),ca=I::rat(-601,100000),cb=I::rat(317,20000);
  auto g=gradient_integral(ar,br,ngrad);
  I err=ha*I::raw(absmax(g[0]-ca),absmax(g[0]-ca))+hb*I::raw(absmax(g[1]-cb),absmax(g[1]-cb));
  I value=point_integral(am,bm,npoint);
  I low=value-(c0+ca*am+cb*bm)-err;
  if(low.l>0){
   ++passed;margin=std::min(margin,low.l);
   output<<b.i<<" "<<b.j<<" "<<b.da<<" "<<b.db<<" "<<low.l<<" "<<value.l<<" "<<g[0].l<<" "<<g[0].h<<" "<<g[1].l<<" "<<g[1].h<<"\n";
   if(passed%100==0)std::cerr<<"verified "<<passed<<" leaves; attempted "<<attempted<<"\n";
   return;
  }
  if(b.da<=b.db){visit({2*b.i,b.j,b.da+1,b.db});visit({2*b.i+1,b.j,b.da+1,b.db});}
  else {visit({b.i,2*b.j,b.da,b.db+1});visit({b.i,2*b.j+1,b.da,b.db+1});}
 }
 void run(){
  for(int i=0;i<32;i++)for(int j=0;j<32;j++)visit({i,j,5,5});
  output.close();
  std::cout<<"{\"status\":\"PASS\",\"precision\":"<<BITS<<",\"point_quadrature\":"<<npoint<<",\"gradient_quadrature\":"<<ngrad<<",\"leaves\":"<<passed<<",\"attempted\":"<<attempted<<",\"outside_leaves\":"<<skipped<<",\"least_margin\":\""<<fraction(margin)<<"\",\"least_margin_display\":"<<(long double)margin/S<<"}\n";
 }
};
int main(int argc,char**argv){try{
 if(BITS<40||BITS>56)throw std::runtime_error("use precision 40 through 56");
 if(argc<2){std::cerr<<"point a_num b_num denom n | grad a_lo a_hi b_lo b_hi denom n | verify filename [np=192] [ng=64]\n";return 2;}
 std::string mode=argv[1];std::cout.precision(18);
 if(mode=="point"){
  I a=I::rat(std::stoll(argv[2]),std::stoll(argv[4])),b=I::rat(std::stoll(argv[3]),std::stoll(argv[4]));int n=std::stoi(argv[5]);auto z=point_integral(a,b,n);
  std::cout<<"{\"lower\":\""<<fraction(z.l)<<"\",\"display\":"<<(long double)z.l/S<<",\"n\":"<<n<<"}\n";
 }else if(mode=="grad"){
  i64 den=std::stoll(argv[6]);I a=I::span(I::rat(std::stoll(argv[2]),den),I::rat(std::stoll(argv[3]),den)),b=I::span(I::rat(std::stoll(argv[4]),den),I::rat(std::stoll(argv[5]),den));auto g=gradient_integral(a,b,std::stoi(argv[7]));
  for(auto z:g)std::cout<<(long double)z.l/S<<" "<<(long double)z.h/S<<"\n";
 }else if(mode=="verify"){
  Certifier c(argv[2],argc>3?std::stoi(argv[3]):192,argc>4?std::stoi(argv[4]):64);c.run();
 }else throw std::runtime_error("unknown mode");
 return 0;
 }catch(const std::exception&e){std::cerr<<"FAIL: "<<e.what()<<"\n";return 1;}}
