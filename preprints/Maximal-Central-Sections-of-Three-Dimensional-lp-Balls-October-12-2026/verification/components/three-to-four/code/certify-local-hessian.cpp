// Lightweight interval feasibility probe. Not a complete parameter cover.
// Uses the installed MPFI/MPFR libraries, with their published stable ABI.
#include <iostream>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <chrono>
#include <vector>
#include <fstream>
extern "C" {
typedef struct {long prec; int sign; long exp; unsigned long* d;} MF;
typedef struct {MF left,right;} MI;
void mpfi_init2(MI*,long); void mpfi_clear(MI*);int mpfi_set_si(MI*,long);int mpfi_set_d(MI*,double);int mpfi_set(MI*,const MI*);int mpfi_interv_d(MI*,double,double);
int mpfi_log(MI*,const MI*);int mpfi_exp(MI*,const MI*);int mpfi_add(MI*,const MI*,const MI*);int mpfi_sub(MI*,const MI*,const MI*);int mpfi_mul(MI*,const MI*,const MI*);int mpfi_div(MI*,const MI*,const MI*);int mpfi_neg(MI*,const MI*);int mpfi_abs(MI*,const MI*);int mpfi_sqr(MI*,const MI*);int mpfi_sqrt(MI*,const MI*);int mpfi_sin(MI*,const MI*);int mpfi_cos(MI*,const MI*);int mpfi_const_pi(MI*);int mpfi_union(MI*,const MI*,const MI*);
int mpfr_set_str(MF*,const char*,int,int);int mpfr_cmp_ui(const MF*,unsigned long);int mpfr_cmp(const MF*,const MF*);int mpfr_pow(MF*,const MF*,const MF*,int);int mpfr_set_ui(MF*,unsigned long,int);double mpfr_get_d(const MF*,int); const char* mpfi_get_version();const char* mpfr_get_version();
}
struct I {MI m; I(){mpfi_init2(&m,80);mpfi_set_si(&m,0);} I(double x):I(){mpfi_set_d(&m,x);} I(double a,double b):I(){mpfi_interv_d(&m,a,b);} I(const char*a,const char*b):I(){mpfr_set_str(&m.left,a,10,3);mpfr_set_str(&m.right,b,10,2);} I(const I& x):I(){mpfi_set(&m,&x.m);} I&operator=(const I&x){mpfi_set(&m,&x.m);return *this;} ~I(){mpfi_clear(&m);} double lo()const{return mpfr_get_d(&m.left,3);} double hi()const{return mpfr_get_d(&m.right,2);} };
I operator+(const I&a,const I&b){I c;mpfi_add(&c.m,&a.m,&b.m);return c;} I operator-(const I&a,const I&b){I c;mpfi_sub(&c.m,&a.m,&b.m);return c;} I operator-(const I&a){I c;mpfi_neg(&c.m,&a.m);return c;} I operator*(const I&a,const I&b){I c;mpfi_mul(&c.m,&a.m,&b.m);return c;} I operator/(const I&a,const I&b){I c;mpfi_div(&c.m,&a.m,&b.m);return c;}
I sq(const I&a){I c;mpfi_sqr(&c.m,&a.m);return c;} I absI(const I&a){I c;mpfi_abs(&c.m,&a.m);return c;} I sqrtI(const I&a){I c;mpfi_sqrt(&c.m,&a.m);return c;} I sinI(const I&a){I c;mpfi_sin(&c.m,&a.m);return c;} I cosI(const I&a){I c;mpfi_cos(&c.m,&a.m);return c;}
I hull(const I&a,const I&b){I c;mpfi_union(&c.m,&a.m,&b.m);return c;}
I powI(const I&a,const I&b){ // a>=0, b>0 OR a>0 and arbitrary b; corner extrema plus x=1.
 I c; MF* l=&c.m.left;MF*r=&c.m.right;
 if(mpfr_cmp_ui(&a.m.left,0)<0){std::cerr<<"negative base\n";std::exit(2);}
 // For this probe positive bases with negative exponents are handled by reciprocal.
 if(mpfr_cmp_ui(&b.m.right,0)<0)return I(1)/powI(a,-b);
 if(mpfr_cmp_ui(&b.m.left,0)<0){I q,t;mpfi_log(&q.m,&a.m);mpfi_mul(&t.m,&q.m,&b.m);mpfi_exp(&c.m,&t.m);return c;}
 if(mpfr_cmp_ui(&a.m.left,0)==0)mpfr_set_ui(l,0,3);
 else mpfr_pow(l,&a.m.left,mpfr_cmp_ui(&a.m.left,1)<0?&b.m.right:&b.m.left,3);
 mpfr_pow(r,&a.m.right,mpfr_cmp_ui(&a.m.right,1)<0?&b.m.left:&b.m.right,2);
 return c;
}

struct J {I x,a,b;J():x(0),a(0),b(0){} J(const I&v):x(v),a(0),b(0){} J(const I&v,const I&v1,const I&v2):x(v),a(v1),b(v2){} };
J operator+(const J&a,const J&b){return J(a.x+b.x,a.a+b.a,a.b+b.b);} J operator-(const J&a,const J&b){return J(a.x-b.x,a.a-b.a,a.b-b.b);} J operator-(const J&a){return J(-a.x,-a.a,-a.b);}
J operator*(const J&a,const J&b){return J(a.x*b.x,a.a*b.x+a.x*b.a,a.b*b.x+a.a*b.a+a.x*b.b);}
J operator/(const J&a,const J&b){I x=a.x/b.x,y=(a.a-x*b.a)/b.x;return J(x,y,(a.b-x*b.b-y*b.a)/b.x);}
J powJ(const J&a,const I&b){if(a.a.lo()==0&&a.a.hi()==0&&a.b.lo()==0&&a.b.hi()==0)return J(powI(a.x,b));I g=powI(a.x,b),d=b*powI(a.x,b-I(1));return J(g,d*a.a,d*a.b+b*(b-I(1))/I(2)*powI(a.x,b-I(2))*sq(a.a));}
J sqJ(const J&a){return a*a;}
J absJ(const J&a){if(a.x.lo()>0)return a;if(a.x.hi()<0)return -a;std::cerr<<"absolute-value root in Taylor cell\n";std::exit(3);}
struct Res {J h[3];};
Res calc(const I&p,const I&u,const I&v,const I&theta,bool jet){
 I cx=absI(cosI(theta)),sx=absI(sinI(theta));J c(cx),s(sx);if(jet){c=J(cx,-sx,-cx/I(2));s=J(sx,cx,-sx/I(2));}
 I S=I(1)+sq(u)+sq(v),ss=sqrtI(S),r=I(2)/p;Res out;
 for(int sign:{-1,1}){J d=J(I(sign))*s,z=J(u)*c+J(v)*d,az; if(jet)az=absJ(z);else az=J(absI(z.x));
  J Q=powJ(c,p)+powJ(s,p)+powJ(az,p);J f=J(ss)*powJ(Q,-r),t=powJ(az,p-I(2))/Q,b=t*z;
  J k=J(I(2)*(p+I(2)))*sqJ(b)-J(I(2)*(p-I(1)))*t;
  out.h[0]=out.h[0]+f*(J(I(1)/S-sq(u)/sq(S))-J(I(4)*u/S)*b*c+k*sqJ(c));
  out.h[1]=out.h[1]+f*(J(-u*v/sq(S))-J(I(2)/S)*b*(J(u)*d+J(v)*c)+k*c*d);
  out.h[2]=out.h[2]+f*(J(I(1)/S-sq(v)/sq(S))-J(I(4)*v/S)*b*d+k*sqJ(d));
 }
 return out;
}
bool roots(const I&u,const I&v,const I&th){I c=absI(cosI(th)),s=absI(sinI(th)),z=u*c-v*s;return c.lo()<=0||s.lo()<=0||(z.lo()<=0&&z.hi()>=0);}
void printI(const char*name,const I&a){std::cout<<name<<" ["<<std::setprecision(17)<<a.lo()<<", "<<a.hi()<<"]\n";}


I eigen_upper_interval(const I&p,const I&u,const I&v,int N){I pi;mpfi_const_pi(&pi.m);I step=pi/I(2*N),hs[3];for(int k=0;k<N;++k){I th=hull(I(k)*step,I(k+1)*step),mid=(I(k)+I(.5))*step;if(roots(u,v,th)){Res r=calc(p,u,v,th,false);for(int j=0;j<3;++j)hs[j]=hs[j]+step*r.h[j].x;}else{Res r=calc(p,u,v,th,true),m=calc(p,u,v,mid,false);for(int j=0;j<3;++j)hs[j]=hs[j]+step*m.h[j].x+step*step*step/I(12)*r.h[j].b;}}return (hs[0]+hs[2])/I(2)+sqrtI(sq((hs[0]-hs[2])/I(2))+sq(hs[1]));}
const long DEN=1000L*(1L<<20);
struct Box {long lo[3],hi[3];int depth;};
int main(){
// These constants are conditional on the completed signed derivative cover.
// |A_uuu|,|A_vvv|<=8; |A_uuv|,|A_uvv|<=6;
// |A_uup|,|A_vvp|<=2; |A_uvp|<=2.
std::vector<Box>stack;for(int k=0;k<10;++k)for(int i=0;i<5;++i)for(int j=0;j<=i;++j){Box b;b.depth=0;b.lo[0]=(3000+100*k)*(1L<<20);b.hi[0]=b.lo[0]+100*(1L<<20);b.lo[1]=(850+30*i)*(1L<<20);b.hi[1]=b.lo[1]+30*(1L<<20);b.lo[2]=(850+30*j)*(1L<<20);b.hi[2]=b.lo[2]+30*(1L<<20);stack.push_back(b);}
std::ofstream csv("logs/local_hessian_certificate_boxes.csv");csv<<"p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,denominator,eigen_upper,variation_upper,final_upper,depth\n";int evaluated=0,passed=0,maxdepth=0;double worst=-1e100;auto start=std::chrono::steady_clock::now();std::cout<<"AUTHOR CERTIFICATE CONDITIONAL ON DERIVATIVE BOUNDS 8 6 2 2 MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" N 128 precision 80\n"<<std::flush;
while(!stack.empty()){Box b=stack.back();stack.pop_back();I center[3],radius[3];for(int i=0;i<3;++i){center[i]=I(double(b.lo[i]+b.hi[i]))/I(double(2*DEN));radius[i]=I(double(b.hi[i]-b.lo[i]))/I(double(2*DEN));}
I eig=eigen_upper_interval(center[0],center[1],center[2],128);I v1=I(14)*radius[1]+I(12)*radius[2]+I(4)*radius[0],v2=I(12)*radius[1]+I(14)*radius[2]+I(4)*radius[0],variation=hull(v1,v2),upper=eig+variation;I test=upper+I(1)/I(500);evaluated++;maxdepth=std::max(maxdepth,b.depth);
if(mpfr_cmp_ui(&test.m.right,0)<0){passed++;worst=std::max(worst,upper.hi());for(int i=0;i<3;++i)csv<<b.lo[i]<<","<<b.hi[i]<<",";csv<<DEN<<","<<std::setprecision(17)<<eig.hi()<<","<<variation.hi()<<","<<upper.hi()<<","<<b.depth<<"\n";}
else{if(b.depth>=20){std::cout<<"FAIL depth limit at "<<b.lo[0]<<","<<b.lo[1]<<","<<b.lo[2]<<" upper "<<upper.hi()<<"\n";return 2;}double score[3]={4*radius[0].hi(),14*radius[1].hi(),14*radius[2].hi()};int a=int(std::max_element(score,score+3)-score);long sum=b.lo[a]+b.hi[a];if(sum%2){std::cout<<"FAIL nonintegral split\n";return 3;}long mid=sum/2;Box b1=b,b2=b;b1.hi[a]=mid;b2.lo[a]=mid;b1.depth++;b2.depth++;stack.push_back(b2);stack.push_back(b1);}
if(evaluated%100==0){csv.flush();std::cout<<"evaluated "<<evaluated<<" passed "<<passed<<" pending "<<stack.size()<<" worst "<<std::setprecision(17)<<worst<<" maxdepth "<<maxdepth<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n"<<std::flush;}}
std::cout<<"COMPLETE PASS evaluated "<<evaluated<<" passed "<<passed<<" worst "<<std::setprecision(17)<<worst<<" maxdepth "<<maxdepth<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";return 0;}
