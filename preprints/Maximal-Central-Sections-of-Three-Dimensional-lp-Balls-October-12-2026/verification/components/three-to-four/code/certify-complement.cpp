// Lightweight interval feasibility probe. Not a complete parameter cover.
// Uses the installed MPFI/MPFR libraries, with their published stable ABI.
#include <iostream>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <vector>
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


I area(const I&p,const I&u,const I&v,const std::vector<I>&c,const std::vector<I>&s,const std::vector<I>&B,const I&step){I total,r=-I(2)/p;for(size_t k=0;k<c.size();++k){I z=u*c[k],w=v*s[k];total=total+powI(B[k]+powI(absI(z+w),p),r)+powI(B[k]+powI(absI(z-w),p),r);}return sqrtI(I(1)+sq(u)+sq(v))*step*total;}
int main(int argc,char**argv){int N=384;std::ofstream csv("logs/complement_interval_vertices.csv");csv<<"p_index,u_index,v_index,certified_margin_lower\n";I pi;mpfi_const_pi(&pi.m);I step=pi/I(2*N);std::vector<I>cs,ss;for(int k=0;k<N;++k){I th=(I(k)+I(.5))*step;cs.push_back(absI(cosI(th)));ss.push_back(absI(sinI(th)));}I loss=I(67)/I(40000)+I(52)/I(N*N);int count=0,failed=0;double global=1e100;int gk=-1,gi=-1,gj=-1;auto start=std::chrono::steady_clock::now();
std::cout<<"UNREVIEWED AUTHOR CERTIFICATE MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" precision 80 N "<<N<<"\n";
for(int k=0;k<=20;++k){I p=I(3)+I(k)/I(20);std::vector<I>B;for(int t=0;t<N;++t)B.push_back(powI(cs[t],p)+powI(ss[t],p));I diag=area(p,I(1),I(1),cs,ss,B,step);double pm=1e100;int mi=-1,mj=-1;
for(int i=0;i<=100;++i){I u=I(i)/I(100);for(int j=0;j<=std::min(i,85);++j){I v=I(j)/I(100),a=area(p,u,v,cs,ss,B,step);I margin=diag-a-(sq(I(1)-u)+sq(I(1)-v))/I(1000)-loss;bool ok=mpfr_cmp_ui(&margin.m.left,0)>0;if(!ok)failed++;double ml=margin.lo();if(ml<pm){pm=ml;mi=i;mj=j;}if(ml<global){global=ml;gk=k;gi=i;gj=j;}csv<<k<<","<<i<<","<<j<<","<<std::setprecision(17)<<ml<<"\n";count++;}}
csv.flush();std::cout<<"p_index "<<k<<" vertices "<<count<<" failed "<<failed<<" min_margin "<<std::setprecision(17)<<pm<<" at "<<mi<<","<<mj<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n"<<std::flush;}
std::cout<<"COMPLETE "<<(count==105651&&failed==0?"PASS":"FAIL")<<" vertices "<<count<<" failed "<<failed<<" minimum "<<std::setprecision(17)<<global<<" at "<<gk<<","<<gi<<","<<gj<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";return count==105651&&failed==0?0:1;
}
