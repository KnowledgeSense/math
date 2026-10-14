// Lightweight interval feasibility probe. Not a complete parameter cover.
// Uses the installed MPFI/MPFR libraries, with their published stable ABI.
#include <iostream>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <chrono>
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


I signI(const I&a){if(a.lo()>0)return I(1);if(a.hi()<0)return I(-1);return I(-1,1);} I logI(const I&a){I o;mpfi_log(&o.m,&a.m);return o;}
I powlog(const I&a,const I&b){if(a.lo()>0)return powI(a,b)*logI(a);I upper(0);if(a.hi()>1)upper=powI(I(a.hi()),b)*logI(I(a.hi()));return hull(I(-1),upper);}
void printI(const char*name,const I&a){std::cout<<name<<" ["<<std::setprecision(17)<<a.lo()<<", "<<a.hi()<<"]\n";}

// C5 branch-only feasibility certificate; no global section theorem.
I branch_diff(const I&p,int N,bool derivative,bool fullcells){
 I d(0),t(0),step=I(1)/I(N);
 for(int j=0;j<N;++j){
  I x=fullcells?hull(I(j)*step,I(j+1)*step):(I(j)+I(.5))*step;
  I y=I(1)-x,a=powI(x,p),b=powI(y,p),S=I(1)+a+b,Q=I(1)+a;
  I D=powI(S,-I(2)/p),T=powI(I(2),-I(1)/p)*powI(Q,-I(2)/p);
  if(derivative){
   I ap=powlog(x,p),bp=powlog(y,p);
   D=D*(I(2)/sq(p)*logI(S)-I(2)/p*(ap+bp)/S);
   T=T*(logI(I(2))/sq(p)+I(2)/sq(p)*logI(Q)-I(2)/p*ap/Q);
  }
  d=d+D;t=t+T;
 }
 return (I(3)*sqrtI(I(3))*d-I(4)*sqrtI(I(2))*t)*step;
}
int main(int argc,char**argv){int P=argc>1?std::stoi(argv[1]):200,N=argc>2?std::stoi(argv[2]):1024;double worst=-1e100;bool pass=true;
 std::cout<<"MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" precision80, derivative Riemann cells, P "<<P<<" N "<<N<<"\n";
 for(int j=0;j<P;++j){I p=hull(I(4)+I(2*j)/I(P),I(4)+I(2*j+2)/I(P));I z=branch_diff(p,N,true,true);std::cout<<"derivative "<<j<<" ";printI("",z);worst=std::max(worst,z.hi());if(z.hi()>=0)pass=false;}
 for(int numer:{499,500}){int K=4096;I p=I(numer)/I(100),z=branch_diff(p,K,false,false),err=I(500)/I(24)/I(K)/I(K);std::cout<<"endpoint "<<numer<<"/100 ";printI("",z+hull(-err,err));}
 std::cout<<"derivative_all_negative "<<pass<<" worst_upper "<<std::setprecision(17)<<worst<<"\n";
}
