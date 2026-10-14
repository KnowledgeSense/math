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
int main(int argc,char**argv){if(argc!=8)return 1;int N=std::stoi(argv[1]);I p(argv[2],argv[3]),u(argv[4],argv[5]),v(argv[6],argv[7]);I w[2]={u,v};I S=I(1)+sq(u)+sq(v),ss=sqrtI(S),l[2]={u/S,v/S};I pi;mpfi_const_pi(&pi.m);I step=pi/I(2*N),res3[4],resp[3];int ijk[4][3]={{0,0,0},{0,0,1},{0,1,1},{1,1,1}},ij[3][2]={{0,0},{0,1},{1,1}};auto start=std::chrono::steady_clock::now();
for(int k=0;k<N;++k){I th=hull(I(k)*step,I(k+1)*step),c=absI(cosI(th)),s=absI(sinI(th));for(int sign:{-1,1}){I d[2]={c,I(sign)*s},z=u*d[0]+v*d[1],az=absI(z),Q=powI(c,p)+powI(s,p)+powI(az,p),g=ss*powI(Q,-I(2)/p),b=z*powI(az,p-I(2))/Q,t=powI(az,p-I(2))/Q;
I L[2]={l[0]-I(2)*b*d[0],l[1]-I(2)*b*d[1]},L2[2][2];for(int i=0;i<2;++i)for(int j=0;j<2;++j)L2[i][j]=I(i==j)/S-I(2)*w[i]*w[j]/sq(S)-I(2)*((p-I(1))*t-p*sq(b))*d[i]*d[j];
I bb=(p-I(1))*(p-I(2))*signI(z)*powI(az,p-I(3))/Q-I(3)*p*(p-I(1))*b*t+I(2)*sq(p)*b*b*b;
for(int q=0;q<4;++q){int i=ijk[q][0],j=ijk[q][1],k=ijk[q][2];I L3=-I(2)*(I(i==j)*w[k]+I(i==k)*w[j]+I(j==k)*w[i])/sq(S)+I(8)*w[i]*w[j]*w[k]/(S*S*S)-I(2)*bb*d[i]*d[j]*d[k];I F=g*(L[i]*L[j]*L[k]+L2[i][j]*L[k]+L2[i][k]*L[j]+L2[j][k]*L[i]+L3);res3[q]=res3[q]+F;}
I ell=(powlog(c,p)+powlog(s,p)+powlog(az,p))/Q,R=I(2)/sq(p)*logI(Q)-I(2)/p*ell,tp=powlog(az,p-I(2))/Q-t*ell,bp=z*tp;
for(int q=0;q<3;++q){int i=ij[q][0],j=ij[q][1];I M=I(i==j)/S-w[i]*w[j]/sq(S)-I(2)*b*(l[i]*d[j]+l[j]*d[i])+(I(2)*(p+I(2))*sq(b)-I(2)*(p-I(1))*t)*d[i]*d[j];I Mp=-I(2)*bp*(l[i]*d[j]+l[j]*d[i])+(I(2)*sq(b)+I(4)*(p+I(2))*b*bp-I(2)*t-I(2)*(p-I(1))*tp)*d[i]*d[j];resp[q]=resp[q]+g*(R*M+Mp);}
}}
std::cout<<"MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" N "<<N<<"\n";for(int i=0;i<4;++i){std::cout<<"third "<<i<<" ";printI("",res3[i]*step);}for(int i=0;i<3;++i){std::cout<<"p_hessian "<<i<<" ";printI("",resp[i]*step);}std::cout<<"seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"\n";
}
