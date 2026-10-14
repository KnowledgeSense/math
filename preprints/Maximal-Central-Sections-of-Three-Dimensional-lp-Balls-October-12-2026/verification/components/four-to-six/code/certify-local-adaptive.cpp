// C5 adaptive complete-neighborhood certification. New per-box derivative bounds.
// Uses the installed MPFI/MPFR libraries, with their published stable ABI.
#include <iostream>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <chrono>
#include <vector>
#include <fstream>
#include <array>
#include <cassert>
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


I signI(const I&a){if(a.lo()>0)return I(1);if(a.hi()<0)return I(-1);return I(-1,1);} I logI(const I&a){I o;mpfi_log(&o.m,&a.m);return o;}
I powlog(const I&a,const I&b){if(a.lo()>0)return powI(a,b)*logI(a);I upper(0);if(a.hi()>1)upper=powI(I(a.hi()),b)*logI(I(a.hi()));return hull(I(-1),upper);}

std::array<I,7> derivatives(const I&p,const I&u,const I&v,int N){I w[2]={u,v};I S=I(1)+sq(u)+sq(v),ss=sqrtI(S),l[2]={u/S,v/S};I pi;mpfi_const_pi(&pi.m);I step=pi/I(2*N),res3[4],resp[3];int ijk[4][3]={{0,0,0},{0,0,1},{0,1,1},{1,1,1}},ij[3][2]={{0,0},{0,1},{1,1}};
for(int k=0;k<N;++k){I th=hull(I(k)*step,I(k+1)*step),c=absI(cosI(th)),s=absI(sinI(th));for(int sign:{-1,1}){I d[2]={c,I(sign)*s},z=u*d[0]+v*d[1],az=absI(z),Q=powI(c,p)+powI(s,p)+powI(az,p),g=ss*powI(Q,-I(2)/p),b=z*powI(az,p-I(2))/Q,t=powI(az,p-I(2))/Q;
I L[2]={l[0]-I(2)*b*d[0],l[1]-I(2)*b*d[1]},L2[2][2];for(int i=0;i<2;++i)for(int j=0;j<2;++j)L2[i][j]=I(i==j)/S-I(2)*w[i]*w[j]/sq(S)-I(2)*((p-I(1))*t-p*sq(b))*d[i]*d[j];
I bb=(p-I(1))*(p-I(2))*signI(z)*powI(az,p-I(3))/Q-I(3)*p*(p-I(1))*b*t+I(2)*sq(p)*b*b*b;
for(int q=0;q<4;++q){int i=ijk[q][0],j=ijk[q][1],k=ijk[q][2];I L3=-I(2)*(I(i==j)*w[k]+I(i==k)*w[j]+I(j==k)*w[i])/sq(S)+I(8)*w[i]*w[j]*w[k]/(S*S*S)-I(2)*bb*d[i]*d[j]*d[k];I F=g*(L[i]*L[j]*L[k]+L2[i][j]*L[k]+L2[i][k]*L[j]+L2[j][k]*L[i]+L3);res3[q]=res3[q]+F;}
I ell=(powlog(c,p)+powlog(s,p)+powlog(az,p))/Q,R=I(2)/sq(p)*logI(Q)-I(2)/p*ell,tp=powlog(az,p-I(2))/Q-t*ell,bp=z*tp;
for(int q=0;q<3;++q){int i=ij[q][0],j=ij[q][1];I M=I(i==j)/S-w[i]*w[j]/sq(S)-I(2)*b*(l[i]*d[j]+l[j]*d[i])+(I(2)*(p+I(2))*sq(b)-I(2)*(p-I(1))*t)*d[i]*d[j];I Mp=-I(2)*bp*(l[i]*d[j]+l[j]*d[i])+(I(2)*sq(b)+I(4)*(p+I(2))*b*bp-I(2)*t-I(2)*(p-I(1))*tp)*d[i]*d[j];resp[q]=resp[q]+g*(R*M+Mp);}
}}
std::array<I,7> out;for(int i=0;i<4;++i)out[i]=res3[i]*step;for(int i=0;i<3;++i)out[4+i]=resp[i]*step;return out;}

std::array<I,3> hessian(const I&p,const I&u,const I&v,int N){I pi;mpfi_const_pi(&pi.m);I step=pi/I(2*N);std::array<I,3> hs;
for(int k=0;k<N;++k){I th=hull(I(k)*step,I(k+1)*step),mid=(I(k)+I(.5))*step;
 if(roots(u,v,th)){Res r=calc(p,u,v,th,false);for(int j=0;j<3;++j)hs[j]=hs[j]+step*r.h[j].x;}
 else{Res r=calc(p,u,v,th,true),m=calc(p,u,v,mid,false);for(int j=0;j<3;++j)hs[j]=hs[j]+step*m.h[j].x+step*step*step/I(12)*r.h[j].b;}}
return hs;}
const long DEN=1000L*(1L<<20);
struct Cell{long lo[3],hi[3];int depth,root;};
int main(int argc,char**argv){if(argc!=5){std::cerr<<"D_or_T first_root last_root output_prefix\n";return 1;}
char type=argv[1][0];int first=std::stoi(argv[2]),last=std::stoi(argv[3]);std::string out=argv[4];
std::vector<Cell> initial;
for(int k=0;k<11;++k)for(int i=0;i<(type=='D'?2:1);++i)for(int j=0;j<2;++j){Cell b; b.depth=0;b.root=initial.size();
 long base[3]={(type=='D'?4000:4900)+100*k,(type=='D'?900:950)+50*i,(type=='D'?900:0)+50*j};
 long widths[3]={100,50,50};for(int a=0;a<3;++a){b.lo[a]=base[a]*(1L<<20);b.hi[a]=(base[a]+widths[a])*(1L<<20);}initial.push_back(b);}
assert(first>=0&&last<=int(initial.size())&&first<last);
std::vector<Cell> stack;for(int i=last-1;i>=first;--i)stack.push_back(initial[i]);
std::ofstream csv(out+".csv"),tree(out+"_tree.csv");
csv<<"root,depth,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,denominator,h11_lo,h11_hi,h12_lo,h12_hi,h22_lo,h22_hi";
for(int j=0;j<7;++j)csv<<",d"<<j<<"_lo,d"<<j<<"_hi";csv<<",err11,err12,err22,eigen_upper\n";
tree<<"root,depth,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,decision,axis\n";
int evaluated=0,passed=0,depthmax=0;double worst=-1e100;auto begin=std::chrono::steady_clock::now();
std::cout<<"C5 NEW PER-BOX DERIVATIVE CERTIFICATE MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" H_N128 D_N128 precision80 type "<<type<<" roots "<<first<<" "<<last<<"\n"<<std::flush;
while(!stack.empty()){Cell b=stack.back();stack.pop_back();I center[3],radius[3],range[3];for(int j=0;j<3;++j){center[j]=I(double(b.lo[j]+b.hi[j]))/I(double(2*DEN));radius[j]=I(double(b.hi[j]-b.lo[j]))/I(double(2*DEN));range[j]=hull(I(double(b.lo[j]))/I(double(DEN)),I(double(b.hi[j]))/I(double(DEN)));}
 auto hs=hessian(center[0],center[1],center[2],128);auto ds=derivatives(range[0],range[1],range[2],128);I bound[7];for(int j=0;j<7;++j)bound[j]=I(absI(ds[j]).hi());
 I err[3]={bound[0]*radius[1]+bound[1]*radius[2]+bound[4]*radius[0],bound[1]*radius[1]+bound[2]*radius[2]+bound[5]*radius[0],bound[2]*radius[1]+bound[3]*radius[2]+bound[6]*radius[0]};
 I aa=I(hs[0].hi())+err[0],bb=I(absI(hs[1]).hi())+err[1],cc=I(hs[2].hi())+err[2];
 I upper=(aa+cc)/I(2)+sqrtI(sq((aa-cc)/I(2))+sq(bb));
 bool good=(upper+I(1)/I(1000)).hi()<0;evaluated++;depthmax=std::max(depthmax,b.depth);
 tree<<b.root<<","<<b.depth;for(int j=0;j<3;++j)tree<<","<<b.lo[j]<<","<<b.hi[j];
 if(good){passed++;worst=std::max(worst,upper.hi());tree<<",PASS,-1\n";
 csv<<b.root<<","<<b.depth;for(int j=0;j<3;++j)csv<<","<<b.lo[j]<<","<<b.hi[j];csv<<","<<DEN;
 for(int j=0;j<3;++j)csv<<","<<std::setprecision(17)<<hs[j].lo()<<","<<hs[j].hi();for(int j=0;j<7;++j)csv<<","<<ds[j].lo()<<","<<ds[j].hi();csv<<","<<err[0].hi()<<","<<err[1].hi()<<","<<err[2].hi()<<","<<upper.hi()<<"\n";
 }else{if(b.depth>=24){tree<<",FAIL,-1\n";std::cerr<<"FAIL depth24 root"<<b.root<<"\n";return 2;}
 double score[3]={radius[0].hi()*std::max(bound[4].hi()+bound[5].hi(),bound[6].hi()+bound[5].hi()),radius[1].hi()*std::max(bound[0].hi()+bound[1].hi(),bound[2].hi()+bound[1].hi()),radius[2].hi()*std::max(bound[1].hi()+bound[2].hi(),bound[3].hi()+bound[2].hi())};
 int axis=int(std::max_element(score,score+3)-score);long total=b.lo[axis]+b.hi[axis];if(total%2){std::cerr<<"FAIL indivisible split\n";return 3;}long mid=total/2;Cell left=b,right=b;left.hi[axis]=mid;right.lo[axis]=mid;left.depth++;right.depth++;stack.push_back(right);stack.push_back(left);tree<<",SPLIT,"<<axis<<"\n";}
 if(evaluated%100==0){csv.flush();tree.flush();std::cout<<"evaluated "<<evaluated<<" leaves "<<passed<<" pending "<<stack.size()<<" worst "<<std::setprecision(17)<<worst<<" depth "<<depthmax<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n"<<std::flush;}}
 std::cout<<"COMPLETE PASS evaluated "<<evaluated<<" leaves "<<passed<<" worst "<<std::setprecision(17)<<worst<<" depth "<<depthmax<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n";
}
