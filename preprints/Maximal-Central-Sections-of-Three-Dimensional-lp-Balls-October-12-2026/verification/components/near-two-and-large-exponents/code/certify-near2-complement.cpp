#include <map>
#include <tuple>
// C6 near2 derivative-gap complement. New p-dependent interpolation bounds.
// Cached base jets preserve the original outward evaluations. Endpoint cells use direct interval subintegration.
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

// New fixed-sector p-Hessian probe. Author feasibility component, not a full cover.
I logI(const I&a){I b;mpfi_log(&b.m,&a.m);return b;}
I plog(const I&t,const I&p){if(t.hi()==0)return I(0);if(t.lo()>0)return powI(t,p)*logI(t);if(t.hi()<=.5){I z(t.hi());return hull(powI(z,p)*logI(z),I(0));}return I(-1,0);}

struct J {I x,a,b;J():x(0),a(0),b(0){} J(const I&v):x(v),a(0),b(0){} J(const I&v,const I&v1,const I&v2):x(v),a(v1),b(v2){} };
J operator+(const J&a,const J&b){return J(a.x+b.x,a.a+b.a,a.b+b.b);} J operator-(const J&a,const J&b){return J(a.x-b.x,a.a-b.a,a.b-b.b);} J operator-(const J&a){return J(-a.x,-a.a,-a.b);}
J operator*(const J&a,const J&b){return J(a.x*b.x,a.a*b.x+a.x*b.a,a.b*b.x+a.a*b.a+a.x*b.b);}
J operator/(const J&a,const J&b){I x=a.x/b.x,y=(a.a-x*b.a)/b.x;return J(x,y,(a.b-x*b.b-y*b.a)/b.x);}
J powJ(const J&a,const I&b){if(a.a.lo()==0&&a.a.hi()==0&&a.b.lo()==0&&a.b.hi()==0)return J(powI(a.x,b));I g=powI(a.x,b),d=b*powI(a.x,b-I(1));return J(g,d*a.a,d*a.b+b*(b-I(1))/I(2)*powI(a.x,b-I(2))*sq(a.a));}
J sqJ(const J&a){return a*a;}
J logJ(const J&a){return J(logI(a.x),a.a/a.x,a.b/a.x-sq(a.a)/(I(2)*sq(a.x)));}
J plogJ(const J&t,const I&p){if(t.x.hi()==0)return J(I(0));if(t.x.lo()==0){assert(t.a.lo()==0&&t.a.hi()==0&&t.b.lo()==0&&t.b.hi()==0);return J(plog(t.x,p));}return powJ(t,p)*logJ(t);}

J absJ(const J&a){if(a.x.lo()>0)return a;if(a.x.hi()<0)return -a;if(a.x.lo()==0&&a.x.hi()==0&&a.a.lo()==0&&a.a.hi()==0&&a.b.lo()==0&&a.b.hi()==0)return J(I(0));std::cerr<<"invalid root jet\n";std::exit(3);}
J darea_integrand(const I&p,const I&u,const I&v,const I&theta,bool jet){
 I cx=absI(cosI(theta)),sx=absI(sinI(theta));J c(cx),s(sx);if(jet){c=J(cx,-sx,-cx/I(2));s=J(sx,cx,-sx/I(2));}J out;J qc=powJ(c,p),qs=powJ(s,p),qcl=c.x.lo()>0?qc*logJ(c):plogJ(c,p),qsl=s.x.lo()>0?qs*logJ(s):plogJ(s,p);
 for(int sign:{-1,1}){J z=J(u)*c+J(v*I(sign))*s,az=jet?absJ(z):J(absI(z.x));J qz=powJ(az,p),qzl=az.x.lo()>0?qz*logJ(az):plogJ(az,p);J Q=qc+qs+qz,ell=(qcl+qsl+qzl)/Q;J g=J(sqrtI(I(1)+sq(u)+sq(v)))*powJ(Q,-I(2)/p);out=out+g*(J(I(2)/sq(p))*logJ(Q)-J(I(2)/p)*ell);}
 return out;
}
bool rootcell(const I&u,const I&v,const I&theta){I c=absI(cosI(theta)),s=absI(sinI(theta));if(c.lo()<=0||s.lo()<=0)return true;if(u.hi()==0&&v.hi()==0)return false;I z=u*c-v*s;return z.lo()<=0&&z.hi()>=0;}
I darea_jet(const I&p,const I&u,const I&v,int N){I pi;mpfi_const_pi(&pi.m);I h=pi/I(2*N),out;
 for(int k=0;k<N;k++){I th=I(k,k+1)*h;
  if(rootcell(u,v,th)){for(int j=0;j<16;j++){I z=(I(k)+I(j,j+1)/I(16))*h;out=out+h/I(16)*darea_integrand(p,u,v,z,false).x;}}
  else{auto z=darea_integrand(p,u,v,th,true),m=darea_integrand(p,u,v,(I(k)+I(.5))*h,false);out=out+h*m.x+h*h*h/I(12)*z.b;}}
 return out;
}


struct Base{J c,s,q,qe;};struct Angles{std::vector<Base> boxes,mids;I h;};std::map<long,Angles> angle_cache;
Base makebase(const I&p,const I&theta,bool jet){I cx=absI(cosI(theta)),sx=absI(sinI(theta));J c(cx),s(sx);if(jet){c=J(cx,-sx,-cx/I(2));s=J(sx,cx,-sx/I(2));}J qc=powJ(c,p),qs=powJ(s,p),qcl=c.x.lo()>0?qc*logJ(c):plogJ(c,p),qsl=s.x.lo()>0?qs*logJ(s):plogJ(s,p);return {c,s,qc+qs,qcl+qsl};}
J cached_integrand(const I&p,const I&u,const I&v,const Base&B,const I&pref,bool jet){J out;for(int sign:{-1,1}){J z=J(u)*B.c+J(v*I(sign))*B.s,az=jet?absJ(z):J(absI(z.x));J qz=powJ(az,p),qzl=az.x.lo()>0?qz*logJ(az):plogJ(az,p);J Q=B.q+qz,ell=(B.qe+qzl)/Q;J g=J(pref)*powJ(Q,-I(2)/p);out=out+g*(J(I(2)/sq(p))*logJ(Q)-J(I(2)/p)*ell);}return out;}
I darea_cached(long key,const I&p,const I&u,const I&v,int N){auto it=angle_cache.find(key);if(it==angle_cache.end()){Angles A;I pi;mpfi_const_pi(&pi.m);A.h=pi/I(2*N);for(int k=0;k<N;k++){A.boxes.push_back(makebase(p,I(k,k+1)*A.h,k!=0&&k!=N-1));A.mids.push_back(makebase(p,(I(k)+I(.5))*A.h,false));}it=angle_cache.emplace(key,std::move(A)).first;}
 const Angles&A=it->second;I out,pref=sqrtI(I(1)+sq(u)+sq(v));for(int k=0;k<N;k++){const auto&B=A.boxes[k];bool root=B.c.x.lo()<=0||B.s.x.lo()<=0;if(!root&&!(u.hi()==0&&v.hi()==0)){I z=u*B.c.x-v*B.s.x;root=(z.lo()<=0&&z.hi()>=0)||absI(z).lo()<=((u+v)*A.h).hi();}
 if(root){for(int j=0;j<16;j++){I z=(I(k)+I(j,j+1)/I(16))*A.h;out=out+A.h/I(16)*darea_integrand(p,u,v,z,false).x;}}
 else{auto z=cached_integrand(p,u,v,B,pref,true),m=cached_integrand(p,u,v,A.mids[k],pref,false);out=out+A.h*m.x+A.h*A.h*A.h/I(12)*z.b;}}return out;
}
J diagp_integrand(const I&p,const J&t){J x=powJ(t,p),y=powJ(J(I(1))-t,p),Q=J(I(1))+x+y;J xe=t.x.lo()>0?x*logJ(t):plogJ(t,p),nt=J(I(1))-t,ye=nt.x.lo()>0?y*logJ(nt):plogJ(nt,p);return J(I(3)*sqrtI(I(3)))*powJ(Q,-I(2)/p)*(J(I(2)/sq(p))*logJ(Q)-J(I(2)/p)*(xe+ye)/Q);}
I diagp(const I&p,int N){I out,h=I(1)/I(N);for(int k=0;k<N;k++){I box=I(k,k+1)/I(N);if(k==0||k==N-1){for(int j=0;j<16;j++)out=out+h/I(16)*diagp_integrand(p,J((I(k)+I(j,j+1)/I(16))*h)).x;}else{auto z=diagp_integrand(p,J(box,I(1),I(0))),m=diagp_integrand(p,J((I(k)+I(.5))*h));out=out+h*m.x+h*h*h/I(12)*z.b;}}return out;}
const long DEN=1000L*(1L<<20);const int N=256;
using Key=std::tuple<long,long,long>;std::map<Key,I> values;std::ofstream vertexlog;
I getarea(long k,long i,long j){Key key(k,i,j);auto f=values.find(key);if(f!=values.end())return f->second;I p=I(double(k))/I(double(DEN)),u=I(double(i))/I(double(DEN)),v=I(double(j))/I(double(DEN));I ans=(i==DEN&&j==DEN)?diagp(p,256):darea_cached(k,p,u,v,N);values.emplace(key,ans);vertexlog<<k<<","<<i<<","<<j<<","<<DEN<<","<<std::setprecision(17)<<ans.lo()<<","<<ans.hi()<<"\n";return ans;}
struct Cell{long lo[3],hi[3];int root,depth;char branch;};
int main(int argc,char**argv){if(argc!=4){std::cerr<<"first_root last_root output_prefix\n";return 1;}int firstRoot=std::stoi(argv[1]),lastRoot=std::stoi(argv[2]);std::string prefix=argv[3];
 std::vector<Cell> initial;
 for(int k=0;k<10;k++)for(int i=0;i<2;i++){Cell b;b.lo[0]=(2000+100*k)*(1L<<20);b.hi[0]=(2100+100*k)*(1L<<20);b.lo[1]=(i?900:0)*(1L<<20);b.hi[1]=(i?1000:900)*(1L<<20);b.lo[2]=0;b.hi[2]=900*(1L<<20);b.root=initial.size();b.depth=0;b.branch='D';initial.push_back(b);}
 assert(firstRoot>=0&&lastRoot<=20&&firstRoot<lastRoot);std::vector<Cell>stack;for(int i=lastRoot-1;i>=firstRoot;--i)stack.push_back(initial[i]);
 vertexlog.open(prefix+"_vertices.csv");vertexlog<<"p,u,v,denominator,area_lower,area_upper\n";
 std::ofstream leaves(prefix+"_leaves.csv"),tree(prefix+"_tree.csv");
 leaves<<"root,depth,branch,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,denominator,corner_gap_lower,interpolation_loss_upper,margin_lower\n";
 tree<<"root,depth,branch,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,decision,axis\n";
 int evaluated=0,passed=0,maxdepth=0;double worst=1e100;auto begin=std::chrono::steady_clock::now();
 std::cout<<"C6 NEAR2 DERIVATIVE GAP COMPLEMENT ZERO-ADJACENT DIRECT v4 MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" N256 precision80 roots20 second_upper_p=448/pl^4_normal=130/pl vertex_tjet_root16 margin_target1/1000000\n"<<std::flush;
 while(!stack.empty()){Cell b=stack.back();stack.pop_back();I widths[3];for(int j=0;j<3;++j)widths[j]=I(double(b.hi[j]-b.lo[j]))/I(double(DEN));
 I pl=I(double(b.lo[0]))/I(double(DEN)),Cp=I(448)/sq(sq(pl)),Cn=I(130)/pl;I losses[3]={Cp*sq(widths[0])/I(8),Cn*sq(widths[1])/I(8),Cn*sq(widths[2])/I(8)};I loss=losses[0]+losses[1]+losses[2];
 I gap;bool first=true;
 for(int a=0;a<2;++a)for(int i=0;i<2;++i)for(int j=0;j<2;++j){long pk=a?b.hi[0]:b.lo[0],ui=i?b.hi[1]:b.lo[1],vj=j?b.hi[2]:b.lo[2];I ref=getarea(pk,DEN,b.branch=='D'?DEN:0),value=ref-getarea(pk,ui,vj);if(first){gap=value;first=false;}else gap=hull(gap,value);}
 I margin=gap-loss;bool good=(margin-I(1)/I(1000000)).lo()>0;evaluated++;maxdepth=std::max(maxdepth,b.depth);
 tree<<b.root<<","<<b.depth<<","<<b.branch;for(int j=0;j<3;++j)tree<<","<<b.lo[j]<<","<<b.hi[j];
 if(good){passed++;worst=std::min(worst,margin.lo());tree<<",PASS,-1\n";leaves<<b.root<<","<<b.depth<<","<<b.branch;for(int j=0;j<3;++j)leaves<<","<<b.lo[j]<<","<<b.hi[j];leaves<<","<<DEN<<","<<std::setprecision(17)<<gap.lo()<<","<<loss.hi()<<","<<margin.lo()<<"\n";
 }else{if(b.depth>=28){tree<<",FAIL,-1\n";std::cerr<<"FAIL depth28 root"<<b.root<<"\n";return 2;}double scores[3]={losses[0].hi(),losses[1].hi(),losses[2].hi()};int axis=int(std::max_element(scores,scores+3)-scores);long sum=b.lo[axis]+b.hi[axis];if(sum%2){std::cerr<<"FAIL indivisible midpoint\n";return 3;}long mid=sum/2;Cell left=b,right=b;left.hi[axis]=mid;right.lo[axis]=mid;left.depth++;right.depth++;stack.push_back(right);stack.push_back(left);tree<<",SPLIT,"<<axis<<"\n";}
 if(evaluated%500==0){vertexlog.flush();leaves.flush();tree.flush();std::cout<<"evaluated "<<evaluated<<" leaves "<<passed<<" vertices "<<values.size()<<" pending "<<stack.size()<<" worst "<<std::setprecision(17)<<worst<<" depth "<<maxdepth<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n"<<std::flush;}}
 std::cout<<"COMPLETE PASS evaluated "<<evaluated<<" leaves "<<passed<<" vertices "<<values.size()<<" worst "<<std::setprecision(17)<<worst<<" depth "<<maxdepth<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n";
}
