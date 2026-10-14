// C5 adaptive complement certificate. Fresh [4,6] interpolation constants 84,84,1.
// Fixed branch per p slab; never interpolate the maximum of vertexwise gaps.
// Uses the installed MPFI/MPFR libraries, with their published stable ABI.
#include <iostream>
#include <cmath>
#include <iomanip>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <vector>
#include <map>
#include <tuple>
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


I area(const I&p,const I&u,const I&v,const std::vector<I>&c,const std::vector<I>&s,const std::vector<I>&B,const I&step){I total,r=-I(2)/p;for(size_t k=0;k<c.size();++k){I z=u*c[k],w=v*s[k];total=total+powI(B[k]+powI(absI(z+w),p),r)+powI(B[k]+powI(absI(z-w),p),r);}return sqrtI(I(1)+sq(u)+sq(v))*step*total;}

const long DEN=1000L*(1L<<20);const int N=512;
using Key=std::tuple<long,long,long>;
std::map<Key,I> values;
std::map<long,std::vector<I>> angularB;
std::vector<I> cs,ss;
I step;
std::ofstream vertexlog;
I getarea(long k,long i,long j){Key key(k,i,j);auto found=values.find(key);if(found!=values.end())return found->second;
 I p=I(double(k))/I(double(DEN)),u=I(double(i))/I(double(DEN)),v=I(double(j))/I(double(DEN));
 auto it=angularB.find(k);if(it==angularB.end()){std::vector<I> temp;for(int a=0;a<N;++a)temp.push_back(powI(cs[a],p)+powI(ss[a],p));it=angularB.emplace(k,std::move(temp)).first;}
 I mid=area(p,u,v,cs,ss,it->second,step),eps=I(60)/I(N*N),answer=mid+hull(-eps,eps);
 values.emplace(key,answer);vertexlog<<k<<","<<i<<","<<j<<","<<DEN<<","<<std::setprecision(17)<<answer.lo()<<","<<answer.hi()<<"\n";return answer;
}
struct Cell{long lo[3],hi[3];int root,depth;char branch;};
int main(int argc,char**argv){if(argc!=2){std::cerr<<"output_prefix\n";return 1;}std::string prefix=argv[1];
 I pi;mpfi_const_pi(&pi.m);step=pi/I(2*N);for(int a=0;a<N;++a){I th=(I(a)+I(.5))*step;cs.push_back(absI(cosI(th)));ss.push_back(absI(sinI(th)));}
 long ticks[5]={0,100,900,950,1000},ps[5]={4000,4900,5000,5100,6000};std::vector<Cell> initial;
 for(int slab=0;slab<4;++slab)for(int i=0;i<4;++i)for(int j=0;j<=i;++j){long p0=ps[slab],p1=ps[slab+1];if(p1<=5100&&ticks[i]>=900&&ticks[j]>=900)continue;if(p0>=4900&&ticks[i]>=950&&ticks[j+1]<=100)continue;
 Cell b;b.lo[0]=p0*(1L<<20);b.hi[0]=p1*(1L<<20);b.lo[1]=ticks[i]*(1L<<20);b.hi[1]=ticks[i+1]*(1L<<20);b.lo[2]=ticks[j]*(1L<<20);b.hi[2]=ticks[j+1]*(1L<<20);b.root=initial.size();b.depth=0;b.branch=p1<=5000?'D':'T';initial.push_back(b);}
 assert(initial.size()==28);std::vector<Cell>stack;for(int i=int(initial.size())-1;i>=0;--i)stack.push_back(initial[i]);
 vertexlog.open(prefix+"_vertices.csv");vertexlog<<"p,u,v,denominator,area_lower,area_upper\n";
 std::ofstream leaves(prefix+"_leaves.csv"),tree(prefix+"_tree.csv");
 leaves<<"root,depth,branch,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,denominator,corner_gap_lower,interpolation_loss_upper,margin_lower\n";
 tree<<"root,depth,branch,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,decision,axis\n";
 int evaluated=0,passed=0,maxdepth=0;double worst=1e100;auto begin=std::chrono::steady_clock::now();
 std::cout<<"C5 FIXED-BRANCH COMPLEMENT MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" N512 precision80 roots28 second_upper84,84,1 area_error60/N^2 margin_target1/100000\n"<<std::flush;
 while(!stack.empty()){Cell b=stack.back();stack.pop_back();I widths[3];for(int j=0;j<3;++j)widths[j]=I(double(b.hi[j]-b.lo[j]))/I(double(DEN));
 I losses[3]={sq(widths[0])/I(8),I(84)*sq(widths[1])/I(8),I(84)*sq(widths[2])/I(8)};I loss=losses[0]+losses[1]+losses[2];
 I gap;bool first=true;
 for(int a=0;a<2;++a)for(int i=0;i<2;++i)for(int j=0;j<2;++j){long pk=a?b.hi[0]:b.lo[0],ui=i?b.hi[1]:b.lo[1],vj=j?b.hi[2]:b.lo[2];I ref=getarea(pk,DEN,b.branch=='D'?DEN:0),value=ref-getarea(pk,ui,vj);if(first){gap=value;first=false;}else gap=hull(gap,value);}
 I margin=gap-loss;bool good=(margin-I(1)/I(100000)).lo()>0;evaluated++;maxdepth=std::max(maxdepth,b.depth);
 tree<<b.root<<","<<b.depth<<","<<b.branch;for(int j=0;j<3;++j)tree<<","<<b.lo[j]<<","<<b.hi[j];
 if(good){passed++;worst=std::min(worst,margin.lo());tree<<",PASS,-1\n";leaves<<b.root<<","<<b.depth<<","<<b.branch;for(int j=0;j<3;++j)leaves<<","<<b.lo[j]<<","<<b.hi[j];leaves<<","<<DEN<<","<<std::setprecision(17)<<gap.lo()<<","<<loss.hi()<<","<<margin.lo()<<"\n";
 }else{if(b.depth>=28){tree<<",FAIL,-1\n";std::cerr<<"FAIL depth28 root"<<b.root<<"\n";return 2;}double scores[3]={losses[0].hi(),losses[1].hi(),losses[2].hi()};int axis=int(std::max_element(scores,scores+3)-scores);long sum=b.lo[axis]+b.hi[axis];if(sum%2){std::cerr<<"FAIL indivisible midpoint\n";return 3;}long mid=sum/2;Cell left=b,right=b;left.hi[axis]=mid;right.lo[axis]=mid;left.depth++;right.depth++;stack.push_back(right);stack.push_back(left);tree<<",SPLIT,"<<axis<<"\n";}
 if(evaluated%500==0){vertexlog.flush();leaves.flush();tree.flush();std::cout<<"evaluated "<<evaluated<<" leaves "<<passed<<" vertices "<<values.size()<<" pending "<<stack.size()<<" worst "<<std::setprecision(17)<<worst<<" depth "<<maxdepth<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n"<<std::flush;}}
 std::cout<<"COMPLETE PASS evaluated "<<evaluated<<" leaves "<<passed<<" vertices "<<values.size()<<" worst "<<std::setprecision(17)<<worst<<" depth "<<maxdepth<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<"\n";
}
