// C6 near-p2 local certificate; formal full-domain GO 2026-10-10 11:03:21 UTC.
// All analytic formulas and new per-box derivative evaluations are for Hessian(partial_p A).
// New fixed-sector derivatives of Hessian(partial_p A), including p=2.
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
I plog(const I&t,const I&p){if(t.lo()>0)return powI(t,p)*logI(t);if(t.hi()<=.5){I z(t.hi());return hull(powI(z,p)*logI(z),I(0));}return I(-1,0);}
I plog2(const I&t,const I&p){if(t.lo()>0)return powI(t,p)*sq(logI(t));if(t.hi()<=.25){I z(t.hi());return hull(powI(z,p)*sq(logI(z)),I(0));}return I(0,1);}
std::array<I,7> variation(const I&p,const I&u,const I&v,int N){
 I S=I(1)+sq(u)+sq(v),U[2]={sq(u),sq(v)},A[2]={U[0]/S,U[1]/S},coef[3]={u*v,v,u};std::array<I,7> out;
 for(int k=0;k<N;k++){I t=I(k,k+1)/I(N),tau0[3]={I(1),t,I(1)-t};
  for(int sec=0;sec<3;sec++){
   I tau[3];if(sec==0){tau[0]=tau0[0];tau[1]=tau0[1];tau[2]=tau0[2];}if(sec==1){tau[0]=tau0[1];tau[1]=tau0[0];tau[2]=tau0[2];}if(sec==2){tau[0]=tau0[1];tau[1]=tau0[2];tau[2]=tau0[0];}
   I q[3],qe[3],qe2[3],Q,E,E2;for(int j=0;j<3;j++){I cp=powI(coef[j],p),tp=powI(tau[j],p),lc=logI(coef[j]);q[j]=cp*tp;qe[j]=cp*(tp*lc+plog(tau[j],p));qe2[j]=cp*(tp*sq(lc)+I(2)*lc*plog(tau[j],p)+plog2(tau[j],p));Q=Q+q[j];E=E+qe[j];E2=E2+qe2[j];}E=E/Q;E2=E2/Q;
   I W[2]={q[1]/Q,q[2]/Q},C[2]={qe[1]/Q-W[0]*E,qe[2]/Q-W[1]*E},D[2];
   for(int i=0;i<2;i++)D[i]=qe2[i+1]/Q-I(2)*E*qe[i+1]/Q+I(2)*W[i]*sq(E)-W[i]*E2;
   I L[2],Lp[2],Lpp[2],L2[2][2],L2p[2][2],L2pp[2][2];
   for(int i=0;i<2;i++){L[i]=-I(1)+A[i]+I(2)*W[i];Lp[i]=I(2)*C[i];Lpp[i]=I(2)*D[i];
    L2[i][i]=I(2)*A[i]*(I(1)-A[i])-I(2)*p*W[i]*(I(1)-W[i]);
    L2p[i][i]=-I(2)*W[i]*(I(1)-W[i])-I(2)*p*C[i]*(I(1)-I(2)*W[i]);
    L2pp[i][i]=-I(4)*C[i]*(I(1)-I(2)*W[i])-I(2)*p*(D[i]*(I(1)-I(2)*W[i])-I(2)*sq(C[i]));}
   L2[0][1]=L2[1][0]=-I(2)*A[0]*A[1]+I(2)*p*W[0]*W[1];
   L2p[0][1]=L2p[1][0]=I(2)*W[0]*W[1]+I(2)*p*(C[0]*W[1]+W[0]*C[1]);
   L2pp[0][1]=L2pp[1][0]=I(4)*(C[0]*W[1]+W[0]*C[1])+I(2)*p*(D[0]*W[1]+I(2)*C[0]*C[1]+W[0]*D[1]);
   I G=u*v*sqrtI(S)*powI(Q,-I(2)/p),R=I(2)*logI(Q)/sq(p)-I(2)*E/p,Rp=-I(4)*logI(Q)/(p*p*p)+I(4)*E/sq(p)-I(2)*(E2-sq(E))/p;
   I H[2][2],Hpp[2][2],Gp[2],Gpp[2];
   for(int i=0;i<2;i++){Gp[i]=G*(R*L[i]+Lp[i]);Gpp[i]=G*((sq(R)+Rp)*L[i]+I(2)*R*Lp[i]+Lpp[i]);for(int j=0;j<2;j++){
    I M=L[i]*L[j]+L2[i][j],Mp=Lp[i]*L[j]+L[i]*Lp[j]+L2p[i][j];
    H[i][j]=G*(R*M+Mp);Hpp[i][j]=G*((sq(R)+Rp)*M+I(2)*R*Mp+Lpp[i]*L[j]+I(2)*Lp[i]*Lp[j]+L[i]*Lpp[j]+L2pp[i][j]);}}
   I H3[4];int ijk[4][3]={{0,0,0},{0,0,1},{0,1,1},{1,1,1}};
   for(int h=0;h<4;h++){int i=ijk[h][0],j=ijk[h][1],k=ijk[h][2];I L3,L3p;
    if(i==k){L3=I(4)*A[i]*(I(1)-A[i])*(I(1)-I(2)*A[i])+I(2)*sq(p)*W[i]*(I(1)-W[i])*(I(1)-I(2)*W[i]);L3p=I(4)*p*W[i]*(I(1)-W[i])*(I(1)-I(2)*W[i])+I(2)*sq(p)*C[i]*(I(1)-I(6)*W[i]+I(6)*sq(W[i]));}
    else{int a=(i==j)?i:k,b=1-a;L3=-I(4)*A[a]*A[b]*(I(1)-I(2)*A[a])-I(2)*sq(p)*W[a]*W[b]*(I(1)-I(2)*W[a]);L3p=-I(4)*p*W[a]*W[b]*(I(1)-I(2)*W[a])-I(2)*sq(p)*(C[a]*W[b]*(I(1)-I(4)*W[a])+W[a]*C[b]*(I(1)-I(2)*W[a]));}
    I M=L[i]*L[j]*L[k]+L2[i][j]*L[k]+L2[i][k]*L[j]+L2[j][k]*L[i]+L3;
    I Mp=Lp[i]*L[j]*L[k]+L[i]*Lp[j]*L[k]+L[i]*L[j]*Lp[k]+L2p[i][j]*L[k]+L2[i][j]*Lp[k]+L2p[i][k]*L[j]+L2[i][k]*Lp[j]+L2p[j][k]*L[i]+L2[j][k]*Lp[i]+L3p;
    H3[h]=G*(R*M+Mp);
   }
   out[0]=out[0]+(H3[0]-I(3)*H[0][0]+I(2)*Gp[0])/(u*u*u);
   out[1]=out[1]+(H3[1]-H[0][1])/(u*u*v);out[2]=out[2]+(H3[2]-H[0][1])/(u*v*v);
   out[3]=out[3]+(H3[3]-I(3)*H[1][1]+I(2)*Gp[1])/(v*v*v);
   out[4]=out[4]+(Hpp[0][0]-Gpp[0])/sq(u);out[5]=out[5]+Hpp[0][1]/(u*v);out[6]=out[6]+(Hpp[1][1]-Gpp[1])/sq(v);
  }
 }
 for(auto &r:out)r=r/I(N);return out;
}
struct J {I x,a,b;J():x(0),a(0),b(0){} J(const I&v):x(v),a(0),b(0){} J(const I&v,const I&v1,const I&v2):x(v),a(v1),b(v2){} };
J operator+(const J&a,const J&b){return J(a.x+b.x,a.a+b.a,a.b+b.b);} J operator-(const J&a,const J&b){return J(a.x-b.x,a.a-b.a,a.b-b.b);} J operator-(const J&a){return J(-a.x,-a.a,-a.b);}
J operator*(const J&a,const J&b){return J(a.x*b.x,a.a*b.x+a.x*b.a,a.b*b.x+a.a*b.a+a.x*b.b);}
J operator/(const J&a,const J&b){I x=a.x/b.x,y=(a.a-x*b.a)/b.x;return J(x,y,(a.b-x*b.b-y*b.a)/b.x);}
J powJ(const J&a,const I&b){if(a.a.lo()==0&&a.a.hi()==0&&a.b.lo()==0&&a.b.hi()==0)return J(powI(a.x,b));I g=powI(a.x,b),d=b*powI(a.x,b-I(1));return J(g,d*a.a,d*a.b+b*(b-I(1))/I(2)*powI(a.x,b-I(2))*sq(a.a));}
J sqJ(const J&a){return a*a;}
J logJ(const J&a){return J(logI(a.x),a.a/a.x,a.b/a.x-sq(a.a)/(I(2)*sq(a.x)));}
J plogJ(const J&t,const I&p){if(t.x.lo()==0){assert(t.a.lo()==0&&t.a.hi()==0&&t.b.lo()==0&&t.b.hi()==0);return J(plog(t.x,p));}return powJ(t,p)*logJ(t);}
std::array<J,3> calcSectorH(const I&p,const I&u,const I&v,const J&t){
 I S=I(1)+sq(u)+sq(v),U[2]={sq(u),sq(v)},coef[3]={u*v,v,u};std::array<J,3> out;J tau0[3]={J(I(1)),t,J(I(1))-t};
 for(int sec=0;sec<3;sec++){
  J tau[3];if(sec==0){tau[0]=tau0[0];tau[1]=tau0[1];tau[2]=tau0[2];}if(sec==1){tau[0]=tau0[1];tau[1]=tau0[0];tau[2]=tau0[2];}if(sec==2){tau[0]=tau0[1];tau[1]=tau0[2];tau[2]=tau0[0];}
  J q[3],qe[3],Q,E;for(int j=0;j<3;j++){I cp=powI(coef[j],p);J tp=powJ(tau[j],p);q[j]=J(cp)*tp;qe[j]=J(cp)*(tp*J(logI(coef[j]))+plogJ(tau[j],p));Q=Q+q[j];E=E+qe[j];}E=E/Q;
  J W[2]={q[1]/Q,q[2]/Q},C[2]={qe[1]/Q-W[0]*E,qe[2]/Q-W[1]*E};
  J L[2],Lp[2],L2[2][2],L2p[2][2];for(int i=0;i<2;i++){L[i]=J(-I(1)+U[i]/S)+J(I(2))*W[i];Lp[i]=J(I(2))*C[i];L2[i][i]=J(I(2)*U[i]/S-I(2)*sq(U[i])/sq(S))-J(I(2)*p)*W[i]*(J(I(1))-W[i]);L2p[i][i]=-J(I(2))*W[i]*(J(I(1))-W[i])-J(I(2)*p)*C[i]*(J(I(1))-J(I(2))*W[i]);}
  L2[0][1]=L2[1][0]=J(-I(2)*U[0]*U[1]/sq(S))+J(I(2)*p)*W[0]*W[1];L2p[0][1]=L2p[1][0]=J(I(2))*W[0]*W[1]+J(I(2)*p)*(C[0]*W[1]+W[0]*C[1]);
  J G=J(u*v*sqrtI(S))*powJ(Q,-I(2)/p),R=J(I(2)/sq(p))*logJ(Q)-J(I(2)/p)*E;
  J H[2][2];for(int i=0;i<2;i++)for(int j=0;j<2;j++)H[i][j]=G*(R*(L[i]*L[j]+L2[i][j])+Lp[i]*L[j]+L[i]*Lp[j]+L2p[i][j]);
  out[0]=out[0]+(H[0][0]-G*(R*L[0]+Lp[0]))/J(sq(u));out[1]=out[1]+H[0][1]/J(u*v);out[2]=out[2]+(H[1][1]-G*(R*L[1]+Lp[1]))/J(sq(v));
 }
 return out;
}
std::array<I,3> sectorTaylor(const I&p,const I&u,const I&v,int N){
 std::array<I,3> out;I h=I(1)/I(N);
 for(int k=0;k<N;k++){I box=I(k,k+1)/I(N);
  if(k==0||k==N-1){auto z=calcSectorH(p,u,v,J(box));for(int i=0;i<3;i++)out[i]=out[i]+h*z[i].x;}
  else{auto z=calcSectorH(p,u,v,J(box,I(1),I(0))),m=calcSectorH(p,u,v,J((I(k)+I(.5))/I(N)));for(int i=0;i<3;i++)out[i]=out[i]+h*m[i].x+h*h*h/I(12)*z[i].b;}
 }
 return out;
}
const long DEN=1000L*(1L<<20);
struct Cell{long lo[3],hi[3];int depth,root;};
int main(int argc,char**argv){if(argc!=5){std::cerr<<"D_or_T first_root last_root output_prefix\n";return 1;}
char type=argv[1][0];if(type!='D'){std::cerr<<"only diagonal derivative neighborhood accepted\n";return 1;}int first=std::stoi(argv[2]),last=std::stoi(argv[3]);std::string out=argv[4];
std::vector<Cell> initial;
for(int k=0;k<10;++k)for(int i=0;i<2;++i)for(int j=0;j<2;++j){Cell b; b.depth=0;b.root=initial.size();
 long base[3]={2000+100*k,900+50*i,900+50*j};
 long widths[3]={100,50,50};for(int a=0;a<3;++a){b.lo[a]=base[a]*(1L<<20);b.hi[a]=(base[a]+widths[a])*(1L<<20);}initial.push_back(b);}
assert(first>=0&&last<=int(initial.size())&&first<last);
std::vector<Cell> stack;for(int i=last-1;i>=first;--i)stack.push_back(initial[i]);
std::ofstream csv(out+".csv"),tree(out+"_tree.csv");
csv<<"root,depth,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,denominator,h11_lo,h11_hi,h12_lo,h12_hi,h22_lo,h22_hi";
for(int j=0;j<7;++j)csv<<",d"<<j<<"_lo,d"<<j<<"_hi";csv<<",err11,err12,err22,eigen_upper\n";
tree<<"root,depth,p_lo,p_hi,u_lo,u_hi,v_lo,v_hi,decision,axis\n";
int evaluated=0,passed=0,depthmax=0;double worst=-1e100;auto begin=std::chrono::steady_clock::now();
std::cout<<"C6 NEAR2 HESSIAN OF P-DERIVATIVE NEW SECTOR CERTIFICATE MPFI "<<mpfi_get_version()<<" MPFR "<<mpfr_get_version()<<" H_N128 D_N128 precision80 type "<<type<<" roots "<<first<<" "<<last<<"\n"<<std::flush;
while(!stack.empty()){Cell b=stack.back();stack.pop_back();I center[3],radius[3],range[3];for(int j=0;j<3;++j){center[j]=I(double(b.lo[j]+b.hi[j]))/I(double(2*DEN));radius[j]=I(double(b.hi[j]-b.lo[j]))/I(double(2*DEN));range[j]=hull(I(double(b.lo[j]))/I(double(DEN)),I(double(b.hi[j]))/I(double(DEN)));}
 auto hs=sectorTaylor(center[0],center[1],center[2],128);auto ds=variation(range[0],range[1],range[2],128);I bound[7];for(int j=0;j<7;++j)bound[j]=I(absI(ds[j]).hi());
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
