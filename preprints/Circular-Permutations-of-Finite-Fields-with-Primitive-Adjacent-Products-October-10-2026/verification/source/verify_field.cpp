#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
#include "extra_limits.hpp"
using U=uint64_t;
void require(bool ok,const char* message){if(!ok)throw std::runtime_error(message);}
std::vector<std::string> split(const std::string&s,char c){std::vector<std::string>o;size_t pos=0;for(;;){auto at=s.find(c,pos);o.push_back(s.substr(pos,at-pos));if(at==std::string::npos)break;pos=at+1;}return o;}
uint32_t number(const std::string&s){require(!s.empty()&&s.size()<=8,"integer length");require(s.size()==1||s[0]!='0',"noncanonical number");U v=0;for(char c:s){require(c>='0'&&c<='9',"invalid integer token");v=v*10+c-'0';}require(v<=25000000,"integer range");return v;}
std::vector<std::string> read_lines(const std::string&path,bool empty=false){std::ifstream f(path,std::ios::binary);require(bool(f),"file missing");std::string s((std::istreambuf_iterator<char>(f)),{});require(s.size()<=20000000,"file size cap");if(s.empty()){require(empty,"empty file");return{};}require(s.back()=='\n',"missing final newline");s.pop_back();auto v=split(s,'\n');for(auto&l:v)require(!l.empty()&&l.find('\r')==std::string::npos,"empty/CR row");return v;}
struct Model{
 uint32_t p,q;int degree;std::vector<uint32_t> polynomial;
 uint32_t plus(uint32_t x,uint32_t y)const{
  if(p==2)return x^y;
  if(degree==1){U s=U(x)+y;return s>=p?s-p:s;}
  uint32_t out=0,place=1;
  for(int i=0;i<degree;++i){out+=((x%p+y%p)%p)*place;x/=p;y/=p;place*=p;}
  return out;
 }
 uint32_t times(uint32_t x,uint32_t y)const{
  if(degree==1)return U(x)*y%p;
  std::array<U,32>a{},b{},product{};
  for(int i=0;i<degree;++i){a[i]=x%p;b[i]=y%p;x/=p;y/=p;}
  for(int i=0;i<degree;++i)for(int j=0;j<degree;++j)product[i+j]=(product[i+j]+a[i]*b[j])%p;
  for(int i=2*degree-2;i>=degree;--i)for(int j=0;j<degree;++j)product[i-degree+j]=(product[i-degree+j]+p-product[i]*polynomial[j]%p)%p;
  uint32_t result=0;for(int i=degree-1;i>=0;--i)result=result*p+product[i];return result;
 }
};
int main(int argc,char**argv){try{
 require(argc==6,"supply certificate, expected q,p,degree,extra allowance");
 U extra_cap=extra_allowance(argv[5]);
 uint32_t eq=number(argv[2]),ep=number(argv[3]),ef=number(argv[4]);
 auto ls=read_lines(argv[1]);require(ls.size()==2,"exactly one field record required");
 require(ls[0]=="q\tp\tdegree\tg\tK\tpolynomial\tuncovered_file\textra_file","TSV header");
 auto row=split(ls[1],'\t');require(row.size()==8,"TSV exact columns");
 uint32_t q=number(row[0]),p=number(row[1]),f=number(row[2]),g=number(row[3]),K=number(row[4]);
 require(q==eq&&p==ep&&f==ef,"field metadata differs from expected order");
 require(q>=8&&q<=25000000&&p>=2&&f>=1&&f<=12,"field resource bounds");
 for(U d=2;d*d<=p;++d)require(p%d!=0,"characteristic not prime");
 U powp=1;for(uint32_t j=0;j<f;++j){require(powp<=25000000/p,"order overflow");powp*=p;}require(powp==q,"field order mismatch");
 Model F{p,q,int(f),{}};for(auto&v:split(row[5],',')){auto c=number(v);require(c<p,"coefficient range");F.polynomial.push_back(c);}
 require(F.polynomial.size()==f+1&&F.polynomial.back()==1,"monic polynomial length");
 require(f!=1||F.polynomial==std::vector<uint32_t>{0,1},"prime polynomial");
 require(row[6]=="uncovered_"+std::to_string(q)+".txt","noncanonical uncovered path");
 uint32_t n=q-1;require(g>0&&g<q,"generator range");require(K<=std::min<uint32_t>(1024,p==2?n:n/2),"witness prefix cap");
 require(row[7]=="extras_"+std::to_string(q)+".tsv","noncanonical extra-stage path");
 auto extra_lines=read_lines(row[7]);require(extra_lines[0]=="j\tprefix_length"&&extra_lines.size()<=8,"extra-stage header/count");
 std::vector<uint32_t> allowed;uint32_t m=n/2,extra_K=std::min<uint32_t>(1024,m);
 if(p!=2)for(uint32_t j=1;j<m&&j<=64&&allowed.size()<8;++j)if(std::gcd(j,m)==1)allowed.push_back(j);
 std::vector<std::pair<uint32_t,uint32_t>> stages;
 for(size_t line=1;line<extra_lines.size();++line){
  require(p!=2&&line<allowed.size(),"extra stage outside fixed family");auto fields=split(extra_lines[line],'\t');require(fields.size()==2,"extra-stage columns");
  uint32_t j=number(fields[0]),length=number(fields[1]);require(j==allowed[line],"extra stages omitted, reordered or duplicated");
  require(length>0&&length<=extra_K,"extra-stage prefix range");if(line+1<extra_lines.size())require(length==extra_K,"nonfinal extra prefix truncated");stages.push_back({j,length});
 }
 require(stages.empty()||K==extra_K,"extra stages before exhausted original core");
 ExtraCounter counter(extra_cap,q,"verifier");

 std::vector<uint8_t>seen(q,0),primitive(q,0);std::vector<uint32_t>exponents(n);uint32_t x=1;
 for(uint32_t e=0;e<n;++e){require(x>0&&x<q&&!seen[x],"generator does not enumerate all nonzero elements");seen[x]=1;exponents[e]=x;primitive[x]=(std::gcd(e,n)==1);x=F.times(x,g);}
 require(x==1,"multiplicative cycle does not close");
 // This complete orbit proves that every nonzero quotient-ring class is a unit.
 std::vector<uint32_t>factors;U rem=n;for(U d=2;d*d<=rem;++d)if(rem%d==0){factors.push_back(d);while(rem%d==0)rem/=d;}if(rem>1)factors.push_back(rem);
 auto power=[&](uint32_t a,U e){uint32_t v=1;for(;e;e>>=1,a=F.times(a,a))if(e&1)v=F.times(v,a);return v;};
 for(uint32_t candidate=1;candidate<g;++candidate){bool primitive_candidate=true;for(auto d:factors)if(power(candidate,n/d)==1){primitive_candidate=false;break;}require(!primitive_candidate,"generator is not least primitive encoding");}
 std::vector<std::array<uint32_t,3>> witnesses;
 for(uint32_t k=0;k<K;++k){U e=p==2?k:2*k+1;witnesses.push_back({exponents[e%n],exponents[(e+(p==2?1:2))%n],exponents[(e+2)%n]});}
 std::vector<uint32_t>recorded;for(auto&s:read_lines(row[6],true)){uint32_t a=number(s);require(a>0&&a<q,"nonzero offset range");require(recorded.empty()||recorded.back()<a,"duplicate/unsorted offset");recorded.push_back(a);}
 struct ExtraWitness{uint32_t x,y,j,k;};std::vector<ExtraWitness> additional;
 for(auto [j,length]:stages)for(uint32_t k=0;k<length;++k)additional.push_back({exponents[(2*k+1)%n],exponents[(2*k+1+2*j)%n],j,k});
 size_t missing=0,core_missing=0;
 for(uint32_t a=1;a<q;++a){bool good=false;
  for(auto&w:witnesses)if(primitive[F.plus(a,w[0])]&&primitive[F.plus(a,w[1])]&&(p!=2||primitive[F.plus(a,w[2])])){good=true;break;}
  if(!good){++core_missing;for(auto&w:additional){counter.check(a,w.j,w.k);if(primitive[F.plus(a,w.x)]&&primitive[F.plus(a,w.y)]){good=true;break;}}}
  if(!good){require(missing<recorded.size()&&recorded[missing]==a,"exact uncovered set differs");++missing;}
 }
 require(missing==recorded.size(),"extra uncovered offset");
 require(missing==0||K==std::min<uint32_t>(1024,p==2?n:n/2),"premature original witness stop");
 require(core_missing>0||stages.empty(),"unnecessary extra stages without a core miss");
 if(p!=2&&missing>0){require(stages.size()+1==allowed.size(),"uncovered offsets with omitted extra stages");if(!stages.empty())require(stages.back().second==extra_K,"uncovered offsets with truncated last stage");}
 std::cout<<"{\"q\":"<<q<<",\"p\":"<<p<<",\"degree\":"<<f<<",\"K\":"<<K<<",\"covered\":"<<(n-missing)<<",\"uncovered\":"<<missing<<",\"extra_stages\":"<<stages.size()<<",\"extra_checks\":"<<counter.used<<",\"status\":\"PASS\"}\n";
 }catch(const std::exception&e){std::cerr<<"REJECT: "<<e.what()<<"\n";return 2;}return 0;}
