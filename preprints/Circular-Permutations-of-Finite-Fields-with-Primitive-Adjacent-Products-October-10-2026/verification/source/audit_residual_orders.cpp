#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
using U=uint64_t;
int main(int argc,char**argv){
 if(argc!=2)throw std::runtime_error("supply original residual CSV");
 const uint32_t cap=25000000;
 // Independent smallest-prime-factor sieve; no reuse of the author's totient sieve.
 std::vector<uint32_t> least(cap+1,0),primes;
 for(uint32_t i=2;i<=cap;++i){if(!least[i]){least[i]=i;primes.push_back(i);}for(uint32_t p:primes){U z=U(i)*p;if(z>cap||p>least[i])break;least[z]=p;}}
 struct PP{uint32_t q,p,e;};std::vector<PP>orders;
 for(U p:primes)for(U q=p,e=1;q<=cap;q*=p,++e){if(q>=8)orders.push_back({uint32_t(q),uint32_t(p),uint32_t(e)});if(q>cap/p)break;}
 std::sort(orders.begin(),orders.end(),[](const PP&a,const PP&b){return a.q<b.q;});
 std::ofstream csv("AUDITED_RESIDUAL_ORDERS.csv");csv<<"q,characteristic,degree,phi_q_minus_1,omega_q_minus_1,W_q_minus_1\n";
 std::vector<uint32_t>bad;U sum=0,above_old=0;
 for(auto row:orders){U n=row.q-1,phi=n,W=1,omega=0;
  while(n>1){U p=least[n];phi=phi/p*(p-1);W*=2;++omega;while(n%p==0)n/=p;}
  if(phi<2||(phi-2)*(phi-2)<9*W*W*row.q){bad.push_back(row.q);sum+=row.q;above_old+=(row.q>18888871);csv<<row.q<<','<<row.p<<','<<row.e<<','<<phi<<','<<omega<<','<<W<<'\n';}
 }
 std::ifstream previous(argv[1]);if(!previous)throw std::runtime_error("original list missing");std::string line;std::getline(previous,line);std::vector<uint32_t>old;
 while(std::getline(previous,line))if(!line.empty())old.push_back(std::stoul(line.substr(0,line.find(','))));
 if(old!=bad)throw std::runtime_error("independent list does not equal original list; retain and inspect");
 std::cout<<"{\"finite_order_domain\":[8,"<<cap<<"],\"prime_power_orders_checked\":"<<orders.size()<<",\"residual_order_count\":"<<bad.size()<<",\"max_residual\":"<<bad.back()<<",\"sum_residual_orders\":"<<sum<<",\"failures_above_old_cutoff\":"<<above_old<<",\"original_order_list_exact_match\":true,\"algorithm\":\"smallest-prime-factor sieve plus per-order factorization\"}\n";
}
