#include <cstdint>
#include <vector>
#include <iostream>
#include <fstream>
#include <stdexcept>
int main(){using U=uint64_t; const uint32_t M=25000000;std::vector<uint32_t>phi(M+1);std::vector<uint8_t>omega(M+1,0),degree(M+1,0);for(uint32_t i=0;i<=M;++i)phi[i]=i;for(uint32_t p=2;p<=M;++p)if(!omega[p]){for(uint32_t x=p;x<=M;x+=p){phi[x]=phi[x]/p*(p-1);++omega[x];}for(U x=p,e=1;x<=M;++e){degree[x]=e;if(x>M/p)break;x*=p;}}std::ofstream f("INDEPENDENT_RESIDUAL_ORDERS.csv");f<<"q,characteristic,degree,phi_q_minus_1,omega_q_minus_1,W_q_minus_1\n";U checked=0,bad=0,sum=0,maxq=0;for(uint32_t q=8;q<=M;++q)if(degree[q]){++checked;U t=phi[q-1],W=U(1)<<omega[q-1];if((t-2)*(t-2)<9*W*W*q){uint32_t p=q;if(degree[q]>1){p=2;while(q%p)++p;}f<<q<<','<<p<<','<<unsigned(degree[q])<<','<<t<<','<<unsigned(omega[q-1])<<','<<W<<'\n';++bad;sum+=q;maxq=q;}}std::cout<<"{\"prime_power_orders_checked\":"<<checked<<",\"residual_count\":"<<bad<<",\"residual_sum\":"<<sum<<",\"max_residual\":"<<maxq<<"}\n";if(checked!=1566722||bad!=2693||sum!=659462866||maxq!=18888871)throw std::runtime_error("order audit discrepancy");}
