#pragma once
#include <cstdint>
#include <fstream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>
inline uint64_t extra_allowance(const std::string&s){
 if(s.empty()||s.size()>7||(s.size()>1&&s[0]=='0'))throw std::runtime_error("extra allowance syntax");
 uint64_t v=0;for(char c:s){if(c<'0'||c>'9')throw std::runtime_error("extra allowance syntax");v=10*v+c-'0';}
 if(v>5000000)throw std::runtime_error("extra per-field allowance exceeds 5000000");return v;
}
inline std::vector<uint64_t> generator_js(uint64_t m){
 std::vector<uint64_t> out;
 for(uint64_t j=1;j<m&&j<=64&&out.size()<8;++j)if(std::gcd(j,m)==1)out.push_back(j);
 return out;
}
struct ExtraCounter{
 uint64_t limit,used,q;std::string implementation;
 ExtraCounter(uint64_t cap,uint64_t order,const std::string&who):limit(cap),used(0),q(order),implementation(who){}
 ~ExtraCounter(){
  std::ofstream f("EXTRA_COUNTER_USAGE_"+implementation+".json");
  f<<"{\"implementation\":\""<<implementation<<"\",\"q\":"<<q<<",\"checks_completed\":"<<used<<",\"allowance\":"<<limit<<"}\n";
 }
 void check(uint64_t a,uint64_t j,uint64_t k){
  if(used>=limit){
   std::ofstream f("EXTRA_COUNTER_STOP_"+implementation+".json");
   f<<"{\"implementation\":\""<<implementation<<"\",\"q\":"<<q<<",\"checks_completed\":"<<used<<",\"allowance\":"<<limit<<",\"j\":"<<j<<",\"k\":"<<k<<",\"a\":"<<a<<"}\n";
   throw std::runtime_error("extra candidate-check allowance exhausted");
  }
  ++used;
 }
};
inline void write_extra_stages(uint64_t q,const std::vector<std::pair<uint64_t,uint64_t>>&stages){
 std::ofstream f("extras_"+std::to_string(q)+".tsv");if(!f)throw std::runtime_error("extra-stage output missing");
 f<<"j\tprefix_length\n";for(auto [j,k]:stages)f<<j<<'\t'<<k<<'\n';
}
