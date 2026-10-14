// Stream the complete primary order-32 classification; retain binary log rank <=7.
// Input: McKay hex rows, 32 tokens per line. Exact F_2 operations only.
#include <zlib.h>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <fstream>
#include <chrono>
int main(int argc,char**argv){
 if(argc!=3){std::cerr<<"usage: filter input.gz output.txt\n";return 2;}
 gzFile f=gzopen(argv[1],"rb");if(!f)return 3;gzbuffer(f,1<<20);
 std::ofstream out(argv[2]);char line[2048];uint64_t count=0,kept=0;std::array<uint64_t,9> hist{};
 auto start=std::chrono::steady_clock::now();
 while(gzgets(f,line,sizeof(line))){
  if(!strchr(line,'\n')&&!gzeof(f)){std::cerr<<"too long\n";return 4;}
  char*p=line;std::array<uint32_t,32>rows{};
  for(int i=0;i<32;i++){char*end;unsigned long v=strtoul(p,&end,16);if(end==p||v>0xffffffffUL){std::cerr<<"parse fail "<<count<<"\n";return 5;}rows[i]=(uint32_t)v;p=end;}
  while(*p==' '||*p=='\n'||*p=='\r'||*p=='\t')p++;
  if(*p){std::cerr<<"excess tokens\n";return 6;}
  std::array<uint32_t,32>basis{};int rank=0;
  for(int i=1;i<32&&rank<8;i++){
   uint32_t v=rows[i]^rows[0];if(v&1)v^=0xffffffffU;
   while(v){int j=31-__builtin_clz(v);if(basis[j])v^=basis[j];else{basis[j]=v;rank++;break;}}
  }
  hist[rank]++;count++;
  if(rank<=7){out<<count<<" "<<rank<<" "<<line;kept++;}
  if(count%1000000==0){double s=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();std::cerr<<count<<" classes, "<<kept<<" retained, "<<s<<" seconds\n";}
 }
 int err;const char*msg=gzerror(f,&err);if(err!=Z_OK&&err!=Z_STREAM_END){std::cerr<<"gzip error "<<err<<" "<<msg<<"\n";return 7;}
 if(gzclose(f)!=Z_OK)return 8;
 std::cout<<"classes "<<count<<" retained "<<kept<<"\n";for(int i=0;i<=8;i++)std::cout<<i<<" "<<hist[i]<<"\n";
 if(count!=6857010){std::cerr<<"unexpected class count\n";return 9;}
}
