// Independent order-32 filter. No author code is imported.
// The normalized log rank is dim(span{row_i+row_0, all_ones})-1.
// This quotients by constant vectors instead of explicitly dephasing.
// Gaussian elimination uses LOW pivots, unlike the author's HIGH pivots.
#include <zlib.h>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <fstream>
#include <array>
#include <string>
#include <stdexcept>
static int hx(char c){
 if(c>='0'&&c<='9')return c-'0';
 if(c>='A'&&c<='F')return c-'A'+10;
 if(c>='a'&&c<='f')return c-'a'+10;
 return -1;
}
static bool ws(char c){return c==' '||c=='\t'||c=='\r'||c=='\n';}
int main(int argc,char**argv){
 try{
  if(argc!=3)throw std::runtime_error("need input.gz output.txt");
  gzFile f=gzopen(argv[1],"rb");if(!f)throw std::runtime_error("open failed");
  gzbuffer(f,1<<20);char buffer[1024];uint64_t count=0,kept=0;
  std::array<uint64_t,9> hist{};std::ofstream out(argv[2]);
  while(gzgets(f,buffer,sizeof(buffer))){
   if(!strchr(buffer,'\n'))throw std::runtime_error("missing newline or long line");
   std::array<uint32_t,32> A{};const char*p=buffer;
   for(int i=0;i<32;++i){
    while(ws(*p))++p;int digits=0;
    while(hx(*p)>=0){if(++digits>8)throw std::runtime_error("overflow");A[i]=(A[i]<<4)|hx(*p++);}
    if(!digits)throw std::runtime_error("missing hexadecimal row");
   }
   while(ws(*p))++p;if(*p)throw std::runtime_error("extra data");
   // Rank of D + <one>. Injection of the constant vector is deliberate.
   std::array<uint32_t,32> piv{};piv[0]=0xffffffffu;int rank=1;
   for(int i=0;i<32 && rank<9;++i){
    uint32_t v=A[i]^A[0];
    for(int j=0;j<32 && v;++j){
     if((v>>j)&1u){
      if(piv[j])v^=piv[j];else{piv[j]=v;++rank;break;}
     }
    }
   }
   const int logrank=rank-1;++hist[logrank];++count;
   if(logrank<=7){
    // Every retained matrix must actually be Hadamard, irrespective of source.
    for(int i=0;i<32;++i)for(int j=0;j<i;++j)
      if(__builtin_popcount(A[i]^A[j])!=16)throw std::runtime_error("non-Hadamard retained matrix");
    out<<count<<" "<<logrank<<" "<<buffer;++kept;
   }
  }
  int ec;const char*em=gzerror(f,&ec);
  if(ec!=Z_OK&&ec!=Z_STREAM_END)throw std::runtime_error(em);
  if(gzclose(f)!=Z_OK)throw std::runtime_error("gzip close failed");
  if(count!=6857010)throw std::runtime_error("classification count differs");
  std::cout<<"classes "<<count<<" retained "<<kept<<"\n";
  for(int r=0;r<9;++r)std::cout<<r<<" "<<hist[r]<<"\n";
 }catch(std::exception&e){std::cerr<<e.what()<<"\n";return 1;}
}
