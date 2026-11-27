// Enumerate every lifted signing whose matched original rows have one-norm above a cutoff.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>
using R=std::vector<int>;using M=std::vector<R>;
uint32_t number(std::istream& in){uint32_t x=0;for(int j=0;j<4;j++){int v=in.get();if(v==EOF)throw std::runtime_error("short packed input");x|=uint32_t(v)<<(8*j);}return x;}
int main(int argc,char**argv){try{
 if(argc!=9)throw std::runtime_error("usage: shallow base split_indices packed_base threshold threads output");
 std::ifstream bf(argv[1]);M mat;std::string line;int m=0;int64_t safe=0;while(std::getline(bf,line)){
  std::istringstream f(line);int v;R row;while(f>>v){safe+=std::abs(int64_t(v));row.push_back(v);}if(!f.eof())throw std::runtime_error("bad input");if(row.empty())continue;
  if(!m)m=row.size();if(int(row.size())!=m)throw std::runtime_error("ragged matrix");mat.push_back(row);}
 if(mat.empty()||safe>=2147483647)throw std::runtime_error("unsafe matrix");int n=mat.size();std::ifstream rf(argv[2]);R I;int i;while(rf>>i){if(i<0||i>=n||std::find(I.begin(),I.end(),i)!=I.end())throw std::runtime_error("bad split index");I.push_back(i);}
 int k=I.size(),T=std::stoi(argv[4]),nt=std::stoi(argv[5]);if(n>96||n+k>160||nt<1||nt>256)throw std::runtime_error("bad dimensions");
 // The surrogate is a rounded version of the final matrix. The caller adds
 // back its total one-norm rounding error before choosing the screening cutoff.
 M K;std::ifstream wf(argv[7]);while(std::getline(wf,line)){R row;std::istringstream f(line);int v;while(f>>v)row.push_back(v);if(!f.eof())throw std::runtime_error("bad surrogate");if(!row.empty())K.push_back(row);}
 if(int(K.size())!=n+k)throw std::runtime_error("bad surrogate height");
 for(const auto& row:K)if(int(row.size())!=m)throw std::runtime_error("bad surrogate width");
 for(int j=0;j<m;j++){std::int64_t total=0;for(const auto& row:K)total+=std::abs(std::int64_t(row[j]));if(total>=2147483647)throw std::runtime_error("surrogate column overflow");}
 M bM=K,eM(k,R(m));for(int h=0;h<k;h++)for(int j=0;j<m;j++){bM[I[h]][j]=K[I[h]][j]+K[n+h][j];eM[h][j]=K[I[h]][j]-K[n+h][j];}
 std::int64_t gate=std::stoll(argv[8]);
 R coord(m);std::vector<int64_t> cost(k);
 for(int h=0;h<k;h++)for(int j=0;j<m;j++){coord[j]=std::max(coord[j],std::abs(eM[h][j]));cost[h]+=std::abs(eM[h][j]);}

 std::ifstream f(argv[3],std::ios::binary);char h[8];f.read(h,8);if(std::string(h,8)!="K3SIG001"||number(f)!=unsigned(n)||number(f)!=unsigned(m)||int(number(f))>T)throw std::runtime_error("packed header");
 uint64_t count=number(f);count|=uint64_t(number(f))<<32;using Rec=std::array<uint32_t,4>;std::vector<Rec> starts;
 for(uint64_t j=0;j<count;j++){Rec r;for(auto& v:r)v=number(f);if(int(r[0])>T)starts.push_back(r);}if(f.peek()!=EOF)throw std::runtime_error("extra records");
 using Hit=std::array<uint32_t,6>;std::vector<std::vector<Hit>> hits(nt);uint64_t nodes=0;
 #pragma omp parallel num_threads(nt) reduction(+:nodes)
 {
 M stack(k+1,R(m)),ystack(k+1,R(m)),work(k+1,R(m));R a(n),indices(k),orientation(m);auto& bucket=hits[omp_get_thread_num()];Hit base{};
 #pragma omp for schedule(dynamic,32)
 for(int jj=0;jj<int(starts.size());jj++){
  const auto& s=starts[jj];std::fill(stack[0].begin(),stack[0].end(),0);base={};
  for(int i=0;i<n;i++){a[i]=(s[1+i/32]>>(i%32)&1)?-1:1;if(a[i]<0)base[1+i/32]|=uint32_t(1)<<(i%32);for(int j=0;j<m;j++)stack[0][j]+=a[i]*mat[i][j];}
  std::fill(ystack[0].begin(),ystack[0].end(),0);for(int i=0;i<n;i++)for(int j=0;j<m;j++)ystack[0][j]+=a[i]*bM[i][j];
  for(int z=0;z<k;z++)if(a[I[z]]<0)base[1+(n+z)/32]|=uint32_t(1)<<((n+z)%32);
  int initial=0;for(int x:stack[0])initial+=std::abs(x);if(initial!=int(s[0]))std::abort();
  auto visit=[&](auto&& self,int pos,int depth,int norm)->void{
    nodes++;Hit rec=base;rec[0]=norm;
    int64_t yscore=0,flip=0;const R& yy=ystack[depth];
    #pragma omp simd reduction(+:yscore,flip)
    for(int j=0;j<m;j++){
       const int mag=std::abs(yy[j]);yscore+=mag;orientation[j]=yy[j]>=0?1:-1;
       flip+=std::max<int64_t>(0,int64_t(depth)*coord[j]-mag);
    }
    int64_t totalcost=0;for(int l=0;l<depth;l++)totalcost+=cost[indices[l]];
    auto possible=[&](){
        if(yscore+totalcost<=gate)return false;
        int64_t bound=yscore+2*flip;
        for(int l=0;l<depth && bound<=gate;l++){
            int64_t dot=0;const auto& d=eM[indices[l]];
            #pragma omp simd reduction(+:dot)
            for(int j=0;j<m;j++)dot+=int64_t(orientation[j])*d[j];
            bound+=std::abs(dot);
        }
        return bound>gate;
    };

    auto emit=[&](auto&& recurse,int h,Hit r)->void{
       if(h==depth){int64_t value=0;
           #pragma omp simd reduction(+:value)
           for(int j=0;j<m;j++)value+=std::abs(work[h][j]);
           if(value>gate)bucket.push_back(r);return;}
       int z=indices[h],i=I[z];uint32_t x=uint32_t(1)<<(i%32),y=uint32_t(1)<<((n+z)%32);
       for(int j=0;j<m;j++)work[h+1][j]=work[h][j]+eM[z][j];
       r[1+i/32]&=~x;r[1+(n+z)/32]|=y;recurse(recurse,h+1,r);
       for(int j=0;j<m;j++)work[h+1][j]=work[h][j]-eM[z][j];
       r[1+i/32]|=x;r[1+(n+z)/32]&=~y;recurse(recurse,h+1,r);
    };if(possible()){work[0]=ystack[depth];emit(emit,0,rec);}
    const auto& x=stack[depth];
    for(int h=pos;h<k;h++){
       int i=I[h],sg=a[i],v=0;auto& y=stack[depth+1];
       #pragma omp simd reduction(+:v)
       for(int j=0;j<m;j++){y[j]=x[j]-sg*mat[i][j];v+=std::abs(y[j]);}
       if(v<=T||v>norm)continue;int other=0;
       #pragma omp simd reduction(+:other)
       for(int j=0;j<m;j++)other+=std::abs(y[j]-sg*mat[i][j]);
       if(other>norm)continue;for(int j=0;j<m;j++)ystack[depth+1][j]=ystack[depth][j]-sg*bM[i][j];indices[depth]=h;self(self,h+1,depth+1,v);
    }
  };visit(visit,0,0,initial);
 }
 }
 std::ofstream out(argv[6],std::ios::binary);uint64_t cnt=0;
 for(const auto& bucket:hits)for(const auto& rec:bucket){for(auto x:rec)for(int j=0;j<4;j++)out.put(char((x>>(8*j))&255u));cnt++;}
 out.close();if(!out)throw std::runtime_error("output failed");std::cout<<"SHALLOW_COMPLETE roots "<<starts.size()<<" partials "<<nodes<<" signed_records "<<cnt<<" threshold "<<T<<"\n";return 0;
}catch(std::exception& e){std::cerr<<e.what()<<"\n";return 2;}}
