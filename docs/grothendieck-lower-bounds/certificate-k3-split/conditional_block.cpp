// Maximum four-choice block norm for each signing of the leading protected rows.
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>
using Row=std::vector<int>;using Matrix=std::vector<Row>;
int main(int argc,char**argv){try{
 if(argc!=4)throw std::runtime_error("usage: conditional_block rows.txt protected_width threads");
 int p=std::stoi(argv[2]),nt=std::stoi(argv[3]);if(p<1||p>18||nt<1)throw std::runtime_error("invalid prefix");
 Matrix r,d;std::vector<bool> alt;std::int64_t safe=0;int m=0;std::string line;std::ifstream f(argv[1]);
 while(std::getline(f,line)){
  Row v;int x;std::istringstream in(line);while(in>>x)v.push_back(x);if(!in.eof())throw std::runtime_error("noninteger entry");if(v.empty())continue;
  if(v.size()%2)throw std::runtime_error("bad width");if(!m)m=v.size()/2;if(2*m!=int(v.size()))throw std::runtime_error("inconsistent width");
  r.emplace_back(v.begin(),v.begin()+m);d.emplace_back(v.begin()+m,v.end());alt.push_back(std::any_of(d.back().begin(),d.back().end(),[](int a){return a!=0;}));
  for(int j=0;j<m;j++)safe+=std::max(std::abs(std::int64_t(r.back()[j])),std::abs(std::int64_t(d.back()[j])));
 }
 const int n=r.size();if(n<p||safe>=2147483647||std::any_of(alt.begin(),alt.begin()+p,[](bool t){return t;}))throw std::runtime_error("unsafe input or variable prefix");
 Row tails(n+1,0);auto norm=[&](const Row& v){int s=0;for(int x:v)s+=std::abs(x);return s;};
 auto dfs=[&](auto&& self,Matrix& stack,int i,int value,int& best)->void{
  if(i==n){best=std::max(best,value);return;}if(std::int64_t(value)+tails[i]<=best)return;
  const auto& prev=stack[i];Row& next=stack[i+1];
  for(int t=0;t<=int(alt[i]);t++){const Row& b=t?d[i]:r[i];for(int s:{1,-1}){
    int z=0;
    #pragma omp simd reduction(+:z)
    for(int j=0;j<m;j++){next[j]=prev[j]+s*b[j];z+=std::abs(next[j]);}
    self(self,stack,i+1,z,best);
  }}
 };Matrix stack(n+1,Row(m));
 for(int i=n-1;i>=p;i--){
  int best=tails[i+1];for(int t=0;t<=int(alt[i]);t++){stack[i+1]=t?d[i]:r[i];dfs(dfs,stack,i+1,norm(stack[i+1]),best);}tails[i]=best;
 }
 int num=1<<(p-1);Row out(num);
 #pragma omp parallel num_threads(nt)
 {
 Matrix work(n+1,Row(m));
 #pragma omp for schedule(dynamic,1)
 for(int mask=0;mask<num;mask++){
  Row& v=work[p];v=r[0];for(int i=1;i<p;i++)for(int j=0;j<m;j++)v[j]+=((mask>>(i-1))&1?-1:1)*r[i][j];
  int best=0;dfs(dfs,work,p,norm(v),best);out[mask]=best;
 }
 }
 for(int z:out)std::cout<<z<<" ";std::cout<<"\n";return 0;
}catch(std::exception& e){std::cerr<<e.what()<<"\n";return 2;}}
