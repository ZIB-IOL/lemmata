// Re-evaluate every archived row assignment, using exact integer arithmetic.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using R=std::vector<int64_t>;using M=std::vector<R>;
M read(const char* path){
    std::ifstream input(path);if(!input)throw std::runtime_error("matrix missing");
    M mat;std::string line;__int128 sum=0;
    while(std::getline(input,line)){std::istringstream in(line);R r;int64_t v;
        while(in>>v){if(v==INT64_MIN)throw std::runtime_error("entry size");sum+=v<0?-v:v;r.push_back(v);}
        if(!in.eof())throw std::runtime_error("invalid matrix");if(r.empty())continue;
        if(!mat.empty()&&r.size()!=mat[0].size())throw std::runtime_error("ragged matrix");mat.push_back(r);}
    if(mat.empty()||sum>=INT64_MAX)throw std::runtime_error("matrix too large");
    return mat;
}
int main(int argc,char**argv){try{
    if(argc!=5)throw std::runtime_error("usage: score_band matrix records reference threshold");
    M mat=read(argv[1]),ref=read(argv[3]);int n=mat.size(),m=mat[0].size();int64_t limit=std::stoll(argv[4]);
    if(int(ref.size())!=n||int(ref[0].size())!=m||n>160)throw std::runtime_error("inconsistent dimensions");
    std::ifstream f(argv[2],std::ios::binary);if(!f)throw std::runtime_error("missing sign file");
    R y(m),z(m);uint64_t count=0;int64_t maximum=-1;std::array<uint32_t,5> winner{};
    while(f.peek()!=EOF){std::array<uint32_t,6> record{};
        for(auto& w:record)for(int j=0;j<4;++j){int c=f.get();if(c==EOF)throw std::runtime_error("short sign file");w|=uint32_t(c)<<(8*j);}
        std::fill(y.begin(),y.end(),0);std::fill(z.begin(),z.end(),0);
        for(int i=0;i<n;++i){int s=(record[1+i/32]>>(i%32)&1)?-1:1;
            for(int j=0;j<m;++j){y[j]+=s*mat[i][j];z[j]+=s*ref[i][j];}}
        int64_t value=0,base=0;for(int j=0;j<m;++j){value+=std::abs(y[j]);base+=std::abs(z[j]);}
        if(base!=2LL*record[0]||int64_t(record[0])<=limit)throw std::runtime_error("incorrect reference score");
        if(value>maximum){maximum=value;std::copy(record.begin()+1,record.end(),winner.begin());}++count;
    }
    std::cout<<"{\"maximum\":"<<maximum<<",\"count\":"<<count<<",\"mask\":[";
    for(int i=0;i<5;++i){if(i)std::cout<<',';std::cout<<winner[i];}std::cout<<"]}\n";return 0;
}catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 2;}}
