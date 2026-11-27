// Exact transfer of a complete near-maximum enumeration to a matrix with split rows.
// The caller generates the near list with verify_classical.cpp on this same ordered
// base and symmetry file. See PROOF.md for the completeness argument.
#include <algorithm>
#include <array>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>
using Row=std::vector<int>;
using Matrix=std::vector<Row>;
struct Strategy{int value;Row a,y;};
struct Op{Row pa,sa,pb,sb;};
void require(bool condition,const std::string& why){if(!condition)throw std::runtime_error(why);}
Matrix read_matrix(const char* file){
    std::ifstream f(file);require(bool(f),"cannot open matrix");Matrix a;std::string line;
    while(std::getline(f,line)){
        std::istringstream s(line);Row r;int v;
        while(s>>v){require(v>-1000000000&&v<1000000000,"coefficient too large");r.push_back(v);}
        require(s.eof(),"noninteger coefficient");
        if(!r.empty()){require(a.empty()||r.size()==a[0].size(),"ragged matrix");a.push_back(std::move(r));}
    }
    require(!a.empty(),"empty matrix");return a;
}
Row read_row(std::istream& f,int n){Row row(n);for(int& x:row)require(bool(f>>x),"short input");return row;}
void check_perm(Row p){std::sort(p.begin(),p.end());for(int i=0;i<int(p.size());i++)require(i==p[i],"invalid permutation");}
void check_signs(const Row& s){for(int x:s)require(x==1||x==-1,"invalid sign");}
int norm1(const Row& a){
    int s=0;
    #pragma omp simd reduction(+:s)
    for(int i=0;i<int(a.size());i++)s+=std::abs(a[i]);
    return s;
}

int main(int argc,char**argv){try{
    require(argc==13,"usage: check_near base lifted split_rows symmetry packed_near cutoff base_max threads gain_cap");
    Matrix M=read_matrix(argv[1]),K=read_matrix(argv[2]);int n=M.size(),m=M[0].size(),k=int(K.size())-n;
    int cutoff=std::stoi(argv[6]),C=std::stoi(argv[7]),threads=std::stoi(argv[8]);
    int margin=std::stoi(argv[12]);require(margin>=0 && margin<C,"bad near margin");int target=C-margin;
    require(k>=1&&k<=81&&int(K[0].size())==m&&cutoff>=0&&C>=cutoff&&threads>=1&&threads<=256,"bad size");
    std::ifstream rf(argv[3]);Row indices=read_row(rf,k);Row used(n);Matrix D(k,Row(m));std::string extra;
    require(!(rf>>extra),"extra split index");
    for(int h=0;h<k;h++){
        int i=indices[h];require(i>=0&&i<n&&!used[i],"invalid split index");used[i]=1;
        for(int j=0;j<m;j++){require(std::int64_t(K[i][j])+K[n+h][j]==2LL*M[i][j],"wrong row sum");D[h][j]=K[i][j]-M[i][j];}
    }
    for(int i=0;i<n;i++)if(!used[i])for(int j=0;j<m;j++)require(K[i][j]==2LL*M[i][j],"changed unsplit row");
    std::int64_t safety=0;
    for(const auto* mat:{&M,&D})for(const Row& r:*mat)for(int x:r)safety+=std::abs(x);
    require(safety<std::numeric_limits<int>::max(),"integer sum safety");
    std::ifstream sf(argv[4]);int prefix,reps,opcount;
    require(bool(sf>>prefix>>reps>>opcount)&&prefix>=1&&prefix<=24&&reps>=1&&reps<=(1<<(prefix-1))&&opcount>=1&&opcount<=1024,"bad symmetry file");
    read_row(sf,reps);std::vector<Op> ops;
    for(int g=0;g<opcount;g++){
        Op op{read_row(sf,n),read_row(sf,n),read_row(sf,m),read_row(sf,m)};
        check_perm(op.pa);check_perm(op.pb);check_signs(op.sa);check_signs(op.sb);
        for(int i=0;i<n;i++)for(int j=0;j<m;j++)require(M[op.pa[i]][op.pb[j]]==op.sa[i]*op.sb[j]*M[i][j],"non-symmetry");
        ops.push_back(std::move(op));
    }
    require(!(sf>>extra),"trailing symmetry data");
    // Map each split displacement into its partner, up to exchanging the two
    // settings. The protected base prefix is binary and disjoint from all pairs.
    require(std::all_of(indices.begin(),indices.end(),[&](int i){return i>=prefix;}),"split in protected prefix");
    Row location(n,-1);for(int h=0;h<k;h++)location[indices[h]]=h;
    for(const auto& g:ops)for(int h=0;h<k;h++) {
        int i=indices[h],other=location[g.pa[i]];
        require(other>=0,"split set fails symmetry check");
        bool same=true,opposite=true;
        for(int j=0;j<m;j++){
            int transformed=g.sa[i]*g.sb[j]*D[h][j];
            same &= D[other][g.pb[j]]==transformed;
            opposite &= D[other][g.pb[j]]==-transformed;
        }
        require(same||opposite,"displacement fails symmetry check");
    }
    struct Near {std::uint32_t score,mask[3];};
    auto read_u32=[](std::istream& f){
        std::uint32_t x=0;
        for(int j=0;j<4;j++){int b=f.get();require(b!=EOF,"truncated packed enumeration");x|=std::uint32_t(b)<<(8*j);}
        return x;
    };
    std::ifstream nf(argv[5],std::ios::binary);char marker[8];nf.read(marker,8);
    require(std::string(marker,8)=="K3SIG001","wrong enumeration header");
    require(int(read_u32(nf))==n && int(read_u32(nf))==m && int(read_u32(nf))==cutoff,"wrong packed dimensions or cutoff");
    std::uint64_t nrec=read_u32(nf);nrec|=std::uint64_t(read_u32(nf))<<32;
    require(nrec>0 && nrec<=std::numeric_limits<int>::max() && n<=96,"invalid packed size");
    std::vector<Near> near(nrec);int highest=0;std::size_t maxrecord=0;
    static_assert(sizeof(Near)==16);
    const std::uint32_t one=1;
    if(*reinterpret_cast<const unsigned char*>(&one)==1){
        nf.read(reinterpret_cast<char*>(near.data()),std::streamsize(near.size()*sizeof(Near)));
        require(bool(nf),"truncated packed enumeration");
    }else{
        for(auto& item:near){item.score=read_u32(nf);for(auto& mask:item.mask)mask=read_u32(nf);}
    }
    for(std::size_t z=0;z<near.size();++z){
        const auto& item=near[z];
        require(int(item.score)>cutoff,"enumeration contains a subthreshold score");
        if(int(item.score)>highest){highest=item.score;maxrecord=z;}
    }
    require(highest==C&&nf.peek()==EOF,"wrong base maximum or trailing data");
    Row cost(k),suffix_cost(k+1);
    for(int h=0;h<k;h++)cost[h]=norm1(D[h]);
    for(int h=k-1;h>=0;h--)suffix_cost[h]=suffix_cost[h+1]+cost[h];
    int greatest=std::stoi(argv[9]);require(greatest>=0 && greatest<=target-cutoff,"unsupported signed gain cap");
    // Norms of all subsets of small row blocks bound an arbitrary union by
    // the triangle inequality. Enumerate each local ternary sign state.
    constexpr int block_width=8;
    int blocks=(k+block_width-1)/block_width;
    std::vector<Row> local_norms(blocks);
    for(int block=0;block<blocks;block++){
        int begin=block*block_width,end=std::min(begin+block_width,k);
        Row& table=local_norms[block];table.assign(1<<(end-begin),0);
        Matrix states(end-begin+1,Row(m));
        auto visit=[&](auto&& self,int h,int subset)->void{
            if(h==end){table[subset]=std::max(table[subset],norm1(states[h-begin]));return;}
            auto& next=states[h-begin+1];const auto& prev=states[h-begin];
            next=prev;self(self,h+1,subset);
            for(int sign:{1,-1}){
                for(int j=0;j<m;j++)next[j]=prev[j]+sign*D[h][j];
                self(self,h+1,subset|(1<<(h-begin)));
            }
        };
        visit(visit,begin,0);
    }
    auto block_bound=[&](std::uint64_t mask){
        int ans=0;for(int g=0;g<blocks&&mask;g++,mask>>=block_width)ans+=local_norms[g][mask&255u];
        return ans;
    };
    require(k<=63,"block mask exceeds 63 rows");
    const std::uint64_t all=(std::uint64_t(1)<<k)-1;

    require(std::int64_t(cutoff)+greatest<=target,"enumeration is too shallow for this lift");
    std::cout<<"near="<<near.size()<<" maps="<<ops.size()<<" split_rows="<<k<<" signed_gain_cap="<<greatest<<" cutoff="<<cutoff<<std::endl;
    Row prefix_caps(1<<(prefix-1),greatest);
    if(argc>=11 && std::string(argv[10])!="-"){
        std::ifstream cf(argv[10]);int pat,cap;std::fill(prefix_caps.begin(),prefix_caps.end(),-1);
        while(cf>>pat>>cap){require(pat>=0&&pat<int(prefix_caps.size())&&cap>=0&&cap<=greatest,"bad prefix cap");prefix_caps[pat]=cap;}
        require(cf.eof(),"invalid cap input");
    }
    Row max_abs(m); for(const auto& d:D)for(int j=0;j<m;j++)max_abs[j]=std::max(max_abs[j],std::abs(d[j]));
    require(std::int64_t(k)*norm1(max_abs)<2147483647,"chord safety bound");
    const int stride=1;
    struct Hit{std::uint32_t score;std::array<std::uint32_t,5> mask{};};
    require(n+k<=160,"too many rows for active masks");
    std::vector<std::vector<Hit>> collected(threads);
    std::cout<<"root stride "<<stride<<std::endl;
    std::atomic<int> done{0};
    int answer=C; Row attaining(n);for(int i=0;i<n;i++)attaining[i]=((near[maxrecord].mask[i/32]>>(i%32))&1u)?-1:1;for(int i:indices)attaining.push_back(attaining[i]);
    std::uint64_t examined=0,branches=0;
    #pragma omp parallel num_threads(threads) reduction(+:examined,branches)
    {
        Row a(n),active(k),signs(k);Matrix stack(k+1,Row(m)),trial(k+1,Row(m));int local=target,cap=greatest;Row witness;Row orientation(m);
        // Test all opposite signs for the current choice of cancelled base rows.
        auto test=[&](auto&& self,int l,int depth,int remaining,int score)->void{
            if(std::int64_t(score)+remaining<=local)return;
            if(l==depth){
                witness=a;for(int i:indices)witness.push_back(a[i]);
                for(int q=0;q<depth;q++){int h=active[q];witness[indices[h]]=signs[q];witness[n+h]=-signs[q];}
                Hit item{};item.score=score;
                for(int i=0;i<n+k;i++)if(witness[i]<0)item.mask[i/32]|=std::uint32_t(1)<<(i%32);
                collected[omp_get_thread_num()].push_back(item);return;
            }
            int h=active[l];const Row& d=D[h];const Row& y=trial[l];Row& next=trial[l+1];
            for(int s:{1,-1}){
                int norm=0;
                #pragma omp simd reduction(+:norm)
                for(int j=0;j<m;j++){next[j]=y[j]+s*d[j];norm+=std::abs(next[j]);}
                signs[l]=s;self(self,l+1,depth,remaining-cost[h],norm);
            }
        };
        // Starting from a violating partial strategy, fill the missing base
        // signs in reverse row order, choosing a maximizing sign each time.
        // Norms increase along that chain. Traversing it backwards suffices.
        auto visit=[&](auto&& self,int pos,int depth,int spent,int norm,std::uint64_t removed)->void{
            const Row& x=stack[depth];
            if(std::int64_t(norm)+std::min(cap,block_bound(removed))>local){
                ++examined;
                int flip_cost=0;
                #pragma omp simd reduction(+:flip_cost)
                for(int j=0;j<m;j++){orientation[j]=x[j]>=0?1:-1;flip_cost+=std::max(0,depth*max_abs[j]-std::abs(x[j]));}
                std::int64_t upper=std::int64_t(norm)+2LL*flip_cost;
                for(int q=0;q<depth && upper<=local;q++){
                    const auto& d=D[active[q]];int dot=0;
                    #pragma omp simd reduction(+:dot)
                    for(int j=0;j<m;j++)dot+=orientation[j]*d[j];
                    upper+=std::abs(dot);
                }
                if(upper>local){trial[0]=x;test(test,0,depth,spent,norm);}
            }
            for(int h=pos;h<k;h++){
                int future=std::min({cap,block_bound(removed|(all&(~std::uint64_t(0)<<h)))});
                if(std::int64_t(norm)+future<=local)break;
                int i=indices[h],s=a[i];const Row& row=M[i];Row& next=stack[depth+1];
                int next_norm=0;
                #pragma omp simd reduction(+:next_norm)
                for(int j=0;j<m;j++){next[j]=x[j]-s*row[j];next_norm+=std::abs(next[j]);}
                if(next_norm>norm||std::int64_t(next_norm)+future<=local)continue;
                // Convexity already ensures a nondecreasing reverse chain.
                // Requiring the better of the two signs further removes duplicates.
                int other=0;
                #pragma omp simd reduction(+:other)
                for(int j=0;j<m;j++)other+=std::abs(next[j]-s*row[j]);
                if(other>norm || (other==norm && s<0))continue;
                ++branches;active[depth]=h;self(self,h+1,depth+1,spent+cost[h],next_norm,removed|(std::uint64_t(1)<<h));
            }
        };
        // Reduce the prefix of the enlarged strategy first. Deletions and
        // additions in the completion argument never touch the prefix.
        #pragma omp for schedule(dynamic,128)
        for(int vindex=0;vindex<int(near.size());vindex+=stride){
            const auto& v=near[vindex];
            const int progress=done.fetch_add(1,std::memory_order_relaxed);
            if(progress&&progress%2000000==0)std::cout<<"roots processed "<<progress<<std::endl;
            cap=prefix_caps[(v.mask[0]>>1)&(prefix_caps.size()-1)];
            require(cap>=0 && (v.mask[0]&1u)==0,"unknown or unnormalized prefix");
            if(std::int64_t(v.score)+cap<=local)continue;
            Row& y=stack[0];std::fill(y.begin(),y.end(),0);
            for(int i=0;i<n;i++){
                a[i]=((v.mask[i/32]>>(i%32))&1u)?-1:1;
                for(int j=0;j<m;j++)y[j]+=a[i]*M[i][j];
            }
            require(norm1(y)==int(v.score),"base strategy has the wrong score");
            visit(visit,0,0,0,v.score,0);
        }
        #pragma omp critical(lift_answer)
        {if(local>answer){answer=local;attaining=witness;}}
    }
    std::ofstream out(argv[11],std::ios::binary);
    std::size_t total_hits=0;
    for(const auto& part:collected)for(const auto& h:part){
        total_hits++;for(auto v:{h.score,h.mask[0],h.mask[1],h.mask[2],h.mask[3],h.mask[4]})
            for(int j=0;j<4;j++)out.put(static_cast<char>((v>>(8*j))&255));
    }
    out.close();require(bool(out),"could not save active assignments");
    std::cout<<"COMPLETE_ACTIVE "<<total_hits<<" above "<<target<<std::endl;
    std::cout<<"monotone removal branches "<<branches<<'\n';
    std::vector<std::int64_t> final_columns(m);
    for(int i=0;i<n+k;i++)for(int j=0;j<m;j++)final_columns[j]+=std::int64_t(attaining[i])*K[i][j];
    std::int64_t score=0;for(auto v:final_columns)score+=std::abs(v);
    require(score==2LL*answer,"attaining signs do not match");
    std::cout<<"MATCHED_ATTAINED "<<score<<" blocks_examined "<<examined<<"\nSIGNS";
    for(int a:attaining)std::cout<<' '<<a;std::cout<<'\n';return 0;
}catch(const std::exception& e){std::cerr<<"ERROR "<<e.what()<<'\n';return 2;}}
