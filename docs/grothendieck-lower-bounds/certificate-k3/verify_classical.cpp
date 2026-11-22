// Independently verify C(M) <= cutoff using exact integer branch and bound.
// Supplied tail bounds are untrusted and are re-proved shortest-tail-first.
// No code from the upstream IBB implementation is used here.
// Usage: verify_threshold original.txt ordered.txt tails.txt cutoff threads [split]
// tails[k] bounds the rows k,...,n-1 (zero based); exactly n+1 entries, tails[n]=0.
#include <algorithm>
#include <atomic>
#include <chrono>
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

using Row = std::vector<int32_t>;
using Matrix = std::vector<Row>;
using U = uint64_t;

struct SymmetryRestriction {
    int prefix=0;
    std::vector<bool> allowed;
};

struct Counterexample {
    U value;
    std::vector<int8_t> signs;
};

static int64_t read_integer_token(const std::string& token) {
    size_t consumed=0;
    const int64_t value=std::stoll(token,&consumed);
    if(consumed!=token.size())throw std::runtime_error("Invalid non-integer token");
    return value;
}

static Matrix read_matrix(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("Cannot open matrix: " + path);
    Matrix rows;
    std::string line;
    while (std::getline(in, line)) {
        std::istringstream stream(line);
        std::vector<int32_t> row;
        std::string token;
        while (stream >> token) {
            const int64_t x=read_integer_token(token);
            if (x < -INT32_MAX || x > INT32_MAX) throw std::runtime_error("Entry out of range");
            row.push_back(int32_t(x));
        }
        if (!stream.eof()) throw std::runtime_error("Invalid non-integer matrix token");
        if (row.empty()) continue;
        if (!rows.empty() && row.size() != rows.front().size()) throw std::runtime_error("Ragged matrix");
        rows.push_back(std::move(row));
    }
    if (rows.empty()) throw std::runtime_error("Empty matrix");
    return rows;
}

// Plain-text symmetry certificate: prefix_length representative_count op_count;
// representative masks (bit 1 means sign -1); then for each operation the row
// permutation, row signs, column permutation, column signs. Every map is
// checked against the ACTUAL reordered matrix. No group closure assumption is
// needed: each map is invertible and preserves the objective. Images of the
// representative prefixes must cover every pattern, which makes their inverses
// send every arbitrary strategy into an allowed prefix without changing value.
static SymmetryRestriction verify_symmetry(const std::string& path, const Matrix& a) {
    std::ifstream in(path);
    int p,r,g;
    if (!(in>>p>>r>>g) || p<1 || p>24 || p>int(a.size()) || r<1 || g<1 || g>1024)
        throw std::runtime_error("Invalid symmetry certificate header");
    const int n=int(a.size()),m=int(a[0].size());
    const U patterns=U(1)<<(p-1);
    if (U(r)>patterns) throw std::runtime_error("Too many representatives");
    SymmetryRestriction result{p,std::vector<bool>(patterns,false)};
    std::vector<U> representatives;
    for (int j=0;j<r;++j) {
        U mask;
        if (!(in>>mask) || mask>=patterns || result.allowed[mask]) throw std::runtime_error("Invalid representative mask");
        result.allowed[mask]=true;
        representatives.push_back(mask);
    }
    std::vector<bool> covered(patterns,false);
    for (int op=0;op<g;++op) {
        std::vector<int> pa(n),sa(n),pb(m),sb(m);
        for (auto* v : {&pa,&sa,&pb,&sb}) for (int& x:*v) if (!(in>>x)) throw std::runtime_error("Truncated symmetry certificate");
        for (auto* v : {&pa,&pb}) {
            auto sorted=*v;std::sort(sorted.begin(),sorted.end());
            for (int k=0;k<int(sorted.size());++k) if(sorted[k]!=k) throw std::runtime_error("Non-permutation symmetry map");
        }
        for (auto* v : {&sa,&sb}) for(int x:*v) if(x!=1 && x!=-1) throw std::runtime_error("Invalid symmetry sign");
        for (int i=0;i<p;++i) if(pa[i]>=p) throw std::runtime_error("Symmetry does not preserve protected prefix");
        for (int i=0;i<n;++i) for(int j=0;j<m;++j)
            if(a[pa[i]][pb[j]]!=sa[i]*sb[j]*a[i][j]) throw std::runtime_error("Claimed map is not an exact signed matrix symmetry");
        std::vector<int> transformed(p);
        for (U mask:representatives) {
            for(int i=0;i<p;++i) {
                const int sign=i==0?1:((mask>>(i-1))&1?-1:1);
                transformed[pa[i]]=sa[i]*sign;
            }
            U image=0;
            for(int i=1;i<p;++i) if(transformed[i]*transformed[0]<0) image|=U(1)<<(i-1);
            covered[image]=true;
        }
    }
    std::string extra;
    if(in>>extra)throw std::runtime_error("Unexpected trailing symmetry data");
    if(std::find(covered.begin(),covered.end(),false)!=covered.end())throw std::runtime_error("Symmetry representatives do not cover every normalized prefix");
    std::cout<<"Verified "<<g<<" exact signed automorphisms and coverage of "<<patterns<<" prefix patterns by "<<r<<" representatives."<<std::endl;
    return result;
}

struct ProofSearch {
    int n, m, threads, split;
    const Matrix& matrix;
    const std::vector<U>& tails;
    U cutoff;
    const SymmetryRestriction* restriction=nullptr;
    unsigned max_counterexamples=1;
    bool enumerate_all=false;
    std::vector<Counterexample> counterexamples{};
    std::atomic<bool> failure{false};
    std::atomic<U> violating_value{0};

    // The input partial sum has signed 32-bit entries. Because total |M_ij|
    // is strictly below INT32_MAX, every partial sum, abs(), and norm is safe.
    // Norm + tail is accumulated in 64 bits. Every call restores its input v.
    void dfs(int k, int32_t* v, int8_t* signs, U norm, U& nodes) {
        ++nodes;
        if ((nodes & 1023u) == 0 && failure.load(std::memory_order_relaxed)) return;
        if (norm + tails[k] <= cutoff) return;
        if (k == n) {
            #pragma omp critical(record_counterexample)
            {
                if(enumerate_all || counterexamples.size()<max_counterexamples) {
                    counterexamples.push_back(Counterexample{norm,std::vector<int8_t>(signs,signs+n)});
                    violating_value.store(norm,std::memory_order_relaxed);
                }
                if(!enumerate_all && counterexamples.size()>=max_counterexamples)failure.store(true,std::memory_order_relaxed);
            }
            return;
        }
        const int32_t* row = matrix[k].data();
        uint32_t plus_norm = 0;
        #pragma omp simd reduction(+:plus_norm)
        for (int j = 0; j < m; ++j) {
            v[j] += row[j];
            plus_norm += uint32_t(std::abs(v[j]));
        }
        signs[k]=1;
        dfs(k + 1, v, signs, plus_norm, nodes);
        uint32_t minus_norm = 0;
        #pragma omp simd reduction(+:minus_norm)
        for (int j = 0; j < m; ++j) {
            // Two subtractions avoid overflowing the intermediate 2*row[j].
            v[j] -= row[j];
            v[j] -= row[j];
            minus_norm += uint32_t(std::abs(v[j]));
        }
        signs[k]=-1;
        dfs(k + 1, v, signs, minus_norm, nodes);
        #pragma omp simd
        for (int j = 0; j < m; ++j) v[j] += row[j];
    }

    bool prove(int start, U& total_nodes, U& total_tasks) {
        // Global sign reversal fixes the first row sign of this tail to +1.
        int count = std::min(split, n - start);
        if(start==0 && restriction)count=std::max(count,restriction->prefix);
        const int depth = start + count;
        const U tasks = U(1) << (count - 1);
        total_tasks = tasks;
        if(start==0 && restriction)total_tasks=(tasks/restriction->allowed.size())*std::count(restriction->allowed.begin(),restriction->allowed.end(),true);
        total_nodes = 0;
        std::atomic<U> finished_tasks{0};
        const U report_step=std::max<U>(1,total_tasks/20);
        #pragma omp parallel num_threads(threads) reduction(+:total_nodes)
        {
            std::vector<int32_t> v(m);
            std::vector<int8_t> signs(n,0);
            U local_nodes = 0;
            #pragma omp for schedule(dynamic,1)
            for (U mask = 0; mask < tasks; ++mask) {
                if(start==0 && restriction && !restriction->allowed[mask & (restriction->allowed.size()-1)])continue;
                if (failure.load(std::memory_order_relaxed)) continue;
                std::copy(matrix[start].begin(), matrix[start].end(), v.begin());
                std::fill(signs.begin(),signs.end(),0);
                signs[start]=1;
                for (int r = 1; r < count; ++r) {
                    const int sign = (mask & (U(1) << (r - 1))) ? -1 : 1;
                    signs[start+r]=int8_t(sign);
                    for (int j = 0; j < m; ++j) v[j] += sign * matrix[start+r][j];
                }
                uint32_t norm = 0;
                #pragma omp simd reduction(+:norm)
                for (int j = 0; j < m; ++j) norm += uint32_t(std::abs(v[j]));
                dfs(depth, v.data(), signs.data(), norm, local_nodes);
                if(start==0) {
                    const U done=finished_tasks.fetch_add(1,std::memory_order_relaxed)+1;
                    if(done%report_step==0 || done==total_tasks) {
                        #pragma omp critical(progress_output)
                        std::cout<<"Full prefix tasks completed "<<done<<"/"<<total_tasks<<std::endl;
                    }
                }
            }
            total_nodes += local_nodes;
        }
        return counterexamples.empty();
    }
};

int main(int argc, char** argv) {
    try {
        if (argc < 6) {
            std::cerr << "Usage: verify_threshold original.txt ordered.txt tails.txt cutoff threads split\n"
                      << "split defaults to 12; options: --tails-only, --symmetry certificate.txt,\n"
                      << "--counterexample-out file.json, --max-counterexamples N (default 1),\n"
                      << "--enumerate-above (exhaustively collect every retained leaf above cutoff).\n";
            return 2;
        }
        Matrix original = read_matrix(argv[1]), ordered = read_matrix(argv[2]);
        Matrix sorted_original = original, sorted_ordered = ordered;
        std::sort(sorted_original.begin(), sorted_original.end());
        std::sort(sorted_ordered.begin(), sorted_ordered.end());
        if (sorted_original != sorted_ordered) throw std::runtime_error("Ordered matrix is not an exact row permutation of original");
        const int n = int(ordered.size()), m = int(ordered[0].size());
        std::ifstream tail_stream(argv[3]);
        if (!tail_stream) throw std::runtime_error("Cannot open tail bounds");
        std::vector<U> supplied;
        std::string tail_token;
        while (tail_stream >> tail_token) {
            const int64_t t=read_integer_token(tail_token);
            if (t < 0) throw std::runtime_error("Negative tail bound");
            supplied.push_back(U(t));
        }
        if (!tail_stream.eof()) throw std::runtime_error("Invalid tail token");
        if (supplied.size() != size_t(n+1) || supplied[n] != 0) throw std::runtime_error("Expected n+1 tails and final zero");
        const U cutoff = std::stoull(argv[4]);
        const int threads = std::stoi(argv[5]);
        int split=12,arg=6;bool tails_only=false,enumerate_above=false;std::string symmetry_path,counterexample_path;
        unsigned max_counterexamples=1;
        if(arg<argc && argv[arg][0]!='-')split=std::stoi(argv[arg++]);
        while(arg<argc) {
            const std::string option=argv[arg++];
            if(option=="--tails-only")tails_only=true;
            else if(option=="--enumerate-above")enumerate_above=true;
            else if(option=="--symmetry" && arg<argc)symmetry_path=argv[arg++];
            else if(option=="--counterexample-out" && arg<argc)counterexample_path=argv[arg++];
            else if(option=="--max-counterexamples" && arg<argc)max_counterexamples=unsigned(std::stoul(argv[arg++]));
            else throw std::runtime_error("Unknown or incomplete option");
        }
        if (threads < 1 || threads > 256 || split < 1 || split > 24 || max_counterexamples<1 || max_counterexamples>1000000)
            throw std::runtime_error("Bad threads, split, or counterexample limit");
        std::vector<U> row_norm(n), verified(n+1,0);
        U total_abs=0;
        for (int i=0;i<n;++i) {
            for (int32_t x : ordered[i]) row_norm[i] += U(std::abs(x));
            total_abs += row_norm[i];
        }
        if (total_abs >= INT32_MAX || cutoff > INT32_MAX) throw std::runtime_error("32-bit safety condition violated");
        SymmetryRestriction symmetry;
        if(!symmetry_path.empty())symmetry=verify_symmetry(symmetry_path,ordered);
        std::cout << "Verified exact row permutation; n=" << n << " m=" << m
                  << " total_absolute_sum=" << total_abs << " cutoff=" << cutoff << std::endl;
        const auto beginning = std::chrono::steady_clock::now();
        U all_nodes=0;
        for (int k=n-1; k>=1; --k) {
            const U triangle = row_norm[k] + verified[k+1];
            if (supplied[k] >= triangle) {
                verified[k] = triangle;
                continue;
            }
            ProofSearch search{n,m,threads,split,ordered,verified,supplied[k]};
            U nodes=0,tasks=0;
            if (!search.prove(k,nodes,tasks)) {
                std::cerr << "REJECTED tail k=" << k << " proposed=" << supplied[k]
                          << " violating_value=" << search.violating_value.load() << std::endl;
                return 1;
            }
            all_nodes += nodes;
            verified[k] = supplied[k];
            std::cout << "Tail k=" << k << " length=" << n-k << " upper=" << verified[k]
                      << " nodes=" << nodes << std::endl;
        }
        std::cout << "All required tail bounds independently verified." << std::endl;
        if(tails_only){std::cout<<"VERIFIED_TAILS_ONLY total_nodes="<<all_nodes<<std::endl;return 0;}
        std::cout << "Full search begins." << std::endl;
        ProofSearch search{n,m,threads,split,ordered,verified,cutoff};
        if(!symmetry_path.empty())search.restriction=&symmetry;
        search.max_counterexamples=max_counterexamples;
        search.enumerate_all=enumerate_above;
        U nodes=0,tasks=0;
        if (!search.prove(0,nodes,tasks)) {
            std::vector<int> original_to_ordered(n,-1);
            std::vector<bool> used(n,false);
            for(int i=0;i<n;++i)for(int j=0;j<n;++j)if(!used[j] && original[i]==ordered[j]){
                original_to_ordered[i]=j;used[j]=true;break;
            }
            std::ofstream file;
            if(!counterexample_path.empty()) {
                file.open(counterexample_path);
                if(!file)throw std::runtime_error("Cannot write counterexample output");
                file<<"{\"rows\":"<<n<<",\"columns\":"<<m<<",\"cutoff\":"<<cutoff
                    <<",\"row_order\":\"original input matrix\",\"exhaustive_in_retained_symmetry_prefixes\":"
                    <<(enumerate_above?"true":"false")<<",\"counterexamples\":[\n";
            }
            for(size_t index=0;index<search.counterexamples.size();++index) {
                const auto& example=search.counterexamples[index];
                std::vector<int> signs(n);
                for(int i=0;i<n;++i) {
                    if(original_to_ordered[i]<0)throw std::runtime_error("Missing original row mapping");
                    signs[i]=example.signs[original_to_ordered[i]];
                    if(signs[i]!=-1 && signs[i]!=1)throw std::runtime_error("Invalid exported sign");
                }
                U exact_value=0;
                for(int j=0;j<m;++j) {
                    int64_t sum=0;
                    for(int i=0;i<n;++i)sum+=int64_t(signs[i])*original[i][j];
                    exact_value+=U(std::abs(sum));
                }
                if(exact_value!=example.value || exact_value<=cutoff)throw std::runtime_error("Counterexample failed exact recomputation");
                std::cout<<"COUNTEREXAMPLE_ORIGINAL index="<<index<<" value="<<exact_value<<" signs=";
                for(int s:signs)std::cout<<s<<' ';
                std::cout<<std::endl;
                if(file) {
                    if(index)file<<",\n";
                    file<<"{\"value\":"<<exact_value<<",\"alice_signs\":[";
                    for(int i=0;i<n;++i){if(i)file<<',';file<<signs[i];}
                    file<<"]}";
                }
            }
            if(file)file<<"\n]}\n";
            if(enumerate_above) {
                const double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-beginning).count();
                std::cout<<"ENUMERATION_COMPLETE cutoff="<<cutoff<<" count="<<search.counterexamples.size()
                    <<" full_nodes="<<nodes<<" total_nodes="<<all_nodes+nodes<<" seconds="<<seconds<<std::endl;
                return 0;
            }
            std::cerr << "REJECTED full cutoff=" << cutoff << " violating_value="
                      << search.violating_value.load() << std::endl;
            return 1;
        }
        all_nodes += nodes;
        const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now()-beginning).count();
        std::cout << "VERIFIED classical_upper=" << cutoff << " full_nodes=" << nodes
                  << " total_nodes=" << all_nodes << " prefix_tasks=" << tasks
                  << " seconds=" << seconds << std::endl;
        if(enumerate_above) {
            std::cout<<"ENUMERATION_COMPLETE cutoff="<<cutoff<<" count=0"<<std::endl;
            if(!counterexample_path.empty()) {
                std::ofstream file(counterexample_path);
                if(!file)throw std::runtime_error("Cannot write counterexample output");
                file<<"{\"rows\":"<<n<<",\"columns\":"<<m<<",\"cutoff\":"<<cutoff
                    <<",\"row_order\":\"original input matrix\",\"exhaustive_in_retained_symmetry_prefixes\":true,\"counterexamples\":[]}\n";
            }
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ERROR " << error.what() << std::endl;
        return 2;
    }
}
