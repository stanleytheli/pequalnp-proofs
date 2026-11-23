// Independent exact enumeration of minimal binary monotone circuits.
// A depth-first traversal introduces each gate once; later references are leaves.
// Each new gate visits the child with the larger remaining gate cone first.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <fstream>
#include <stdexcept>
#include <unordered_set>
#include <string>
#include <vector>
using Mask=std::uint64_t;
struct Node {int left=-1,right=-1,bit=-1;};
struct Target {
    static constexpr unsigned width=28,mask=(1u<<width)-1;
    using Table=std::vector<std::uint64_t>;
    Table exact,below,above;
    unsigned goal;
    static bool bit(const Table& t,unsigned i){ return (t[i>>6]>>(i&63))&1; }
    explicit Target(unsigned g) : exact(1u<<(width-6)),goal(g) {
        std::array<int,8> p{0,1,2,3,4,5,6,7};
        int pos[8][8]={},k=0;
        for(int i=0;i<8;i++)for(int j=i+1;j<8;j++)pos[i][j]=pos[j][i]=k++;
        do {
            unsigned v=0;k=0;
            for(int i=0;i<8;i++)for(int j=i+1;j<8;j++,k++)
                if((g>>pos[p[i]][p[j]])&1u)v|=1u<<k;
            exact[v>>6]|=std::uint64_t(1)<<(v&63);
        }while(std::next_permutation(p.begin(),p.end()));
        below=above=exact;
        for(unsigned k=0;k<6;k++){
            unsigned d=1u<<k;std::uint64_t lo=0;
            for(int i=0;i<64;i++)if(!(i&d))lo|=std::uint64_t(1)<<i;
            for(unsigned i=0;i<below.size();i++){
                below[i]|=(below[i]>>d)&lo;
                above[i]|=(above[i]&lo)<<d;
            }
        }
        for(unsigned k=6;k<width;k++){
            unsigned jump=1u<<(k-6);
            for(unsigned start=0;start<below.size();start+=2*jump)
                for(unsigned i=start;i<start+jump;i++){
                    below[i]|=below[i+jump];above[i+jump]|=above[i];
                }
        }
    }
    bool possible(Mask val) const {
        const unsigned v=val&mask;
        return (!(val>>width) && bit(below,v)) || bit(above,v);
    }
    bool matches(Mask val) const { return !(val>>width) && bit(exact,unsigned(val)); }
};

struct Search {
    const Target& target;int rootleft=-1;
    std::array<std::array<unsigned char,512>,4> erased{};
    unsigned weak=4, maxBudget=3;
    unsigned killed(Mask difference) const {
        return erased[0][difference&511] & erased[1][(difference>>9)&511]
             & erased[2][(difference>>18)&511] & erased[3][(difference>>27)&511];
    }
    int n,variables; std::array<Mask,8> variable{}; std::vector<bool> small=std::vector<bool>(32768); std::unordered_set<Mask> targets;
    std::array<Mask,30> values{}; std::array<int,30> id{};
    std::array<Mask,30> pool{}; std::array<int,30> poolid{};
    std::array<std::array<int,3>,16> recorded{};
    std::vector<Node> ops;
    std::array<int,30> later_leaves{};
    unsigned long long completed=0, generated=0; bool found=false;
    explicit Search(int gates,Target& t):target(t),n(gates),variables(8){
        int k=0;
        for(int i=0;i<variables;i++)for(int j=i+1;j<variables;j++,k++){variable[i]|=Mask(1)<<k;variable[j]|=Mask(1)<<k;}
        for(int i=0;i<variables;i++)variable[i]|=Mask(1)<<(k+i);
        for(int c=0;c<4;c++){
            erased[c][0]=255;
            for(int bits=1;bits<512;bits++){
                Mask index=Mask(1)<<(9*c+__builtin_ctz(unsigned(bits)));unsigned losable=0;
                for(int j=0;j<8;j++)if(variable[j]&index)losable|=1u<<j;
                erased[c][bits]=erased[c][bits&(bits-1)]&losable;
            }
        }
    }
    std::array<int,30> fresh_nodes{},age{};std::array<bool,30> second_leaf{};
    int parse(const std::string& s,int& pos){
        if(s[pos++]=='x'){
            int leaf=int(ops.size());fresh_nodes[leaf]=0;second_leaf[leaf]=false;
            ops.push_back({});return leaf;
        }
        int a=parse(s,pos),b=parse(s,pos);
        int parent=int(ops.size());
        fresh_nodes[parent]=1+fresh_nodes[a]+fresh_nodes[b];
        if(fresh_nodes[a]==0 && fresh_nodes[b]==0)second_leaf[b]=true;
        ops.push_back({a,b,-1});return parent;
    }
    void walk(int pc,int inputs,int ng,int count,unsigned once,unsigned twice,unsigned thrice){
        if(found)return;
        if(pc==int(ops.size())){
            completed++;
            if(inputs==variables && target.matches(values[pc-1])){
                std::cout<<"MATCH "<<n<<" labeled "<<values[pc-1];
                for(int j=0;j<ng;j++)std::cout<<" "<<recorded[j][0]<<","<<recorded[j][1]<<","<<recorded[j][2];
                std::cout<<"\n"<<std::flush;found=true;
            }
            return;
        }
        if(pc==rootleft+1 && !target.possible(values[rootleft]))return;
        if(inputs+later_leaves[pc]<variables)return;
        auto [a,b,dummy]=ops[pc];
        if(a<0){
            if(inputs<variables){
                age[pc]=count;values[pc]=pool[count]=variable[inputs];id[pc]=poolid[count]=inputs;
                walk(pc+1,inputs+1,ng,count+1,once,twice,thrice);
            }
            if(inputs+later_leaves[pc]>variables)
                for(int i=(second_leaf[pc]?age[pc-1]+1:0);i<count;i++){
                    age[pc]=i;values[pc]=pool[i];id[pc]=poolid[i];
                    walk(pc+1,inputs,ng,count,once,twice,thrice);
                }
        }else{
            if(fresh_nodes[a]==fresh_nodes[b] && fresh_nodes[a]>0 &&
                    __builtin_popcountll(values[a])>__builtin_popcountll(values[b]))return;
            for(int op=0;op<=1;op++){
                Mask v=op ? Mask(values[a]&values[b]):Mask(values[a]|values[b]);
                if(std::find(pool.begin(),pool.begin()+count,v)!=pool.begin()+count)continue;
                unsigned lose=killed(v^values[a])|killed(v^values[b])|killed(v);
                if(lose&thrice)continue;
                unsigned two=twice|(lose&once);
                if(__builtin_popcount(two)>4)continue;
                if(ng>=3){
                    for(int j=0;j<variables;j++)lose|=killed(v^variable[j]);
                    for(int j=0;j<count;j++)if(poolid[j]>=variables)lose|=killed(v^pool[j]);
                    if(lose&thrice)continue;
                    two=twice|(lose&once);
                    if(__builtin_popcount(two)>4)continue;
                }
                values[pc]=pool[count]=v;id[pc]=poolid[count]=variables+ng;
                recorded[ng]={op,id[a],id[b]};generated++;
                walk(pc+1,inputs,ng+1,count+1,once|lose,two,thrice|(lose&twice));
            }
        }
    }
    void run(int lo,int hi){
        std::vector<std::vector<std::string>> shapes(n+1);
        shapes[0]={"x"};
        for(int k=1;k<=n;k++)
            for(int a=0;a<k;a++){int b=k-1-a;if(a<b)continue;
                for(auto& l:shapes[a])for(auto& r:shapes[b])shapes[k].push_back("g"+l+r);}
        for(int idx=lo;idx<hi && idx<int(shapes[n].size());idx++){
            if((idx-lo)%20==0)std::cout<<"shape "<<idx<<" of "<<shapes[n].size()<<" visited "<<completed<<"\n"<<std::flush;
            auto& s=shapes[n][idx];
            ops.clear();int p=0;parse(s,p);rootleft=ops.back().left;
            later_leaves.fill(0);
            for(int i=int(ops.size())-1;i>=0;i--)later_leaves[i]=later_leaves[i+1]+(ops[i].left<0);
            walk(0,0,0,0,0,0,0);
            if(found)break;
        }
        std::cout<<"gates "<<n<<" shapes "<<shapes[n].size()<<" circuits "<<completed<<" evaluated gates "<<generated
                 <<" found "<<found<<"\n"<<std::flush;
    }
};
int main(int argc,char** argv){
    if(argc!=5)return 2;
    unsigned target=unsigned(std::stoul(argv[1]));int n=std::atoi(argv[2]),lo=std::atoi(argv[3]),hi=std::atoi(argv[4]);
    if(n!=12||lo<0||lo>=hi||target!=53643800)return 2;
    Target graph(target);Search search(n,graph);search.run(lo,hi);
}
