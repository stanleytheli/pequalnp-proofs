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
struct Search {
    int nPairs=0,rootleft=-1,budget=0;Mask target=0;
    std::vector<unsigned char> restrict_equal;unsigned long long pruned=0;
    int n,variables; std::array<Mask,8> variable{}; std::vector<bool> small=std::vector<bool>(32768); std::unordered_set<Mask> targets;
    std::array<Mask,30> values{}; std::array<int,30> id{};
    std::array<Mask,30> pool{}; std::array<int,30> poolid{};
    std::array<std::array<int,3>,16> recorded{};
    std::vector<Node> ops;
    std::array<int,30> later_leaves{};
    unsigned long long completed=0, generated=0; bool found=false;
    explicit Search(int gates,int m,int lower):n(gates),variables(m),budget(gates-lower) {
        int k=0;
        for(int i=0;i<m;i++)for(int j=i+1;j<m;j++,k++){variable[i]|=Mask(1)<<k;variable[j]|=Mask(1)<<k;}
        nPairs=k;target=(Mask(1)<<k)-1;
        for(int i=0;i<m;i++)variable[i]|=Mask(1)<<(k+i);
        const int total=k+m;restrict_equal.resize(1u<<total);
        restrict_equal[0]=static_cast<unsigned char>((1u<<m)-1);
        for(unsigned i=1;i<restrict_equal.size();i++){
            int first=__builtin_ctz(i);unsigned includes=0;
            for(int j=0;j<m;j++)if((variable[j]>>first)&1)includes|=1u<<j;
            restrict_equal[i]=restrict_equal[i&(i-1)]&includes;
        }
    }
    std::array<int,32> fresh_nodes{},age{};std::array<bool,32> second_leaf{};
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
    void walk(int pc,int inputs,int ng,int count,unsigned long long savings){
        if(found)return;
        if(pc==int(ops.size())){
            completed++;
            if(inputs==variables && values[pc-1]==target){
                std::cout<<"MATCH "<<n;
                for(int j=0;j<ng;j++)std::cout<<" "<<recorded[j][0]<<","<<recorded[j][1]<<","<<recorded[j][2];
                std::cout<<"\n"<<std::flush;found=true;
            }
            return;
        }
        if(pc==rootleft+1 && (values[rootleft]&~target) && (values[rootleft]&target)!=target)return;
        if(inputs+later_leaves[pc]<variables)return;
        auto [a,b,dummy]=ops[pc];
        if(a<0){
            if(inputs<variables){
                age[pc]=count;values[pc]=pool[count]=variable[inputs];id[pc]=poolid[count]=inputs;
                walk(pc+1,inputs+1,ng,count+1,savings);
            }
            if(inputs+later_leaves[pc]>variables)
                for(int i=(second_leaf[pc]?age[pc-1]+1:0);i<count;i++){
                    age[pc]=i;values[pc]=pool[i];id[pc]=poolid[i];
                    walk(pc+1,inputs,ng,count,savings);
                }
        }else{
            if(fresh_nodes[a]==fresh_nodes[b] && fresh_nodes[a]>0 &&
                    __builtin_popcountll(values[a])>__builtin_popcountll(values[b]))return;
            for(int op=0;op<=1;op++){
                Mask v=op ? Mask(values[a]&values[b]):Mask(values[a]|values[b]);
                if(std::find(pool.begin(),pool.begin()+count,v)!=pool.begin()+count)continue;
                unsigned kills=restrict_equal[v];
                for(int i=0;i<variables;i++)kills|=restrict_equal[v^variable[i]];
                for(int i=0;i<count;i++)if(poolid[i]>=variables)kills|=restrict_equal[v^pool[i]];
                unsigned long long updated=savings;bool fail=false;
                for(unsigned hit=kills;hit;hit&=hit-1){
                    unsigned i=__builtin_ctz(hit),shift=4*i;
                    if(int((savings>>shift)&15)>=budget){fail=true;break;}
                    updated+=1ull<<shift;
                }
                if(fail){pruned++;continue;}
                values[pc]=pool[count]=v;id[pc]=poolid[count]=variables+ng;
                recorded[ng]={op,id[a],id[b]};generated++;
                walk(pc+1,inputs,ng+1,count+1,updated);
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
            if((idx-lo)%20==0)std::cout<<"shape "<<idx<<" of "<<shapes[n].size()<<" visited "<<completed<<" pruned "<<pruned<<"\n"<<std::flush;
            auto& s=shapes[n][idx];
            ops.clear();int p=0;parse(s,p);rootleft=ops.back().left;
            later_leaves.fill(0);
            for(int i=int(ops.size())-1;i>=0;i--)later_leaves[i]=later_leaves[i+1]+(ops[i].left<0);
            walk(0,0,0,0,0);
            if(found)break;
        }
        std::cout<<"gates "<<n<<" shapes "<<shapes[n].size()<<" circuits "<<completed<<" evaluated gates "<<generated
                 <<" found "<<found<<"\n"<<std::flush;
    }
};
int main(int argc,char** argv){
    if(argc!=7)return 2;
    int m=std::atoi(argv[1]),a=std::atoi(argv[2]),b=std::atoi(argv[3]),lower=std::atoi(argv[4]);
    int lo=std::atoi(argv[5]),hi=std::atoi(argv[6]);
    if(m<2||m>6||a<m-1||b>13||a>b||lo<0||lo>=hi||lower<0||lower>a)return 2;
    for(int n=a;n<=b;n++){Search s(n,m,lower);s.run(lo,hi);if(s.found)break;}
}
