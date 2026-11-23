// Independent exact enumeration of minimal binary monotone circuits.
// A depth-first traversal introduces each gate once; later references are leaves.
// Each new gate visits the child with the larger remaining gate cone first.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <string>
#include <vector>
using Mask=std::uint64_t;
struct Node {int left=-1,right=-1,bit=-1;};
struct Entry {Mask truth=0;int rep=-1;std::array<int,6> rename{};};
struct Catalogue {
    std::array<Entry,1<<16> entries{};
    std::array<int,1<<15> best{};
    int classes=0,found=0;
    static unsigned index(Mask x){x^=x>>33;x*=0xff51afd7ed558ccdULL;x^=x>>33;return unsigned(x)&65535u;}
    Catalogue(){
        const int limit=1<<15;
        std::array<bool,limit> seen{};
        for(int rep=1;rep<limit;rep++){
            if(seen[rep])continue;
            int k=0,active=0;bool e[6][6]{};
            for(int i=0;i<6;i++)for(int j=i+1;j<6;j++,k++)if(rep>>k&1){e[i][j]=e[j][i]=true;active|=(1<<i)|(1<<j);}
            if(active!=63)continue;
            classes++;
            std::array<int,6> p{0,1,2,3,4,5};
            do{
                int label=0;k=0;Mask h=0;
                for(int i=0;i<6;i++)for(int j=i+1;j<6;j++,k++)if(e[p[i]][p[j]]){
                    label|=1<<k;
                    for(int x=0;x<64;x++)if((x>>i)&(x>>j)&1)h|=Mask(1)<<x;
                }
                if(seen[label])continue;
                seen[label]=true;unsigned slot=index(h);
                while(entries[slot].rep>=0)slot=(slot+1)&65535u;
                entries[slot]={h,rep,p};
            }while(std::next_permutation(p.begin(),p.end()));
        }
    }
    const Entry* lookup(Mask h) const {
        constexpr Mask small=(Mask(1)<<0)|(Mask(1)<<1)|(Mask(1)<<2)|(Mask(1)<<4)|(Mask(1)<<8)|(Mask(1)<<16)|(Mask(1)<<32);
        if(h&small)return nullptr;
        for(unsigned i=index(h);entries[i].rep>=0;i=(i+1)&65535u)if(entries[i].truth==h)return &entries[i];
        return nullptr;
    }
};

struct Search {
    Catalogue& cat;
    int n; std::array<Mask,6> variable{}; std::array<bool,32768> is_target{};
    std::array<Mask,24> values{}; std::array<int,24> id{};
    std::array<Mask,24> pool{}; std::array<int,24> poolid{};
    std::array<std::array<int,3>,16> recorded{};
    std::vector<Node> ops;
    std::array<int,24> later_leaves{};
    unsigned long long completed=0, generated=0; bool found=false;
    explicit Search(int gates,Catalogue& catalog):cat(catalog),n(gates) {
        for(int x=0;x<64;x++)for(int i=0;i<6;i++)if(x>>i&1)variable[i]|=Mask(1)<<x;
    }
    std::array<int,24> fresh_nodes{},age{};std::array<bool,24> second_leaf{};
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
    void walk(int pc,int inputs,int ng,int count){
        if(found)return;
        if(pc==int(ops.size())){
            completed++;
            if(inputs==6)if(const Entry* e=cat.lookup(values[pc-1]); e && !cat.best[e->rep]){
                cat.best[e->rep]=ng;cat.found++;
                std::cout<<"graph "<<e->rep<<" minimum "<<ng;
                for(int i=0;i<ng;i++){
                    auto g=recorded[i];if(g[1]<6)g[1]=e->rename[g[1]];if(g[2]<6)g[2]=e->rename[g[2]];
                    std::cout<<" "<<g[0]<<","<<g[1]<<","<<g[2];
                }
                std::cout<<"\n"<<std::flush;
            }
            return;
        }
        if(inputs+later_leaves[pc]<6)return;
        auto [a,b,dummy]=ops[pc];
        if(a<0){
            if(inputs<6){
                age[pc]=count;values[pc]=pool[count]=variable[inputs];id[pc]=poolid[count]=inputs;
                walk(pc+1,inputs+1,ng,count+1);
            }
            if(inputs+later_leaves[pc]>6)
                for(int i=(second_leaf[pc]?age[pc-1]+1:0);i<count;i++){
                    age[pc]=i;values[pc]=pool[i];id[pc]=poolid[i];
                    walk(pc+1,inputs,ng,count);
                }
        }else{
            if(fresh_nodes[a]==fresh_nodes[b] && fresh_nodes[a]>0 &&
                    __builtin_popcountll(values[a])>__builtin_popcountll(values[b]))return;
            for(int op=0;op<=1;op++){
                Mask v=op ? Mask(values[a]&values[b]):Mask(values[a]|values[b]);
                if(std::find(pool.begin(),pool.begin()+count,v)!=pool.begin()+count)continue;
                values[pc]=pool[count]=v;id[pc]=poolid[count]=6+ng;
                recorded[ng]={op,id[a],id[b]};generated++;
                walk(pc+1,inputs,ng+1,count+1);
            }
        }
    }
    void run(){
        std::vector<std::vector<std::string>> shapes(n+1);
        shapes[0]={"x"};
        for(int k=1;k<=n;k++)
            for(int a=0;a<k;a++){int b=k-1-a;if(a<b)continue;
                for(auto& l:shapes[a])for(auto& r:shapes[b])shapes[k].push_back("g"+l+r);}
        for(auto& s:shapes[n]){
            ops.clear();int p=0;parse(s,p);
            later_leaves.fill(0);
            for(int i=int(ops.size())-1;i>=0;i--)later_leaves[i]=later_leaves[i+1]+(ops[i].left<0);
            walk(0,0,0,0);
            if(found)break;
        }
        std::cout<<"gates "<<n<<" shapes "<<shapes[n].size()<<" circuits "<<completed<<" evaluated gates "<<generated
                 <<" classes "<<cat.found<<"/"<<cat.classes<<"\n"<<std::flush;
    }
};
int main(int argc,char** argv){
    if(argc!=3)return 2;
    int a=std::atoi(argv[1]),b=std::atoi(argv[2]);if(a<5||b>11||a>b)return 2;
    static Catalogue cat;
    for(int n=a;n<=b;n++){Search s(n,cat);s.run();if(s.found)return 0;}
}
