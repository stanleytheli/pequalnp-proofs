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
struct Catalogue {
    std::vector<unsigned char> ids;std::vector<int> mincost{0},representative{0};int vertices,bits;
    Catalogue(int v,const std::string& path):vertices(v),bits(v*(v-1)/2){
        ids.assign(std::size_t(1)<<bits,0);
        std::ifstream in(path);if(!in)throw std::runtime_error("graph table missing");
        unsigned g;int goal;
        while(in>>g>>goal){
            const int cls=int(mincost.size());if(cls>=256)throw std::runtime_error("too many graph classes");
            representative.push_back(g);mincost.push_back(goal);std::vector<int> p(v);std::iota(p.begin(),p.end(),0);
            int pairid[8][8]{};int k=0;for(int i=0;i<v;i++)for(int j=i+1;j<v;j++)pairid[i][j]=pairid[j][i]=k++;
            do {unsigned label=0;k=0;
                for(int i=0;i<v;i++)for(int j=i+1;j<v;j++,k++)
                    if(g>>pairid[p[i]][p[j]]&1u)label|=1u<<k;
                if(ids[label] && ids[label]!=cls)throw std::runtime_error("duplicate graph class");
                ids[label]=static_cast<unsigned char>(cls);
            }while(std::next_permutation(p.begin(),p.end()));
        }
    }
};

struct Search {
    Catalogue& cat;std::vector<unsigned long long> hits;
    int n,variables; std::array<Mask,8> variable{}; std::vector<bool> small=std::vector<bool>(32768); std::unordered_set<Mask> targets;
    std::array<Mask,30> values{}; std::array<int,30> id{};
    std::array<Mask,30> pool{}; std::array<int,30> poolid{};
    std::array<std::array<int,3>,16> recorded{};
    std::vector<Node> ops;
    std::array<int,30> later_leaves{};
    unsigned long long completed=0, generated=0; bool found=false;
    explicit Search(int gates,Catalogue& c):cat(c),hits(c.mincost.size()),n(gates),variables(c.vertices){
        int k=0;
        for(int i=0;i<variables;i++)for(int j=i+1;j<variables;j++,k++){variable[i]|=Mask(1)<<k;variable[j]|=Mask(1)<<k;}
        for(int i=0;i<variables;i++)variable[i]|=Mask(1)<<(k+i);
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
            if(inputs==variables && (values[pc-1]>>cat.bits)==0){
                const int cl=cat.ids[values[pc-1]];
                if(cl && n<cat.mincost[cl]){
                    if(hits[cl]++==0){
                        std::cout<<"short pair model "<<cat.representative[cl]<<" at "<<n<<" labeled "<<values[pc-1];
                        for(int j=0;j<ng;j++)std::cout<<" "<<recorded[j][0]<<","<<recorded[j][1]<<","<<recorded[j][2];
                        std::cout<<"\n"<<std::flush;
                    }
                }
            }
            return;
        }
        if(inputs+later_leaves[pc]<variables)return;
        auto [a,b,dummy]=ops[pc];
        if(a<0){
            if(inputs<variables){
                age[pc]=count;values[pc]=pool[count]=variable[inputs];id[pc]=poolid[count]=inputs;
                walk(pc+1,inputs+1,ng,count+1);
            }
            if(inputs+later_leaves[pc]>variables)
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
                values[pc]=pool[count]=v;id[pc]=poolid[count]=variables+ng;
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
                 <<" targets-below "<<std::count_if(hits.begin(),hits.end(),[](auto x){return x>0;})<<"\n"<<std::flush;
    }
};
int main(int argc,char** argv){
    if(argc!=5)return 2;
    int v=std::atoi(argv[1]),a=std::atoi(argv[2]),b=std::atoi(argv[3]);if(v<2||v>8||a<v-1||b>12||b<a)return 2;
    Catalogue cat(v,argv[4]);
    for(int n=a;n<=b;n++){Search s(n,cat);s.run();}
}
