// Independent exact enumeration of minimal binary monotone circuits.
// A depth-first traversal introduces each gate once; later references are leaves.
// Each new gate visits the child with the larger remaining gate cone first.
#include <algorithm>
#include <fstream>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <bitset>
#include <unordered_set>
#include <string>
#include <vector>
using Mask=std::uint32_t;
struct Node {int left=-1,right=-1,bit=-1;};
struct Search {
    int n,variables; std::array<Mask,8> variable{}; std::vector<bool> small=std::vector<bool>(32768); std::unordered_set<Mask> targets;
    std::array<Mask,24> values{}; std::array<int,24> id{};
    std::array<Mask,24> pool{}; std::array<int,24> poolid{};
    std::array<std::array<int,3>,16> recorded{};
    std::vector<Node> ops;
    std::array<int,24> later_leaves{};
    unsigned long long completed=0, generated=0; bool found=false;
    std::vector<unsigned char> fast=std::vector<unsigned char>(1u<<25);
    std::unordered_map<Mask,std::array<int,8>> names;
    unsigned long long pair_count=0,full_count=0,nested_count=0;
    const std::array<std::pair<int,int>,8> edges{{{0,1},{1,2},{2,3},{3,4},{4,5},{0,5},{0,6},{1,7}}};
    explicit Search(int gates):n(gates),variables(8) {
        bool edge[8][8]{};
        for(auto [a,b]:edges)edge[a][b]=edge[b][a]=true;
        std::array<int,8> p{0,1,2,3,4,5,6,7};
        do{Mask m=0;int k=0;
            for(int i=0;i<8;i++)for(int j=i+1;j<8;j++,k++){
                variable[i]|=1u<<k;variable[j]|=1u<<k;
                if(edge[p[i]][p[j]])m|=1u<<k;
            }
            fast[m>>3]|=1u<<(m&7);names.emplace(m,p);
        }while(std::next_permutation(p.begin(),p.end()));
    }
    bool check_candidate(int ng, Mask mask) {
        if((fast[mask>>3]&(1u<<(mask&7)))==0)return false;
        ++pair_count;
        const auto& remap=names.at(mask);
        using Truth=std::bitset<256>;
        std::array<Truth,20> wires;Truth expected;
        std::array<std::array<int,3>,16> gates=recorded;
        for(int x=0;x<256;x++){
            for(int i=0;i<8;i++)wires[i][x]=(x>>i)&1;
            for(auto [a,b]:edges)if(((x>>a)&(x>>b)&1)!=0)expected.set(x);
        }
        for(int j=0;j<ng;j++){
            auto& g=gates[j];
            if(g[1]<8)g[1]=remap[g[1]];
            if(g[2]<8)g[2]=remap[g[2]];
            wires[8+j]=g[0]?(wires[g[1]]&wires[g[2]]):(wires[g[1]]|wires[g[2]]);
        }
        if(ng==11){
            static std::ofstream log("pair-candidates.txt");
            for(int ii=0;ii<ng;ii++)log<<gates[ii][0]<<" "<<gates[ii][1]<<" "<<gates[ii][2]<<" ";
            log<<"\n";
        }
        if(wires[7+ng]!=expected)return false;
        ++full_count;
        if(ng<11){
            std::cout<<"SMALLER correct circuit "<<ng<<"\n";
            for(int i=0;i<ng;i++)std::cout<<gates[i][0]<<" "<<gates[i][1]<<" "<<gates[i][2]<<"\n";
            return true;
        }
        auto nesting=[&](int change,int keep){
            int total=0;std::array<unsigned,20> anc{};
            for(int i=0;i<ng;i++){
                const auto& g=gates[i];
                unsigned prev=i==change?anc[keep]:(anc[g[1]]|anc[g[2]]);
                anc[8+i]=prev;
                if(g[0]){total+=__builtin_popcount(prev);anc[8+i]|=1u<<i;}
            }return total;
        };
        const int chain=nesting(-1,0);
        if(chain==0)return false;
        ++nested_count;
        for(int j=0;j<ng-1;j++)if(!gates[j][0]){
            for(int t=1;t<=2;t++){
                const int keep=gates[j][t],lift=gates[j][3-t];
                if((wires[lift]&~expected).none() && nesting(j,keep)<chain) return false;
            }
        }
        std::cout<<"WITNESS with "<<chain<<" nested AND pairs\n";
        for(int j=0;j<ng;j++)std::cout<<gates[j][0]<<" "<<gates[j][1]<<" "<<gates[j][2]<<"\n";
        return true;
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
            if(inputs==variables && __builtin_popcount(values[pc-1])==8 && check_candidate(ng,values[pc-1]))found=true;
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
    void run(int lo,int hi){
        std::vector<std::vector<std::string>> shapes(n+1);
        shapes[0]={"x"};
        for(int k=1;k<=n;k++)
            for(int a=0;a<k;a++){int b=k-1-a;if(a<b)continue;
                for(auto& l:shapes[a])for(auto& r:shapes[b])shapes[k].push_back("g"+l+r);}
        for(int index=lo;index<int(shapes[n].size()) && index<hi;index++){
            if((index-lo)%20==0)std::cout<<"progress "<<n<<" "<<index<<" of "<<shapes[n].size()<<" matches "<<pair_count<<" full "<<full_count<<" nested "<<nested_count<<"\n"<<std::flush;
            const auto& s=shapes[n][index];
            ops.clear();int p=0;parse(s,p);
            later_leaves.fill(0);
            for(int i=int(ops.size())-1;i>=0;i--)later_leaves[i]=later_leaves[i+1]+(ops[i].left<0);
            walk(0,0,0,0);
            if(found)break;
        }
        std::cout<<"gates "<<n<<" shapes "<<shapes[n].size()<<" circuits "<<completed<<" evaluated gates "<<generated
                 <<" pair "<<pair_count<<" full "<<full_count<<" nested "<<nested_count<<" found "<<found<<"\n"<<std::flush;
    }
};
int main(int argc,char** argv){
    if(argc!=5)return 2;
    int a=std::atoi(argv[1]),b=std::atoi(argv[2]);if(a<5||b>11||a>b)return 2;
    for(int n=a;n<=b;n++){Search s(n);s.run(std::atoi(argv[3]),std::atoi(argv[4]));if(s.found)return 0;}
}
