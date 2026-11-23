// Exact number of raw disjunctions needed in a safe conjunction covering a prescribed edge set.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <stdexcept>
#include <vector>
using Mask = std::uint64_t;
int bits(Mask x) { return __builtin_popcountll(x); }
int first(Mask x) { return __builtin_ctzll(x); }
constexpr int V=14, E=21;
using Edge=std::array<int,2>;
const int lines[7][3]={{0,1,3},{0,2,6},{1,5,6},{0,4,5},{3,4,6},{2,3,5},{1,2,4}};
std::vector<Edge> edges;
std::vector<int> negatives;
struct Clause {int inputs, hits; Mask rejects;};
std::vector<Clause> clauses;
using Perm=std::array<std::array<int,128>,3>;
std::vector<Perm> permutations;
void prepare() {
    int lookup[V][V]{}, adj[V]{};
    for(int j=0;j<7;j++) for(int a:lines[j]){
        int b=j+7;lookup[a][b]=lookup[b][a]=int(edges.size())+1;
        edges.push_back({a,b});adj[a]|=1<<b;adj[b]|=1<<a;
    }
    for(int s=0;s<1<<V;s++){
        bool independent=true;int touches=s;
        for(int p=s;p;p&=p-1){int a=first(p);independent&=!(s&adj[a]);touches|=adj[a];}
        if(independent && touches==(1<<V)-1)negatives.push_back(s);
    }
    if(negatives.size()!=37) throw std::logic_error("negative rows");
    for(int s=1;s<1<<V;s++){
        int hits=0;Mask rejects=0;
        for(int e=0;e<E;e++)if(s&(1<<edges[e][0]|1<<edges[e][1]))hits|=1<<e;
        for(unsigned j=0;j<negatives.size();j++)if(!(s&negatives[j]))rejects|=Mask(1)<<j;
        if(rejects)clauses.push_back({s,hits,rejects});
    }
    std::array<int,7> p={0,1,2,3,4,5,6};
    do for(int side=0;side<2;side++){
        int v[V];bool ok=true;
        for(int i=0;i<7;i++)v[i]=p[i]+7*side;
        for(int j=0;j<7;j++){
            int n=0;for(int a:lines[j])n|=1<<v[a];v[7+j]=-1;
            for(int b=7*(1-side);b<7*(2-side);b++)if(adj[b]==n)v[7+j]=b;
            ok&=v[7+j]>=0;
        }
        if(!ok)continue;
        Perm tab{};
        for(int e=0;e<E;e++){
            int id=lookup[v[edges[e][0]]][v[edges[e][1]]]-1;
            if(id<0)throw std::logic_error("permutation");
            for(int s=0;s<128;s++)if(s&(1<<(e%7)))tab[e/7][s]|=1<<id;
        }
        permutations.push_back(tab);
    }while(std::next_permutation(p.begin(),p.end()));
    if(permutations.size()!=336)throw std::logic_error("automorphism count");
}

struct Cover {
    std::vector<Mask> candidates;
    std::array<std::vector<Mask>,64> containing;
    std::map<Mask,int> memo;
    explicit Cover(int required){
        std::set<Mask> all;
        for(auto c:clauses)if((required&~c.hits)==0)all.insert(c.rejects);
        std::vector<Mask> sorted(all.begin(),all.end());
        std::sort(sorted.begin(),sorted.end(),[](Mask a,Mask b){return bits(a)>bits(b);});
        for(Mask a:sorted){
            if(std::any_of(candidates.begin(),candidates.end(),[a](Mask b){return !(a&~b);}))continue;
            candidates.push_back(a);
            for(Mask x=a;x;x&=x-1)containing[first(x)].push_back(a);
        }
    }
    int minimum(Mask left){
        if(!left)return 0;
        auto it=memo.find(left);if(it!=memo.end())return it->second;
        int pivot=first(left);
        for(Mask r=left;r;r&=r-1)if(containing[first(r)].size()<containing[pivot].size())pivot=first(r);
        int best=100;
        for(Mask z:containing[pivot])best=std::min(best,1+minimum(left&~z));
        return memo[left]=best;
    }
};
int main(){
    prepare();
    std::vector<bool> seen(1<<E);
    int classes=0; long long tested=0;
    std::map<std::pair<int,int>,int> counts;
    for(int d=1;d<1<<E;d++){
        if(seen[d])continue;
        int orbit=0;
        for(const auto& p:permutations){
            int x=p[0][d&127]|p[1][(d>>7)&127]|p[2][d>>14];
            if(!seen[x]){seen[x]=true;orbit++;}
        }
        Cover c(d);
        int minimal=c.minimum((Mask(1)<<negatives.size())-1);
        if(minimal<1||minimal>37)throw std::logic_error("impossible cover");
        counts[{minimal,bits(d)}]+=orbit;classes++;tested+=orbit;
    }
    if(tested!=(1<<E)-1)throw std::logic_error("incomplete orbit coverage");
    std::cout<<"orbits "<<classes<<" subsets "<<tested<<" negative_rows "<<negatives.size()<<"\n";
    for(const auto& c:counts)std::cout<<c.first.first<<" "<<c.first.second<<" "<<c.second<<"\n";
}
