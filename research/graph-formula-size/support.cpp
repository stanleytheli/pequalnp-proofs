#include <algorithm>
#include <array>
#include <iostream>
#include <vector>
#include <cstdint>
using U=unsigned;
constexpr int side=13, all=(1<<side)-1;
const int input[side][4]={{0,1,3,9},{0,2,8,12},{1,7,11,12},{0,6,10,11},{5,9,10,12},{4,8,9,11},{3,7,8,10},{2,6,7,9},{1,5,6,8},{0,4,5,7},{3,4,6,12},{2,3,5,11},{1,2,4,10}};
int pc(int x){return __builtin_popcount(unsigned(x));}
int lo(int x){return __builtin_ctz(unsigned(x));}
int main(){
    int nb[side]{},unions[all+1]{};
    for(int i=0;i<side;i++)for(auto j:input[i])nb[i]|=1<<j;
    for(int x=1;x<=all;x++)unions[x]=unions[x&(x-1)]|nb[lo(x)];
    std::array<int,27> best{},pt{},ln{};best.fill(-100);
    for(int lines=0;lines<=all;lines++){
        // Hall deficiency on an induced bipartite graph: matching size
        // |P| - max_{T subset P} ( |T| - |N(T) intersect lines| ).
        std::array<int,all+1> deficiency{},m{};
        for(int p=1;p<=all;p++){
            m[p]=m[p&(p-1)]+pc(nb[lo(p)]&lines);
            deficiency[p]=pc(p)-pc(unions[p]&lines);
            for(int q=p;q;q&=q-1)deficiency[p]=std::max(deficiency[p],deficiency[p^(q&-q)]);
            int tau=pc(p)-deficiency[p],r=pc(p)+pc(lines),score=m[p]-tau-r+1;
            if(score>best[r]){best[r]=score;pt[r]=p;ln[r]=lines;}
        }
    }
    for(int r=1;r<=26;r++)std::cout<<r<<" "<<best[r]<<" "<<pt[r]<<" "<<ln[r]<<std::endl;
}
