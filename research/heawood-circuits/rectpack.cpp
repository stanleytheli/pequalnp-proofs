#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <utility>
#include <vector>
using namespace std;

// Exact weight of a union of r disjoint rectangles. Enumerate their masks on
// the smaller axis; the best subset of mutually disjoint masks can then be
// selected independently in each column.
int main(int argc, char **argv){
    if(argc!=4) return 2;
    const int p=stoi(argv[1]),q=stoi(argv[2]),r=stoi(argv[3]);
    if(r<1 || r>6) return 2;
    int lines[7][3]={{0,1,3},{0,2,6},{1,5,6},{0,4,5},{3,4,6},{2,3,5},{1,2,4}};
    vector<pair<int,int>> e;
    int nb[14]={};
    for(int j=0;j<7;j++)for(int a:lines[j]){
        e.emplace_back(a,j+7);nb[a]|=1<<(j+7);nb[j+7]|=1<<a;
    }
    vector<int> P,Q;
    for(int i=0;i<21;i++)if(p>>i&1)P.push_back(i);
    for(int j=0;j<14;j++)if(q>>j&1)Q.push_back(j);
    bool trans=Q.size()<P.size();
    int n=trans?Q.size():P.size(),m=trans?P.size():Q.size();
    if(n>11) return 2;
    vector<vector<int>> w(1<<n,vector<int>(m));
    for(int s=1;s<(1<<n);s++){
        int l=__builtin_ctz(unsigned(s)),t=s&(s-1);
        for(int j=0;j<m;j++){
            auto [a,b]=e[P[trans?j:l]];
            int z=Q[trans?l:j],opp=z>=7?a:b;
            int v=(z==a||z==b)?2:((nb[z]>>opp&1)?-1:1);
            w[s][j]=w[t][j]+v;
        }
    }
    long long nodes=0;
    int maxval=0;
    array<int,6> choice{};
    auto dfs=[&](auto&&self,int cnt,int begin)->void{
        if(++nodes>12000000){cerr<<"state cap\n";exit(3);}
        if(cnt==r){
            array<int,64> masks{};
            array<bool,64> ok{};ok[0]=true;
            for(int z=1;z<(1<<r);z++){
                int l=__builtin_ctz(unsigned(z)),t=z&(z-1);
                ok[z]=ok[t]&&!(masks[t]&choice[l]);
                masks[z]=masks[t]|choice[l];
            }
            int val=0;
            for(int j=0;j<m;j++){
                int mx=0;
                for(int z=1;z<(1<<r);z++)if(ok[z])mx=max(mx,w[masks[z]][j]);
                val+=mx;
            }
            maxval=max(maxval,val);return;
        }
        // A zero row-mask permits fewer rectangles. Duplicate nonempty row masks
        // can always be merged because their column sets are pairwise disjoint.
        if(begin==0){choice[cnt]=0;self(self,cnt+1,0);}
        for(int s=max(1,begin);s<(1<<n);s++){
            choice[cnt]=s;self(self,cnt+1,s+1);
        }
    };
    dfs(dfs,0,0);
    cout<<p<<" "<<q<<" "<<r<<" "<<maxval<<" "<<nodes<<"\n";
}
