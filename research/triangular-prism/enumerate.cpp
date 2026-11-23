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
using Mask=std::uint16_t;
struct Node {int left=-1,right=-1,bit=-1;};
struct Search {
    int n; std::array<Mask,6> variable{}; std::array<bool,32768> is_target{};
    std::array<Mask,24> values{}; std::array<int,24> id{};
    std::array<Mask,24> pool{}; std::array<int,24> poolid{};
    std::array<std::array<int,3>,16> recorded{};
    std::vector<Node> ops;
    std::array<int,24> later_leaves{};
    unsigned long long completed=0, generated=0; bool found=false;
    explicit Search(int gates):n(gates) {
        auto edge=[](int a,int b){return a/3==b/3 || std::abs(a-b)==3;};
        std::array<int,6> p{0,1,2,3,4,5};
        do {
            Mask t=0; int k=0;
            for(int i=0;i<6;i++)for(int j=i+1;j<6;j++,k++){
                if(edge(p[i],p[j]))t|=Mask(1u<<k);
                variable[i]|=Mask(1u<<k); variable[j]|=Mask(1u<<k);
            }
            is_target[t]=true;
        } while(std::next_permutation(p.begin(),p.end()));
    }
    int parse(const std::string& s,int& pos){
        if(s[pos++]=='x'){ops.push_back({}); return int(ops.size())-1;}
        int a=parse(s,pos),b=parse(s,pos);
        ops.push_back({a,b,-1});return int(ops.size())-1;
    }
    void walk(int pc,int inputs,int ng,int count){
        if(found)return;
        if(pc==int(ops.size())){
            completed++;
            if(inputs==6 && is_target[values[pc-1]]){
                found=true;std::cout<<"MATCH up to input renaming\n";
                for(int i=0;i<ng;i++)std::cout<<recorded[i][0]<<" "<<recorded[i][1]<<" "<<recorded[i][2]<<"\n";
            }
            return;
        }
        if(inputs+later_leaves[pc]<6)return;
        auto [a,b,dummy]=ops[pc];
        if(a<0){
            if(inputs<6){
                values[pc]=pool[count]=variable[inputs];id[pc]=poolid[count]=inputs;
                walk(pc+1,inputs+1,ng,count+1);
            }
            if(inputs+later_leaves[pc]>6)
                for(int i=0;i<count;i++){
                    values[pc]=pool[i];id[pc]=poolid[i];
                    walk(pc+1,inputs,ng,count);
                }
        }else{
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
                 <<" found "<<found<<"\n"<<std::flush;
    }
};
int main(int argc,char** argv){
    if(argc!=3)return 2;
    int a=std::atoi(argv[1]),b=std::atoi(argv[2]);if(a<5||b>11||a>b)return 2;
    for(int n=a;n<=b;n++){Search s(n);s.run();if(s.found)return 0;}
}
