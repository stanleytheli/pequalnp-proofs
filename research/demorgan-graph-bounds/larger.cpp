#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <tuple>
#include <string>
#include <memory>
#include <vector>

using Bits=std::uint64_t;
constexpr int N=VERTICES, full=(1<<N)-1, limit=31;
int pop(int a){return __builtin_popcount(unsigned(a));}
int low(int a){return __builtin_ctz(unsigned(a));}
struct Boards{
    std::vector<int> intermediate;
    int neighborhood[full+1]{},nb[N]{},core[full+1]{},edges[full+1]{},alpha[full+1]{},bound[full+1]{},rep[full+1]{};
    std::vector<std::array<int,N>> group;
    explicit Boards(unsigned __int128 graph,int seed){
        int index=0;
        for(int i=0;i<N;i++)for(int j=i+1;j<N;j++,index++)if((graph>>index)&1){
            nb[i]|=1<<j;nb[j]|=1<<i;
        }
        for(int s=1;s<=full;s++){
            int a=low(s),r=s^(1<<a);
            neighborhood[s]=neighborhood[r]|nb[a];edges[s]=edges[r]+pop(nb[a]&r);alpha[s]=std::max(alpha[r],1+alpha[r&~nb[a]]);
            for(int j=0;j<N;j++)if((s>>j&1)&&(nb[j]&s))core[s]|=1<<j;
            rep[s]=s;
            if(pop(s)>seed && s!=full && core[s]==s)intermediate.push_back(s);
        }
        std::array<int,N> perm{};
        automorphisms(perm,0,0);
    }
    void automorphisms(std::array<int,N>& perm,int i,int used){
        if(i==N){
            group.push_back(perm);
            for(int s:intermediate){
                int image=0;
                for(int q=s;q;q&=q-1)image|=1<<perm[low(q)];
                rep[s]=std::min(rep[s],image);
            }
            return;
        }
        for(int j=0;j<N;j++)if(!(used>>j&1)&&pop(nb[j])==pop(nb[i])){
            bool valid=true;for(int k=0;k<i;k++)if(((nb[i]>>k)&1)!=((nb[j]>>perm[k])&1)){valid=false;break;}
            if(valid){perm[i]=j;automorphisms(perm,i+1,used|(1<<j));}
        }
    }
    int upper(int s)const{return edges[s]-alpha[s];} // size plus one minus vertex count
};
constexpr int words=((1<<N)+63)/64;
using Table=std::array<Bits,words>;
struct Gate{int a,b,op;}; // zero is OR, one AND, two unary NOT
struct Restriction{int retained,ones,score;};
struct Search{
    Boards& b;int s,depth;
    std::vector<int> vertices;
    std::vector<Gate> prefix;
    std::vector<Restriction> restrictions;
    std::map<int,std::vector<Restriction>> projected;
    std::vector<std::array<int,N>> stabilizer;
    Table val[limit]{},truth{},all{};
    Table critical[N]{},diff[limit][N]{};
    int reads[limit]{},nots=0;
    long long nodes=0;
    Search(Boards& bb,int mask,int d):b(bb),s(mask),depth(d){
        for(int i=0;i<N;i++)if(s>>i&1)vertices.push_back(i);
        for(int x=0;x<=full;x++){
            Bits bit=Bits(1)<<(x%64);int k=x/64;
            all[k]|=bit;
            if(b.edges[s&x])truth[k]|=bit;
            for(int i:vertices)if(x>>i&1)val[i][k]|=bit;
            if((x&~s)||b.edges[x])continue;
            for(int i:vertices)if(!(x>>i&1)&&(b.nb[i]&x))critical[i][k]|=bit;
        }
        for(auto p:b.group){
            int img=0;for(int i:vertices)img|=1<<p[i];if(img==s)stabilizer.push_back(p);
        }
        for(int k=(s-1)&s;k;k=(k-1)&s){
            if(b.core[k]!=k)continue;
            int eligible=s&~k&~b.neighborhood[k];
            for(int p=eligible;;p=(p-1)&eligible){
                if(!b.edges[p])restrictions.push_back({k,p,b.bound[k]});
                if(!p)break;
            }
        }
    }
    const std::vector<Restriction>& projection(int active){
        auto i=projected.find(active);if(i!=projected.end())return i->second;
        std::map<std::pair<int,int>,int> best;
        for(auto r:restrictions){
            int free=active&b.neighborhood[r.ones]&~r.retained;
            for(int f=free;;f=(f-1)&free){
                auto key=std::make_pair((r.retained|f)&active,r.ones&active);
                best[key]=std::max(best[key],r.score);if(!f)break;
            }
        }
        std::vector<Restriction> out;
        for(auto entry:best)out.push_back({entry.first.first,entry.first.second,entry.second});
        std::sort(out.begin(),out.end(),[](auto x,auto y){return x.score>y.score;});
        return projected.emplace(active,std::move(out)).first->second;
    }
    void derivatives(int w){
        for(int i:vertices){
            int jump=1<<i;
            for(int k=0;k<words;k++){
                Bits shifted=jump<64?val[w][k]>>jump:val[w][k^(jump/64)];
                diff[w][i][k]=(shifted^val[w][k])&critical[i][k];
            }
        }
    }
    bool charged(int goal){
        int active=0,readGate=0,ends=0,twice=0,extra=nots;
        int n=int(prefix.size());
        for(int w=0;w<N+n;w++){
            if(w<N&&reads[w])active|=1<<w;
            if(w>=N){if(reads[w])readGate|=1<<w;else ends|=1<<w;}
            if(reads[w]>1){twice|=1<<w;extra+=reads[w]-1;}
        }
        std::vector<int> choices;
        for(int g=readGate;;g=(g-1)&readGate){
            int h=g;
            if(extra+pop(h)<goal){
                for(int p=active;p;p&=p-1){
                    int a=low(p);bool required=false;
                    for(int k=0;k<words;k++)if(critical[a][k]){
                        Bits remaining=critical[a][k];
                        for(int q=g|ends;q&&remaining;q&=q-1)remaining&=~diff[low(q)][a][k];
                        if(remaining){required=true;break;}
                    }
                    if(required)h|=1<<a;
                }
                if(extra+pop(h)<goal)choices.push_back(h);
            }
            if(!g)break;
        }
        if(choices.empty())return true;
        for(auto r:projection(active)){
            int fixed=active&~r.retained,ones=r.ones,bonus=0,ordinary=0,anc[limit]{};
            for(int j=0;j<n;j++){
                Gate g=prefix[j];int w=N+j,m=(1<<g.a)|(1<<g.b),c=m&fixed,o=m&ones;
                bool hi=false,lo=false;
                if(g.op==2){hi=(c&~o)!=0;lo=o!=0;}
                else if(g.op==1){hi=o==m;lo=(c&~o)!=0;}
                else{hi=o!=0;lo=(c&~o)==m;}
                if(hi||lo){fixed|=1<<w;if(hi)ones|=1<<w;bonus+=2-pop(c);}
                else if(c)anc[w]=anc[low(m&~c)];
                else{ordinary|=1<<j;anc[w]=(1<<j)|anc[g.a]|anc[g.b];}
            }
            for(int p=fixed&twice;p;p&=p-1)bonus+=reads[low(p)]-1;
            int tips=0;for(int q=ends;q;q&=q-1)tips|=anc[low(q)];
            choices.erase(std::remove_if(choices.begin(),choices.end(),[&](int h){
                int live=tips;for(int q=h&readGate;q;q&=q-1)live|=anc[low(q)];
                return r.score+bonus+pop(h&fixed)+pop(ordinary&~live)>=goal;
            }),choices.end());
            if(choices.empty())return true;
        }
        return false;
    }
    bool prove(int goal){
        nodes++;
        if(!prefix.empty()&&charged(goal))return true;
        int j=int(prefix.size()),next=N+j;
        if(j>=pop(s)-2+goal)return true;
        if(j==depth)return false;
        std::vector<int> wires=vertices;for(int w=N;w<next;w++)wires.push_back(w);
        for(int ii=0;ii<int(wires.size());ii++)for(int jj=ii;jj<int(wires.size());jj++){
            int a=wires[ii],c=wires[jj];
            bool canonical=true;
            for(auto p:stabilizer){
                auto im=[&](int i){return i<N?p[i]:i;};int ia=im(a),ic=im(c);
                if(std::minmax(ia,ic)>=std::minmax(a,c))continue;
                bool fixing=true;
                for(auto g:prefix){int u=im(g.a),v=im(g.b);if(std::minmax(u,v)!=std::minmax(g.a,g.b)){fixing=false;break;}}
                if(fixing){canonical=false;break;}
            }
            if(!canonical)continue;
            for(int op=(ii==jj?2:0);op<=(ii==jj?2:1);op++){
                bool order=true;
                for(int t=std::max(0,c-N+1);t<j;t++){
                    auto g=prefix[t];if(std::make_tuple(g.a,g.b,g.op)>std::make_tuple(a,c,op)){order=false;break;}
                }
                if(!order)continue;
                for(int k=0;k<words;k++)val[next][k]= op==2?(all[k]^val[a][k]):
                    op==1?(val[a][k]&val[c][k]):(val[a][k]|val[c][k]);
                if(val[next]==truth){
                    if(s==full)std::cerr<<"found complete circuit at size "<<j+1<<"\n";
                    return false;
                }
                if(val[next]==Table{}||val[next]==all||std::any_of(wires.begin(),wires.end(),[&](int w){return val[w]==val[next];}))continue;
                derivatives(next);prefix.push_back({a,c,op});reads[a]++;
                if(op==2)nots++;else reads[c]++;
                bool ok=prove(goal);
                if(op==2)nots--;else reads[c]--;reads[a]--;prefix.pop_back();
                if(!ok)return false;
            }
        }
        return true;
    }
};

int main(int argc,char**argv){
    if(argc!=4)return 2;
    int depth=std::atoi(argv[1]),seed=std::atoi(argv[2]);
    if(depth<1||depth>=limit-N||seed<2||seed>=N)return 2;
    std::ifstream in(argv[3]);std::string decimal;int known;
    if(!in)return 3;
    while(in>>decimal>>known){
        unsigned __int128 mask=0;
        for(char c:decimal){
            if(c<'0'||c>'9')return 4;
            mask=10*mask+(c-'0');
        }
        int active=0,slot=0;
        for(int i=0;i<N;i++)for(int j=i+1;j<N;j++,slot++){
            if((mask>>slot)&1)active|=(1<<i)|(1<<j);
        }
        if(active!=full || (mask>>slot)!=0)return 5;
        if(known==N-1){std::cout<<decimal<<" "<<known<<" "<<known<<" 0"<<std::endl;continue;}
        auto owner=std::make_unique<Boards>(mask,seed);Boards& b=*owner;
        long long visits=0;
        for(int n=2;n<=N;n++)for(int s=1;s<=full;s++)if(pop(s)==n&&b.core[s]==s){
            if(s!=b.rep[s]){b.bound[s]=b.bound[b.rep[s]];continue;}
            if(n<=seed){b.bound[s]=b.upper(s);continue;}
            Search problem(b,s,depth);
            int start=0;
            for(auto r:problem.restrictions)start=std::max(start,r.score);
            b.bound[s]=start;
            while(b.bound[s]<b.upper(s)&&problem.prove(b.bound[s]+1))b.bound[s]++;
            visits+=problem.nodes;
        }
        if(b.upper(full)+N-1!=known)throw std::logic_error("target mismatch");
        std::cout<<decimal<<" "<<N-1+b.bound[full]<<" "<<known<<" "<<visits<<"\n"<<std::flush;
    }
}
