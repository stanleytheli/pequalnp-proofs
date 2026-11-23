#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <tuple>
#include <vector>

using Bits=std::uint64_t;
constexpr int N=VERTICES, full=(1<<N)-1, limit=30;
int pop(int a){return __builtin_popcount(unsigned(a));}
int low(int a){return __builtin_ctz(unsigned(a));}
struct Boards{
    int neighborhood[full+1]{},nb[N]{},core[full+1]{},edges[full+1]{},alpha[full+1]{},bound[full+1]{},rep[full+1]{};
    std::vector<std::array<int,N>> group;
    std::array<Bits,N> rows[full+1]{};
    Bits domain[full+1]{},posDomain[full+1]{};
    void tests(int s){
        if(domain[s])return;
        int i=0;for(int x=s;;x=(x-1)&s){
            bool take=pop(x)==2&&edges[x]==1;
            if(edges[x]==0){
                int dom=x;for(int p=x;p;p&=p-1)dom|=nb[low(p)];
                take=(dom&s)==s;
            }
            if(take){
                if(edges[x])posDomain[s]|=Bits(1)<<i;
                if(i>=62)throw std::logic_error("too many rows");
                for(int p=x;p;p&=p-1)rows[s][low(p)]|=Bits(1)<<i;
                i++;
            }
            if(!x)break;
        }
        domain[s]=(Bits(1)<<i)-1;
    }
    explicit Boards(Bits graph){
        int index=0;
        for(int i=0;i<N;i++)for(int j=i+1;j<N;j++,index++)if((graph>>index)&1){
            nb[i]|=1<<j;nb[j]|=1<<i;
        }
        for(int s=1;s<=full;s++){
            int a=low(s),r=s^(1<<a);
            neighborhood[s]=neighborhood[r]|nb[a];edges[s]=edges[r]+pop(nb[a]&r);alpha[s]=std::max(alpha[r],1+alpha[r&~nb[a]]);
            for(int j=0;j<N;j++)if((s>>j&1)&&(nb[j]&s))core[s]|=1<<j;
            rep[s]=s;
        }
        std::array<int,N> perm{};
        automorphisms(perm,0,0);
    }
    void automorphisms(std::array<int,N>& perm,int i,int used){
        if(i==N){
            group.push_back(perm);
            std::array<int,full+1> img{};
            for(int s=1;s<=full;s++){img[s]=img[s&(s-1)]|(1<<perm[low(s)]);rep[s]=std::min(rep[s],img[s]);}
            return;
        }
        for(int j=0;j<N;j++)if(!(used>>j&1)&&pop(nb[j])==pop(nb[i])){
            bool valid=true;for(int k=0;k<i;k++)if(((nb[i]>>k)&1)!=((nb[j]>>perm[k])&1)){valid=false;break;}
            if(valid){perm[i]=j;automorphisms(perm,i+1,used|(1<<j));}
        }
    }
    int upper(int s)const{return edges[s]-alpha[s];} // size plus one minus vertex count
};
struct Gate{int a,b;bool meet;};
struct Restriction{int retained,ones,score;};

struct Case{
    Boards& b;int s,depth;
    std::vector<Gate> prefix;
    std::vector<int> positive,negative,vertices;
    std::vector<Restriction> restrictions;
    std::vector<std::array<int,N>> stabilizer;
    Bits values[limit]{},truthMask=0,allTests=0;
    int reads[limit]{};
    std::map<int,std::vector<Restriction>> projected;
    long long nodes=0;
    Case(Boards& boards,int verticesMask,int maxDepth):b(boards),s(verticesMask),depth(maxDepth){
        for(int v=0;v<N;v++)if(s>>v&1)vertices.push_back(v);
        for(int k=s;k;k=(k-1)&s){
            if(pop(k)==2&&b.edges[k])positive.push_back(k);
            if(b.edges[k]==0){
                int dominates=k;for(int a=k;a;a&=a-1)dominates|=b.nb[low(a)];
                if((dominates&s)==s)negative.push_back(k);
            }
        }
        std::vector<int> tests=positive;tests.insert(tests.end(),negative.begin(),negative.end());
        if(tests.size()>62)throw std::logic_error("too many test rows");
        for(int t=0;t<int(tests.size());t++)for(int v:vertices)if(tests[t]>>v&1)values[v]|=Bits(1)<<t;
        truthMask=(Bits(1)<<positive.size())-1;allTests=(Bits(1)<<tests.size())-1;
        for(auto perm:b.group){
            int img=0;for(int v:vertices)img|=1<<perm[v];
            if(img==s)stabilizer.push_back(perm);
        }
        for(int k=(s-1)&s;k;k=(k-1)&s){
            if(b.core[k]!=k)continue;
            int eligible=s^k;for(int a=k;a;a&=a-1)eligible&=~b.nb[low(a)];
            for(int p=eligible;;p=(p-1)&eligible){
                if(b.edges[p]==0)restrictions.push_back({k,p,b.bound[k]});
                if(p==0)break;
            }
        }
        std::sort(restrictions.begin(),restrictions.end(),[](auto x,auto y){
            return std::make_tuple(-x.score,x.retained,x.ones)<std::make_tuple(-y.score,y.retained,y.ones);
        });
    }
    const std::vector<Restriction>& projection(int touched){
        auto it=projected.find(touched);if(it!=projected.end())return it->second;
        std::map<std::pair<int,int>,int> kept;
        for(auto r:restrictions){
            int free=touched&b.neighborhood[r.ones]&~r.retained;
            for(int f=free;;f=(f-1)&free){
                auto key=std::make_pair((r.retained|f)&touched,r.ones&touched);
                kept[key]=std::max(kept[key],r.score);
                if(f==0)break;
            }
        }
        std::vector<Restriction> cases;
        for(auto item:kept)cases.push_back({item.first.first,item.first.second,item.second});
        std::sort(cases.begin(),cases.end(),[](auto x,auto y){return x.score>y.score;});
        return projected.emplace(touched,std::move(cases)).first->second;
    }
    std::vector<int> future_sets(int touched){
        // Wires without an in-prefix reader are already required to be read downstream.
        // Every minterm and maximal false row must differ, in the positive direction,
        // at a wire read by the completion. Record clauses not covered by zero-read wires.
        int end=N+int(prefix.size()), active=touched|(((1<<int(prefix.size()))-1)<<N);
        std::vector<int> clauses;
        for(int j=0;j<int(negative.size());j++)for(int i=0;i<int(positive.size());i++){
            int d=positive[i]&~negative[j];bool hit=(d&~touched)!=0;
            if(hit)continue;
            for(int w=0;w<end;w++)if((active>>w&1)&&((values[w]>>i)&1)&&!((values[w]>>(positive.size()+j))&1)){
                if(!reads[w]){hit=true;break;}d|=1<<w;
            }
            if(!hit)clauses.push_back(d);
        }
        std::sort(clauses.begin(),clauses.end(),[](int x,int y){return std::make_pair(pop(x),x)<std::make_pair(pop(y),y);});
        std::vector<int> minimal{0};
        for(int clause:clauses){
            std::vector<int> next;bool change=false;
            for(int h:minimal){
                if(h&clause)next.push_back(h);
                else{change=true;for(int m=clause;m;m&=m-1)next.push_back(h|(m&-m));}
            }
            if(!change)continue;
            std::sort(next.begin(),next.end(),[](int x,int y){return std::make_pair(pop(x),x)<std::make_pair(pop(y),y);});
            minimal.clear();
            for(int h:next)if(std::none_of(minimal.begin(),minimal.end(),[h](int g){return (g&h)==g;}))minimal.push_back(h);
        }
        return minimal;
    }
    std::vector<int> remaining(int touched,int goal){
        auto plans=future_sets(touched);
        int used=0;
        for(int w=0;w<N+int(prefix.size());w++)used+=std::max(0,reads[w]-1);
        plans.erase(std::remove_if(plans.begin(),plans.end(),[&](int h){return pop(h)+used>=goal;}),plans.end());
        return plans;
    }
    bool charged(int goal,std::vector<int>& future){
        int touched=0,usedTwice=0;for(int w=0;w<N+int(prefix.size());w++){
            if(w<N&&reads[w])touched|=1<<w;
            if(reads[w]>=2)usedTwice|=1<<w;
        }
        if(future.empty())return true;
        for(auto r:projection(touched)){
            int fixed=touched&~r.retained,ons=r.ones,bonus=0;
            for(int j=0;j<int(prefix.size());j++){
                Gate g=prefix[j];int m=(1<<g.a)|(1<<g.b),c=fixed&m,o=ons&m;
                bool isOne=g.meet?o==m:o!=0;
                bool isZero=g.meet?(c&~o)!=0:(c&~o)==m;
                if(isOne||isZero){
                    fixed|=1<<(N+j);if(isOne)ons|=1<<(N+j);bonus+=2-pop(c);
                }
            }
            for(int t=fixed&usedTwice;t;t&=t-1)bonus+=reads[low(t)]-1;
            future.erase(std::remove_if(future.begin(),future.end(),[&](int h){return r.score+bonus+pop(fixed&h)>=goal;}),future.end());
            if(future.empty())return true;
        }
        return false;
    }
    struct ExtraSlice { int k,f,p,score; };
    std::map<int,std::vector<ExtraSlice>> slice_cache;
    const std::vector<ExtraSlice>& extra_slices(int touched){
        auto found=slice_cache.find(touched);
        if(found!=slice_cache.end())return found->second;
        std::vector<ExtraSlice> all;
        for(auto c:restrictions){
            int exposed=touched&b.neighborhood[c.ones]&~c.retained;
            for(int f=exposed;f;f=(f-1)&exposed)all.push_back({c.retained,f,c.ones&touched,c.score});
        }
        std::sort(all.begin(),all.end(),[](auto a,auto b){
            return std::make_tuple(-a.score,a.k,a.f,a.p)<std::make_tuple(-b.score,b.k,b.f,b.p);
        });
        all.erase(std::unique(all.begin(),all.end(),[](auto a,auto b){return a.k==b.k&&a.f==b.f&&a.p==b.p;}),all.end());
        if(slice_cache.size()>=40)slice_cache.clear();
        return slice_cache.emplace(touched,std::move(all)).first->second;
    }
    bool semantic_free(int goal,std::vector<int>& future){
        int touched=0,usedTwice=0;for(int w=0;w<N+int(prefix.size());++w){
            if(w<N&&reads[w])touched|=1<<w;
            if(reads[w]>=2)usedTwice|=1<<w;
        }
        if(future.empty())return true;
        for(auto c:extra_slices(touched)){
            b.tests(c.k);
            int length=__builtin_popcountll(b.domain[c.k]);
            if(length+pop(c.f)>=63)continue;
            Bits domain=(Bits(1)<<(length+pop(c.f)))-1;
            Bits neg=b.domain[c.k]^b.posDomain[c.k],pos=domain^neg;
            Bits row[limit]{},previous[limit]{};int previousCount=0;
            for(int t=c.k;t;t&=t-1){
                int a=low(t);previous[previousCount++]=row[a]=b.rows[c.k][a];
            }
            for(int t=c.f;t;t&=t-1){
                int a=low(t);previous[previousCount++]=row[a]=Bits(1)<<length++;
            }
            for(int t=c.p;t;t&=t-1)row[low(t)]=domain;
            int fixed=touched&~(c.k|c.f),bonus=0;
            for(int j=0;j<int(prefix.size());j++){
                auto g=prefix[j];int w=N+j,m=(1<<g.a)|(1<<g.b);
                row[w]=g.meet?(row[g.a]&row[g.b]):(row[g.a]|row[g.b]);
                bool zero=(row[w]&pos)==0,one=(row[w]&neg)==neg;
                if(zero||one){
                    row[w]=zero?0:domain;
                    bonus+=2-pop(fixed&m);fixed|=1<<w;
                }else{
                    bool duplicate=false;
                    for(int h=0;h<previousCount;h++){
                        Bits other=previous[h];
                        if((row[w]&pos&~other)||(other&neg&~row[w]))continue;
                        duplicate=true;row[w]=other;
                    }
                    if(duplicate&&!(fixed&m))bonus++;
                    previous[previousCount++]=row[w];
                }
            }
            for(int t=fixed&usedTwice;t;t&=t-1)bonus+=reads[low(t)]-1;
            future.erase(std::remove_if(future.begin(),future.end(),[&](int h){return c.score+bonus+pop(fixed&h)>=goal;}),future.end());
            if(future.empty())return true;
        }
        return false;
    }
    bool semantic_charge(int goal,std::vector<int>& future){
        int touched=0,usedTwice=0;
        for(int w=0;w<N+int(prefix.size());w++){
            if(w<N&&reads[w])touched|=1<<w;
            if(reads[w]>=2)usedTwice|=1<<w;
        }
        if(future.empty())return true;
        int lastK=-1,lastP=-1;
        for(auto r:restrictions){
            int pinPos=r.ones&touched;
            if(r.retained==lastK&&pinPos==lastP)continue;
            lastK=r.retained;lastP=pinPos;
            int fixed=touched&~r.retained,bonus=0;
            b.tests(r.retained);
            auto domain=b.domain[r.retained];
            Bits row[limit]{},previous[limit]{};int previousCount=0;
            for(int q=touched;q;q&=q-1){
                int w=low(q);
                row[w]=(pinPos>>w&1)?domain:b.rows[r.retained][w];
            }
            for(int q=r.retained;q;q&=q-1)previous[previousCount++]=b.rows[r.retained][low(q)];
            for(int j=0;j<int(prefix.size());j++){
                auto g=prefix[j];int w=N+j,m=(1<<g.a)|(1<<g.b);
                row[w]=g.meet?(row[g.a]&row[g.b]):(row[g.a]|row[g.b]);
                const Bits pos=b.posDomain[r.retained], neg=domain^pos;
                const bool forceZero=(row[w]&pos)==0;
                const bool forceOne=(row[w]&neg)==neg;
                if(forceZero||forceOne){
                    // Clamp immediately. Through a monotone suffix, this only
                    // raises positive-row outputs or lowers negative-row outputs.
                    row[w]=forceZero?0:domain;
                    bonus+=2-pop(fixed&m);
                    fixed|=1<<w;
                }else{
                    bool duplicate=false;
                    for(int h=0;h<previousCount;h++){
                        Bits other=previous[h];
                        if((row[w]&pos&~other)||(other&neg&~row[w]))continue;
                        duplicate=true;
                        // Rewire to a dominating earlier representative. Continue
                        // down the order to retain a maximal available choice.
                        row[w]=other;
                    }
                    if(duplicate&&!(fixed&m))bonus++;
                    previous[previousCount++]=row[w];
                }
            }
            for(int t=fixed&usedTwice;t;t&=t-1)bonus+=reads[low(t)]-1;
            future.erase(std::remove_if(future.begin(),future.end(),[&](int h){return r.score+bonus+pop(fixed&h)>=goal;}),future.end());
            if(future.empty())return true;
        }
        return false;
    }
    bool completes(int targetSize,const std::vector<int>& wires){
        int budget=(targetSize-int(prefix.size())+1)/2;
        if(budget<=0)return false;
        std::vector<Bits> sets;
        Bits achieved=0;
        for(int i=0;i<int(wires.size());i++)for(int j=i+1;j<int(wires.size());j++){
            Bits mask=values[wires[i]]&values[wires[j]];
            if(!mask||(mask&~truthMask))continue;
            if(std::any_of(sets.begin(),sets.end(),[mask](Bits x){return (x&mask)==mask;}))continue;
            sets.erase(std::remove_if(sets.begin(),sets.end(),[mask](Bits x){return (x&mask)==x;}),sets.end());
            sets.push_back(mask);achieved|=mask;
        }
        return achieved==truthMask&&cover(sets,truthMask,budget);
    }
    bool cover(const std::vector<Bits>& sets,Bits need,int budget){
        if(!need)return true;
        if(budget<=0)return false;
        int width=0;
        for(Bits m:sets)width=std::max(width,__builtin_popcountll(m&need));
        if(width*budget<__builtin_popcountll(need))return false;
        Bits best=0;int count=100000;
        for(Bits p=need;p;p&=p-1){
            Bits point=p&-p;
            int num=0;for(Bits m:sets)if(m&point)num++;
            if(num<count){best=point;count=num;}
        }
        for(Bits m:sets)if((m&best)&&cover(sets,need&~m,budget-1))return true;
        return false;
    }
    bool prove(int goal){
        nodes++;
        if(!prefix.empty()){
            int touched=0;for(int w=0;w<N;w++)if(reads[w])touched|=1<<w;
            auto future=remaining(touched,goal);
            if(charged(goal,future)||semantic_charge(goal,future)||semantic_free(goal,future))return true;
        }
        int next=N+int(prefix.size()), cap=pop(s)-2+goal;
        std::vector<int> wires=vertices;
        for(int w=N;w<next;w++)wires.push_back(w);
        if(completes(cap,wires))return false;
        if(int(prefix.size())>=cap-1)return true;
        if(int(prefix.size())==depth)return false;
        struct Option{Bits val;int a,b;bool meet;};
        std::vector<Option> options;
        for(int i=0;i<int(wires.size());i++)for(int j=i+1;j<int(wires.size());j++){
            int a=wires[i],c=wires[j];
            for(bool meet:{false,true}){
                Bits val=meet?(values[a]&values[c]):(values[a]|values[c]);
                options.push_back({val,a,c,meet});
            }
        }
        for(int i=0;i<int(wires.size());i++)for(int j=i+1;j<int(wires.size());j++){
            int a=wires[i],c=wires[j];
            bool canonical=true;
            for(auto &p:stabilizer){
                auto image=[&](int w){return w<N?p[w]:w;};
                int ia=image(a),ic=image(c);
                if(std::minmax(ia,ic)>=std::minmax(a,c))continue;
                bool fixes=true;
                for(auto g:prefix){
                    int u=image(g.a),v=image(g.b);
                    if(std::minmax(u,v)!=std::minmax(g.a,g.b)){fixes=false;break;}
                }
                if(fixes){canonical=false;break;}
            }
            if(!canonical)continue;
            for(bool meet:{false,true}){
                bool ordered=true;
                int earliest=std::max(0,std::max(a,c)-N+1);
                for(int t=earliest;t<int(prefix.size());t++){
                    auto g=prefix[t];
                    if(std::make_tuple(g.a,g.b,g.meet)>std::make_tuple(a,c,meet)){ordered=false;break;}
                }
                if(!ordered)continue;
                Bits val=meet?(values[a]&values[c]):(values[a]|values[c]);
                if(!(val&~truthMask)||__builtin_popcountll(val&truthMask)<2)continue;
                // An earlier signal may replace this one if positive rows increase
                // and negative rows decrease. Correctness on these rows suffices.
                bool redundant=false;
                for(int w:wires)if(!(val&truthMask&~values[w])&&!(values[w]&~truthMask&~val)){
                    redundant=true;break;
                }
                if(redundant)continue;
                for(auto alternative:options){
                    Bits alt=alternative.val;
                    if((val&truthMask&~alt)||(alt&~truthMask&~val))continue;
                    if(alt!=val||std::make_tuple(alternative.a,alternative.b,alternative.meet)<std::make_tuple(a,c,meet)){
                        redundant=true;break;
                    }
                }
                if(redundant)continue;
                values[next]=val;reads[a]++;reads[c]++;prefix.push_back({a,c,meet});
                bool ok=prove(goal);
                prefix.pop_back();reads[c]--;reads[a]--;if(!ok)return false;
            }
        }
        return true;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int depth=std::atoi(argv[1]),seed=std::atoi(argv[2]);
    if(depth<1||depth>=limit-N||seed<2||seed>9)return 2;
    std::ifstream in(argv[3]);Bits mask;int known;
    while(in>>mask>>known){
        Boards b(mask);
        long long visits=0;
        for(int n=2;n<=N;n++)for(int s=1;s<=full;s++)if(pop(s)==n&&b.core[s]==s){
            if(s!=b.rep[s]){b.bound[s]=b.bound[b.rep[s]];continue;}
            if(n<=seed){b.bound[s]=b.upper(s);continue;}
            Case problem(b,s,depth);
            int start=0;
            for(auto r:problem.restrictions)start=std::max(start,r.score);
            b.bound[s]=start;
            while(b.bound[s]<b.upper(s)&&problem.prove(b.bound[s]+1))b.bound[s]++;
            visits+=problem.nodes;
        }
        if(b.upper(full)+N-1!=known)throw std::logic_error("target mismatch");
        std::cout<<mask<<" "<<N-1+b.bound[full]<<" "<<known<<" "<<visits<<"\n"<<std::flush;
    }
}
