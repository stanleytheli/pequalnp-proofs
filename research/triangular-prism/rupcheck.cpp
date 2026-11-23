// Streaming checker for the RUP fragment of textual LRAT, rejecting RAT steps.
#include <algorithm>
#include <charconv>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
struct Parser {
    const char* s;const char* e;
    explicit Parser(const std::string& line):s(line.data()),e(s+line.size()){}
    void space(){while(s!=e && (*s==' '||*s=='\r'||*s=='\t'))s++;}
    int number(){space();int n;auto r=std::from_chars(s,e,n);if(r.ec!=std::errc())throw std::runtime_error("expected integer");s=r.ptr;return n;}
};
int main(int argc,char**argv)try {
    if(argc!=3)return 2;
    std::ifstream cnf(argv[1]),proof(argv[2]);if(!cnf||!proof)return 2;
    std::string line;int n=0,expected=0;
    std::vector<std::vector<int>> db(1);std::vector<bool> active(1);
    auto store=[&](int id,std::vector<int> c){
        std::sort(c.begin(),c.end());c.erase(std::unique(c.begin(),c.end()),c.end());
        if(id<int(active.size()))throw std::runtime_error("reused addition id");
        db.resize(id+1);active.resize(id+1);db[id]=std::move(c);active[id]=true;
    };
    while(std::getline(cnf,line)){
        if(line.empty()||line[0]=='c')continue;
        if(line[0]=='p'){std::istringstream in(line);std::string p,kind;in>>p>>kind>>n>>expected;if(kind!="cnf"||n<=0)throw std::runtime_error("invalid header");continue;}
        Parser p(line);std::vector<int> c;
        for(int l;(l=p.number());){if(std::abs(l)>n)throw std::runtime_error("invalid literal");c.push_back(l);}
        store(int(db.size()),std::move(c));
    }
    if(expected!=int(db.size())-1)throw std::runtime_error("wrong number of original clauses");
    std::vector<signed char> val(n+1,0);std::vector<int> changed;long additions=0,removed=0;
    auto assign=[&](int lit){
        int v=std::abs(lit);signed char dir=lit>0?1:-1;
        if(val[v])return val[v]!=dir;
        val[v]=dir;changed.push_back(v);return false;
    };
    while(std::getline(proof,line)){
        if(line.empty())continue;
        Parser p(line);int id=p.number();p.space();
        if(p.s!=p.e&&*p.s=='d'){
            p.s++;for(int k;(k=p.number());){if(k<=0||k>=int(db.size())||!active[k])throw std::runtime_error("invalid deletion");
                active[k]=false;std::vector<int>().swap(db[k]);removed++;}
            continue;
        }
        std::vector<int> c;bool contradiction=false;
        for(int lit;(lit=p.number());){if(std::abs(lit)>n)throw std::runtime_error("unknown added variable");c.push_back(lit);contradiction|=assign(-lit);}
        for(int k;(k=p.number());){
            if(k<0)throw std::runtime_error("RAT inference outside supported fragment");
            if(k>=int(db.size())||!active[k])throw std::runtime_error("nonactive hint");
            if(contradiction)continue;
            int un=0,last=0;bool satisfied=false;
            for(int lit:db[k]){
                auto v=val[std::abs(lit)];if(v==0){++un;last=lit;}
                else if((v>0)==(lit>0)){satisfied=true;break;}
            }
            if(!satisfied && un==0)contradiction=true;
            else if(!satisfied && un==1)contradiction=assign(last);
        }
        if(!contradiction)throw std::runtime_error("RUP inference failed at "+std::to_string(id));
        for(int v:changed)val[v]=0;changed.clear();++additions;
        if(c.empty()){std::cout<<"verified empty clause "<<id<<", "<<additions<<" RUP additions, "<<removed<<" deletions\n";return 0;}
        store(id,std::move(c));
    }
    throw std::runtime_error("no empty clause");
}catch(const std::exception& x){std::cerr<<x.what()<<"\n";return 1;}
