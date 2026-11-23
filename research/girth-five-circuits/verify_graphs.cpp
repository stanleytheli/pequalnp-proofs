// Independently check coverage by generating labeled graphs one edge at a time.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <vector>

using Mask = std::uint32_t;
struct Case { Mask mask; int optimum; };

class Verification {
    int n;
    int pairs;
    std::array<std::array<int,8>,8> positions{};
    std::vector<std::pair<int,int>> edges;
    std::vector<bool> covered;
    std::array<unsigned,8> neighbors{};
    std::size_t listed = 0, visited = 0;

    void enumerate(int k, Mask mask) {
        if (k == pairs) {
            for (int i=0;i<n;i++) if (!neighbors[i]) return;
            if (!covered[mask]) throw std::runtime_error("missing labeled graph");
            visited++;
            return;
        }
        enumerate(k+1,mask);
        auto [i,j] = edges[k];
        if (neighbors[i] & neighbors[j]) return;
        for (int r=0; r<n; r++)
            if ((neighbors[i] & (1u<<r)) && (neighbors[r] & neighbors[j])) return;
        neighbors[i] |= 1u<<j;
        neighbors[j] |= 1u<<i;
        enumerate(k+1,mask | (1u<<k));
        neighbors[i] ^= 1u<<j;
        neighbors[j] ^= 1u<<i;
    }

    void add(Case entry) {
        int cover = n;
        for (unsigned set=0; set<(1u<<n); set++) {
            bool ok = true;
            for (int k=0; k<pairs; k++) {
                auto [a,b] = edges[k];
                if ((entry.mask & (1u<<k)) && !(set & ((1u<<a)|(1u<<b)))) ok = false;
            }
            if (ok) cover = std::min(cover, __builtin_popcount(set));
        }
        if (__builtin_popcount(entry.mask)+cover-1 != entry.optimum)
            throw std::runtime_error("incorrect cover or optimum");
        std::vector<int> perm(n);
        std::iota(perm.begin(),perm.end(),0);
        std::set<Mask> images;
        do {
            Mask relabeled = 0;
            for (int k=0;k<pairs;k++) if (entry.mask & (1u<<k)) {
                auto [a,b] = edges[k];
                relabeled |= 1u << positions[perm[a]][perm[b]];
            }
            images.insert(relabeled);
        } while (std::next_permutation(perm.begin(),perm.end()));
        for (auto m : images) {
            if (covered[m]) throw std::runtime_error("duplicate isomorphism class");
            covered[m] = true;
            listed++;
        }
    }

public:
    explicit Verification(int vertices) : n(vertices), pairs(n*(n-1)/2),
        covered(std::size_t(1)<<pairs) {
        for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
            positions[i][j]=positions[j][i]=int(edges.size());
            edges.emplace_back(i,j);
        }
    }
    void run(const std::vector<Case>& cases) {
        for (auto c : cases) add(c);
        enumerate(0,0);
        if (visited != listed) throw std::runtime_error("listed graph violates girth or has an isolate");
        std::cout << n << " vertices, " << cases.size() << " classes, "
                  << visited << " labeled graphs\n";
    }
};

int main(int argc,char** argv) {
    if (argc!=2) return 2;
    std::ifstream input(argv[1]);
    if (!input) return 2;
    std::array<std::vector<Case>,9> table;
    int n, goal;
    Mask graph;
    while (input >> n >> graph >> goal) {
        if (n<2 || n>8) return 2;
        table[n].push_back({graph,goal});
    }
    for(n=2;n<=8;n++) Verification(n).run(table[n]);
}
