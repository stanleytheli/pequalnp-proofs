# One internal AND and arbitrary shared OR gates

Let G be finite and simple, with m>0 edges, minimum vertex cover τ, and no triangles or four-cycles. The final terms are x_z AND B_z, joined by a binary OR tree over distinct centers z. Earlier gates may be reused arbitrarily. If at most one of those gates is an AND and the others are binary OR gates, the circuit needs at least m+τ−1 gates to compute the edge function. The usual star construction attains equality.

Let q count the earlier OR gates and c the centers. Discard unused gates and simplify constants. A remaining internal AND has the form h=(OR A) AND (OR B), with nonempty raw supports A and B. A raw variable counts as an available wire of width one. The two operands, and any subexpression of either, may also feed unrelated raw OR paths. All downstream effects of h before the terminal ANDs are by OR paths. Each detected edge has a center as an endpoint, so c≥τ. It suffices to show q+1≥m−c; if no internal AND exists the usual stronger bound q≥m−c follows directly.

An OR network producing raw subsets R_z⊆N(z) at distinct centers needs at least Σ_z(|R_z|−1) gates. In the raw cone for R_z, at least |R_z|−1 gates represent two or more different labels. Fold empty and singleton sets and count edges in the remaining connected binary network to see this. Such gates cannot occur in the cone of another center because distinct vertices have at most one common neighbor. Empty output sets are harmless in this inequality.

## Repair of edges in one star

Delete h by setting it false, preserving its raw operand cones for counting purposes. This leaves neighbor sums R_z at the centers. Suppose all edges missed by these sums form a star centered at a, with the other endpoints D contained in one available raw OR wire W. Then q+1≥m−c.

Indeed, project the raw OR circuit to N(a) by assigning all other variables false. W now contains every label in D. If a is a center, virtually join W to R_a in this projection at cost at most one gate. The resulting output contains R_a∪D, and requires at least |R_a∪D|−1 wide projected gates. No corresponding original gate can be counted in the unprojected cone of another center: two of its raw labels are neighbors of a, whereas a cone of z≠a contains only neighbors of z. The other centers and a together cover all m edges, giving q+1≥m−c.

If a is absent from the list of centers and D is nonempty, the projected W alone supplies at least |D|−1 wide gates, disjoint from all counted center cones. Consequently q≥Σ_z(|R_z|−1)+|D|−1≥m−c−1. If no edge is missing, the raw OR bound already suffices.

## Cases for the internal gate

If A={a}, h can fire on a two-vertex input only when it contains a. If a∈B then h=x_a. Otherwise every edge lost by deleting h is incident to a with its other endpoint in B. Apply the one-star repair. The argument for singleton B is symmetric.

Now assume both supports have size at least two, and put S=A∩B. Any center reached by h is adjacent to every vertex in S: h is true on those singletons, the output must reject the center singleton, and its term accepts the corresponding pair. If |S|≥2, there is at most one such center z. Every lost edge upon deleting h is then incident to z. If z∈A, its counterparts are in B; if z∈B, they are in A. If z lies in neither, its counterparts must all lie in S, hence in A. Apply the one-star repair.

It remains that |S|≤1. Replace h by the OR of S, using false or a raw input at no gate cost. This gives a residual shared raw OR network with outputs R_z⊆N(z). Call a center active if some graph edge was detected by its original term and is no longer detected by that term. On such an edge {z,u} neither endpoint is in S, since a singleton from S would have preserved the detection through the same OR paths. Thus z∈A and u∈B, or vice versa. If z∈A, every member of B is adjacent to z by testing {z,b} in that term. There is at most one such center in A since |B|≥2. The analogous statement holds for B.

At each active center, virtually join its residual R_z to the opposite original operand. This costs at most k OR gates, where k≤2 is the number of active centers. All enlarged neighbor sums cover every original edge. If k=2, the edge between the two active centers occurs in both enlarged sums. Hence their total cardinality is at least m+max(0,k−1). Applying the raw OR bound gives q+k≥m+max(0,k−1)−c, as required.

The original circuit therefore uses at least q+1+2c−1≥m+c−1≥m+τ−1 gates. This is a paper proof.

## Many wide internal ANDs with shared OR input cones

The bound also holds with any number h of auxiliary AND gates, under the following assumptions. Each has two independently formed raw OR operands A_i,B_i, each of size at least two, with |A_i∩B_i|≤1. The operand cones may share arbitrary gates with each other and with the final neighbor signals. The outputs of the ANDs go through an arbitrary shared OR network to the final stars. No auxiliary AND depends on another.

Replace each auxiliary output by its singleton intersection or false. This produces residual raw sums R_z⊆N(z) at all centers, at no extra gate cost. If a z-term formerly detected an edge that its residual sum misses, its final OR contained a successful auxiliary. Since neither endpoint is in that auxiliary's intersection, one endpoint belongs to each exclusive operand. For each auxiliary record all centers at which such a detection occurred through that auxiliary. For that center, its opposite whole operand is contained in its neighborhood, by evaluating its contribution on the input consisting of the center and each member of that operand. There is at most one such center on each side of an auxiliary.

Write s for the number of auxiliaries with just one recorded center and p for the number of *distinct unordered pairs* obtained from the auxiliaries with two. At every center collect its residual set and the opposite raw operands just identified. Their union U_z is contained in N(z) and all these unions cover all m edges. For each of the p distinct pairs {z,w}, the edge zw belongs to both corresponding unions. Therefore Σ_z |U_z|≥m+p.

At z, group the operands arising from double-center auxiliaries with the same partner w. All sets in this group contain w. Leave each single-center operand and the residual sum as separate groups. Thus the total number of groups over all centers is at most c+s+2p. A group of raw OR outputs with a common label has a connected union of input cones, even after folding wires with zero or one label: paths to that common raw input connect their outputs. If its union has b distinct labels, at least b−1 wide OR gates occur in this union. More generally the union of all the cones at z has at most as many connected components as groups, and contains at least |U_z| minus that number of wide gates, by the same connected binary network count on each component. A raw gate shared by two different centers' cones would have to contain at least two common neighbors to contribute to both counts. Thus q≥Σ_z |U_z|−(c+s+2p)≥m−c−s−p. As h≥s+p, the original q+h+2c−1 gates reach the claimed bound.

This argument counts shared raw OR gates at most once. It specifically permits physical sharing between operands of different nonlinear gates.
