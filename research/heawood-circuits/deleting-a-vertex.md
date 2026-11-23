# Consequences of the 23-gate single-vertex deletion

Let a binary monotone circuit for the Heawood edge function have s gates. Work with its live output cone and fold constants, aliases, and repeated operands. The independent pure-deletion replay in lower.cpp gives 23 as the minimum after deleting any vertex. The graph has no triangles or four-cycles, and each vertex has degree three.

Fix a raw input v to false. Write r for its number of reader slots. At least r gates disappear. One direct proof is to follow wires which have become constants. Each fixed wire has at least one outgoing reader slot, since the output stays nonconstant. If a fixed gate has c fixed input slots, charge 2−c additional gate removals. Counting fixed slots at all gates shows that the number of removed constant and boundary gates is

    1 + Σ_{fixed wires}(original fanout−1) + Σ_{fixed gates}(2−c).

In particular r≤s−23. If s≤24 all raw inputs have a single reader. Take any first gate and name its distinct raw inputs u and v. If it is AND, fixing v false prevents any dependence on u. A neighbor of u distinct from v still witnesses that dependence. If it is OR, fixing v true prevents dependence on u. When uv is an edge, the singleton {v} and edge {u,v} distinguish u. Otherwise u and v have at most one common neighbor, and a neighbor w of u outside N(v) gives the distinguishing inputs {v,w} and {u,v,w}. Hence s≥25.

If s=25 each raw input has at most two reader slots. A raw input with two readers cannot feed any AND gate: fixing that raw input false already uses both available deletions, and a directly-read AND adds one further unit in the fixed-gate sum. To see this even if its other operand becomes constant indirectly, choose the earliest AND that becomes fixed among descendants of the raw input. With other inputs left as variables, any earlier newly fixed gate with two inputs would itself be a descendant fixed gate; the first fixed gate has only one fixed operand. Thus from a raw input with two readers all its immediate readers are OR. Every first gate is an OR of two distinct inputs, each having exactly two readers. The single-reader contradiction above applies independently to either operand of that OR; a first AND would require both primary operands to have a single reader.

The 25-gate bound is still two gates below the explicit circuit. The structural conditions describe what any 25-gate witness must do.
