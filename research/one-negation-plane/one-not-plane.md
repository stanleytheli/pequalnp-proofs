# A one-NOT lower bound for all line ORs of a projective plane

Let a finite projective plane have order \(q\ge2\) and \(M=q^2+q+1\) points and lines. Give its points Boolean inputs. For every line, the circuit must output the OR of the \(q+1\) inputs on that line. Gates are AND, OR or NOT, with fan-in at most two and arbitrary fan-out. Positions that are raw inputs can be outputs. Count all gate positions, including the NOT.

**Theorem.** A circuit with at most one NOT that computes all \(M\) line outputs has at least

\[
 \begin{cases}
 (q^3+q^2+3q+4)/2,&q\text{ even},\\[2pt]
 (q^3+2q^2+2q+3)/2,&q\text{ odd}.
 \end{cases}
\]

For the 57 lines of the plane of order seven the bound is **229 gates**. The project's L996 records a conditional 175-gate statement for its cyclic representation. The present lower bound follows from direct gate counts. [L996's public statement](https://data.pequalnp.com/data/lemma/L-meta-996.feeb43f2ce11.json)

**Proof.** If the circuit has a NOT, let \(h\) be the monotone function on its input wire. When \(h\) is constant, replace the NOT by its constant value and retain a monotone circuit of the same size. For a monotone circuit, the private-gate count on the empty base gives \(q\) distinct positions per line, for a lower bound of \(qM\). Thus assume \(h\) is nonconstant. Choose a set \(Y\) of minimum cardinality on which it is true and write \(k=|Y|\ge1\), \(N\) for the gate count, and \(H\) for the number of lines meeting \(Y\).

The reserved-position and the light-window arguments of `window-partial.md` give at least \(k\) reserved positions and at least \(\min(k,q+1)-1\) additional private positions per line. The heavy-window argument gives \(q\) private positions per line disjoint from \(Y\). All its private positions are false at \(Y\). Every meeting line supplies its own final output gate, true at \(Y\), independently of \(k\). This is a real gate because its singleton support has \(q+1\) points. It cannot be any reserved gate since the reserved prefix gates have empty singleton support and the NOT is false at \(Y\). Distinct line outputs need different final wires. Therefore

\[
 N\ge k+M(\min(k,q+1)-1),\qquad
 N\ge k+q(M-H)+H.
\]

The first point of \(Y\) hits \(q+1\) lines. For each further point at least one incident line has already been counted, namely its line to the first point. Thus \(H\le1+qk\), and the second bound gives \(N\ge k+qM-(q-1)(1+qk)\).

The first bound increases with \(k\). The latter affine bound decreases with \(k\) for \(q\ge2\). Before saturation of the first bound, the crossing is at

\[
 k_* = (q^3+2q^2+q+2)/(2q^2+1)
     = q/2+1+(q/2+1)/(2q^2+1).
\]

Write \(j=\lfloor q/2\rfloor+1\). Then \(j<k_*<j+1\) and \(j+1\le q+1\). The minimum of the maximum over integral \(k\) is the lesser of the second bound at \(j\) and the first at \(j+1\). For even \(q\), the first value is \((q^3+q^2+3q+4)/2\), and the second exceeds it by \(q^2+q/2+1\). For odd \(q\), those values are \((q^3+2q^2+2q+3)/2\) and that value plus \((q+1)/2\). The bounds in the theorem follow. ∎

At \(q=7\), the two integer thresholds bracketing the crossing are four and five. For \(k\le4\) the heavy estimate gives at least \(4+7\cdot28+29=229\). For \(k\ge5\) the light estimate gives at least \(5+57\cdot4=233\). The cyclic model used by L996 has points \(\mathbb Z/57\mathbb Z\) and translates of \(\{0,1,3,13,32,36,43,52\}\) as lines.
