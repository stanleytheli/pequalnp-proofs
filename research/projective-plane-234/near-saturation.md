# An unconditional 234-gate bound for the 57 projective-plane line ORs

Every fan-in-two AND/OR/NOT circuit with at most one NOT computing the 57 line ORs of the order-seven projective plane has at least **234 gates**. The complete physical-circuit proof is kernel-checked in `Plane234.lean`, theorem `PEqualNP.Outside.Window997.plane57_one_not_234`. The following argument traces the quantities used in that proof.

Assume \(N\le233\). A monotone circuit needs 399 gates. For a genuine NOT with nonconstant monotone input \(h\), choose a minimum-weight true assignment \(Y\) and write \(k=|Y|\). For constant \(h\) the monotone bound already applies. Let \(d\) be the number of lines avoiding \(Y\). Each line contains eight points and distinct lines meet once.

The two checked bounds give \(N\ge k+7d+(57-d)\) and \(N\ge k+57(\min(k,8)-1)\). In addition one arbitrary line may always obtain its full seven units in the latter count. For \(k\ge5\) this gives \(N\ge236\); for \(k\le3\) the heavy bound and \(d\ge56-7k\) give \(N\ge270\). Thus \(k=4\), and the heavy bound forces \(d=28\). Write \(s=N-229\le4\). The number 229 comprises four reserved slots, seven slots for each of 28 disjoint lines, and one slot for each of 29 meeting outputs.

## A reader of the NOT saves a slot in the false pin

The NOT itself cannot be an output because it is true at empty. If no later gate reads it, replacing the NOT by false leaves all outputs unchanged and the 399 bound applies. Otherwise take any later gate that reads the NOT output. It cannot be an original line output. An OR reader is true on empty, where the NOT is true. An AND reader is false on every \(Y\cup\{p\}\), where the NOT is false, whereas for each line some such input makes that line output true. This also rules out unary readers and gates reading the NOT twice.

Form the false pin by replacing the NOT at its physical slot with a zero-input OR. The selected later reader becomes transparent. Its value is identically false or is carried by the one other earlier operand. An absent, forward or invalid operand contributes false under the project's rules. The proof keeps the original array and wire addresses. Its private cut skips this physical reader at zero cost, and the reader cannot equal a meeting output. Thus the count can reserve the reader and the NOT separately. Equivalently the remaining charges have an effective budget of \(N-1\).

The false-pinned circuit is globally sound for each output line: a true output implies the input meets the line. It computes the original outputs above \(Y\). Each line disjoint from \(Y\) requires seven private gates globally sound for that line and firing on at least two of the inputs \(Y\cup\{p\}\). Choose seven for each such line. These 196 positions are distinct and false at \(Y\), and meeting output positions are true at \(Y\). The 29 meeting output positions remain distinct, since the selected reader cannot be an output. The pin itself and at least three dark prefix gates, true at \(Y\) with empty singleton support, lie outside all those positions. Thus in the effective budget at most \(s-1\le3\) slots are left after these specified allocations.

No meeting output can occur before the NOT. If its line is \(T\), this prefix already computes its full OR on every input. By the monotone singleton cut in that prefix at least seven distinct prefix gates have singleton supports of size at least two contained in \(T\). None can be assigned to a disjoint line, since prior to the NOT singleton evaluations agree with the false pin and all of a charged gate’s singleton witnesses lie in its own line. No dark gate supplies such a witness. Another meeting output in the prefix has its own full line as singleton support. Thus at least six new slots in addition to the output of \(T\) would be required, exceeding the available three.

## A sparse certificate for switching off the NOT input

Treat the previously chosen heavy private slots before the NOT as new input wires (stopping the backward computation at them). Every such input is false on all subsets of \(Y\). It is globally sound for its assigned heavy line, so removing that full line suffices to keep the input false. The remaining ordinary prefix has at most \(3+(s-1)\) gates, since its only previously allocated gates are dark and no meeting output precedes the NOT.

At \(Y\), trace a true certificate for \(h\). For true AND gates use all inputs, and for true OR gates choose one true input. Expand each physical slot at most once in reverse order. No heavy input can occur among the true leaves, and every raw leaf must be in \(Y\). There must be at least four such raw points, since together they already force \(h\) true, and all smaller assignments make \(h\) false. Each nonbranching gate does not increase the frontier size. Hence at least three ordinary binary AND gates are present, leaving at most \(s-1\) ordinary OR gates.

Fix any \(y\in Y\). At \(Y\setminus\{y\}\), \(h\) is false. Trace a false certificate in the same truncated prefix. A false AND needs only one false input; a false OR uses all inputs. The frontier now has at most \(1+(s-1)\) atoms. It includes the raw variable \(y\), since restoring that point makes \(h\) true while leaving every heavy atom false. Each other frontier atom is a raw outside point, a heavy input made false by avoiding its whole assigned row, or a permanently false missing wire. Thus deleting the point \(y\) and at most three more objects, each a point or a disjoint line, gives a point set \(P\) on which \(h(P)=0\). More generally `sparse_certificate997` proves this claim with at most \(|G|+1-|Y|\) extra objects for an arbitrary family of exceptional row-sound inputs and \(|G|\) ordinary prefix gates.

## Charging the surviving points

For any h-false \(P\), every line \(L\) can simultaneously charge \(\max(3,|L\cap P|-1)\) slots, in addition to the four reserves. Furthermore, one selected line \(R\) can replace its charge by seven. Use the checked chain theorem: the rows choose the better of \(P\) and the full domain, and \(R\) uses the intermediate domain \(P\cup R\). All points there outside \(R\) lie in \(P\), ensuring the required falsity on its local tests.

Let \(D=P^c\). Each point appears on eight lines, so before applying any floor the row charges sum to \(399-8|D|\). If at most two deleted objects are lines, then \(|D|\le17\): two lines use at most fifteen points, leaving at most two single points. The charge excluding the reserves is already at least 263. If three objects are lines, those three cover at most 22 points, since the first has eight points and every further line adds at most seven. Together with \(y\), \(|D|\le23\). Each of the three entirely removed lines has raw charge \(-1\) and receives at least three through its light count. Choosing one of them for the full seven units adds four more. Thus
\[
 N\ge4+399-8\cdot23+3\cdot4+4=235.
\]
Both cases contradict \(N\le233\), proving the theorem. Without setting aside the NOT reader, the same reasoning already excludes \(N\le232\).

The incidence arguments depend only on the projective-plane axioms. The checked 57-point model uses the translates of \(\{0,1,3,13,32,36,43,52\}\) in \(\mathbb Z/57\mathbb Z\). No claim of optimality is made.
