# A complex seven-plane with full row normals requires a three-value pair

Let \(P(A)=\sum_{\sigma:[4]\hookrightarrow[5]}\prod_i A_{i,\sigma(i)}\) and let \(J\) be the \(4\times5\) all-ones matrix. Suppose \(L\) is a seven-dimensional complex linear space with \(P(J+X)=120\) for all \(X\in L\). Assume that every nonzero member has at least three active rows, that each row projection has dimension four, and that its normal covector has full coordinate support. Then some pair of normalized row normals has **three distinct coordinate ratios**, of the form \(R,\mathrm i R,-\mathrm i R\). In particular this case cannot occur for a seven-plane defined over the reals.

## The hollow symmetric matrices

By the pair phase proposition in [the main proof](full-row-obstruction.md#the-pair-constraints), an alternative to the three-value pair is that every pair has two opposite ratio values. Suppose the latter. There is then a sign matrix \(E\in\{\pm1\}^{4\times5}\) and nonzero \(w_j,s_i\) with normalized normals \(w^{(i)}_j=E_{ij}w_j/s_i\), where \(s_i=\sum_j E_{ij}w_j\). The pair's cross relation \(w^{(i)}\cdot X_k=(s_k/s_i)^2w^{(k)}\cdot X_i\) follows from the weighted group sums derived there. In the coordinates \(Z_{ij}=w_j X_{ij}/s_i\), the space \(L\) lies in
\[
 D=\{Z:ZE^t\text{ is symmetric with zero diagonal}\}.
\]
Write \(D_X\) in the original coordinates. No two rows of \(E\) are proportional. Hence \(E\) has rank three or four, since projection of sign vectors in any rank-two row space onto two independent coordinates is injective and gives only two proportional sign classes. In either case \(\dim D=10\). At rank four the map \(Z\mapsto ZE^t\) is onto, with kernel dimension four, and the hollow symmetric matrices have dimension six. At rank three the kernel has dimension eight. Writing \(E=UV\) with \(U\) a \(4\times3\) matrix of rank three, symmetric matrices in the image are exactly \(UHU^t\) for symmetric \(3\times3\) matrices \(H\). Requiring zero diagonal gives four independent conditions on \(H\). In a basis formed from three rows of \(U\), the fourth has at least two nonzero coordinates and thus contributes a nonzero off-diagonal coefficient in addition to the three coordinate squares.

Put \(C=\{c:(w_j c_j)_j\in\ker E\}\). Then \(P_C=\mathbb C^4\otimes C\subset D_X\). For every nonzero \(c\in C\), define \(F(c)=\{h:h\otimes c\in L\}\). Its dimension \(f\) satisfies \(1\le f\le2\). The lower bound follows from \(\dim L=7,\dim D_X=10\) by intersecting with the four-space \(P_c=\mathbb C^4\otimes\mathbb Cc\). At dimension three, \(F(c)\) would intersect a coordinate two-plane and give a matrix with at most two active rows.

For each degree \(1\le d\le4\), the degree-\(d\) part \(P_d\) of \(P(J+X)\) is a positive multiple of the sum over the size-\(d\) matchings on the row and column indices. In particular
\[
 P_d(h\otimes c)=k_d e_d(h)e_d(c),\qquad
 (\mathrm d P_d)_{h\otimes c}(Y)
 =\frac{k_d}{d}\sum_{ij} e_{d-1}(h_{\widehat i})e_{d-1}(c_{\widehat j})Y_{ij}
\]
for a nonzero normalization \(k_d\) in each degree. Indeed \(k_d\) includes the \(d!\) assignments for a fixed pair of \(d\)-element row and column sets in the first identity. In the second identity the fixed position \((i,j)\) leaves \((d-1)!\) assignments. Only vanishing is used below. Every such differential annihilates \(L\) when \(h\in F(c)\). It also annihilates \(P_c\) whenever \(e_d(c)=0\), by restriction of the first formula. On \(Z\) it is the simple covector with row entries \(s_i e_{d-1}(h_{\widehat i})\) and column entries \(e_{d-1}(c_{\widehat j})/w_j\), up to the scalar.

## Rank three

Now \(\dim C=2\), so \(K=L\cap P_C\) has dimension at least five. The quadratic form on \(P_C\) polarizes to the tensor of the nonsingular four-row form \((\sum h_i)(\sum h'_i)-\sum h_i h'_i\) and the restriction to \(C\) of \(B(c,c')=(\sum c_j)(\sum c'_j)-\sum c_jc'_j\). If \(B|_C\) has rank two the resulting quadratic is nonsingular on an eight-space and has maximal isotropic dimension four. If it has rank one with radical \(\mathbb Cc_0\), the image of \(K\) in \(P_C/P_{c_0}\) is totally isotropic in a nonsingular four-space, so has dimension at most two. Then \(K\cap P_{c_0}\) has dimension at least three, contrary to the bound on \(F(c_0)\). Thus \(B|_C\) would vanish identically. But the rank-three column space of \(E\) projects injectively onto three coordinates, so contains at most four sign columns up to proportionality. Among the five columns there is a proportional pair. It gives a \(c\in C\) with just two nonzero coordinates, for which \(B(c,c)=2c_ic_j\ne0\).

## Rank four

Fix a generator \(c\ne0\) of \(C\). The kernel vector cannot have support one, since no column of \(E\) vanishes. A covector \(a\otimes d\) with \(d\ne0\) and at least three active row coefficients cannot vanish on \(D\). In fact vanishing on the kernel of \(Z\mapsto ZE^t\) first requires \(d=E^tv\). Against all hollow symmetric matrices one must then have \(a_iv_k+a_kv_i=0\) for \(i\ne k\). Three active \(a_i\) force the corresponding three ratios \(v_i/a_i\) to be zero, then all \(v_i\) to be zero.

More generally for a fixed nonzero \(d\), the map \(a\mapsto(a\otimes d)|_D\) has kernel of dimension at most one. This is immediate for \(d\notin\operatorname{im}E^t\). For \(d=E^tv\), the off-diagonal equations make \(a=0\) if \(v\) has at least three active coordinates, and for one or two active coordinates of \(v\) the solutions form a line on the same support. The annihilator of \(L+P_c\) inside \(D_X^*\) has dimension exactly \(f-1\).

### The column has nonzero sum

All \(h\in F(c)\) satisfy \(e_1(h)=0\). If \(e_2(c)=0\), use the quadratic differentials, which annihilate \(L+P_c\). Their row vectors \((-s_i h_i)_i\) give an \(f\)-space with at least three active coordinates in each nonzero member. The fixed column vector is nonzero, as \(\sum c_j-c_i=0\) for every \(i\) would force \(c=0\). By the simple-covector result these differentials give \(f\) independent forms, impossible in a space of dimension \(f-1\).

Suppose \(e_2(c)\ne0\). Then all of \(F(c)\) is centered and totally \(e_2\)-isotropic. On the centered three-dimensional row space \(e_2(h)=-\sum h_i^2/2\) is nonsingular, so \(f=1\), and \(L+P_c=D_X\). Pick \(h\ne0\) in \(F(c)\). If \(h\) has three active entries, then \(e_3(h)\ne0\), so \(e_3(c)=0\). The cubic differential has row entries proportional, after row scaling, to \(h_i^2\), by \(e_1(h)=e_2(h)=0\). Its column vector is nonzero. Indeed, if all \(e_2(c_{\widehat j})\) vanished, each \(c_j\) would solve \(x^2-e_1(c)x+e_2(c)=0\). If there were only one coordinate value, the assumption \(e_2(c_{\widehat j})=0\) would make it zero. With two distinct values \(a,b\) of multiplicities \(k,5-k\), their sum is \(e_1(c)\) and product \(e_2(c)\). The identities for sums and squared sums give
\((k-1)a+(4-k)b=(k-1)a^2+(4-k)b^2=0\), forcing at most one nonzero coordinate of \(c\). This contradicts its support bound. The cubic differential thus violates the simple-covector result.

If \(h\) has all four entries active, then \(e_4(c)=0\). If \(c\) has at least three active coordinates, the quartic column vector \((e_3(c_{\widehat j}))_j\) is nonzero. A support of three gives a nonzero entry at an omitted position, a support of four is incompatible with \(e_4(c)=0\), and at full support \(e_3(c_{\widehat j})=-e_5(c)/c_j^2\) by \(e_4(c)=0\). All four quartic row coefficients are nonzero, giving the same contradiction. With a two-position support of \(c\), the cubic differential applies because \(e_3(c)=0\) and all four row entries \(h_i^2\) are nonzero.

### The column is centered

If \(f=1\) then \(L+P_c=D_X\), on which total entry sum vanishes, since the sum vanishes on \(L\) by the linear level equation and on \(P_c\) by centeredness. This would give the prohibited simple covector \((s_i)_i\otimes(1/w_j)_j\). Thus \(f=2\). Write \(\ell_i\) for the four coordinate linear forms on the plane \(F(c)\). They are nonzero and pairwise independent because any zero or proportional pair would give a nonzero \(h\) with at most two active rows. Taking a generic \(h\), and then \(h\) at the kernel of one coordinate, gives \(e_4(c)=e_3(c)=0\), respectively. Thus \(c\) has either two or five active entries.

At full support its quartic column differential is nonzero as above. The four cubic row factors \(\prod_{k\ne i}\ell_k\) are linearly independent by evaluating a proposed relation at the zero of each \(\ell_i\). Hence the row vectors as \(h\) varies span all four dimensions, and their restricted differentials span at least three. All must annihilate \(L+P_c\), whose annihilator has dimension one.

Finally take the two active entries of \(c\), which are opposite. Now \(e_2(c)\ne0\), hence \(e_2(h)=0\) throughout \(F(c)\). The cubic column factor is nonzero at positions outside the support of \(c\). Its row entries up to sign and row scalings are the binary quadratics
\[
 q_i=\ell_i(\mu-\ell_i),\qquad \mu=\ell_1+\ell_2+\ell_3+\ell_4.
\]
Every two of these quadratics are linearly independent. To see that none vanishes, suppose \(\mu=\ell_i\). Then the three other forms have zero sum and zero sum of squares by \(e_2(h)=0\). Their joint image would be a linear subspace of a nonsingular centered quadratic plane on which the form vanishes, of dimension at most one, contrary to their pairwise independence. If nonzero \(q_i,q_j\) were proportional, coprimality of the nonproportional \(\ell_i,\ell_j\) forces \(\mu-\ell_i\) proportional to \(\ell_j\) and \(\mu-\ell_j\) proportional to \(\ell_i\). Hence \(\mu=\ell_i+\ell_j\), making the other two forms opposite, again impossible.

These cubic differentials give at least two independent forms on \(D\). To see this, denote their fixed nonzero column vector by \(d\). If \(d\notin\operatorname{im}E^t\), or \(d=E^tv\) with at least three active coordinates of \(v\), the row restriction map is injective. Otherwise choose two row indices outside the one- or two-point support of \(v\). Comparing their off-diagonal entries against a fixed active coordinate of \(v\) directly exhibits the two independent quadratics just proved. This contradicts the one-dimensional annihilator of \(L+P_c\). Both ranks of \(E\) are excluded, proving the claim.
