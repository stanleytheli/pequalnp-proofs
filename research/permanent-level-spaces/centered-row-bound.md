# A centered row bounds the dimension of a 5×5 permanent level space

**Theorem.** Let \(J\) be the all-ones matrix. Suppose a complex linear subspace \(L\) of 5×5 matrices satisfies \(\operatorname{per}(J+X)=120\) for all \(X\in L\) and contains every matrix supported in a specified row whose entries sum to zero. Then \(\dim L\le7\). Transposition gives the same conclusion for a centered column.

This is a paper result on the search problem L-gct-190. General 5×5 spaces without the specified row or column remain open here. The reduction to five constant cofactors and the initial Gram-rank and one-line observations were developed by the coordinating agent. The rank-one classification and the completion of the two-line case were developed by the reviewing agent. The proof uses elementary polynomial and linear algebra over the complex numbers.

## The five omitted-column conditions

Move the specified row to the bottom. Denote the upper 4×5 block by \(X'\) and its columns by \(x_1,\ldots,x_5\). Write \(K\) for the projected space. Expanding the permanent in the bottom row, translations by every centered bottom row show that the five 4×4 permanents obtained by omitting one column of \(J+X'\) agree on \(L\). Their common polynomial \(g\), multiplied by the sum of the translated bottom row, is identically 120. Units in the polynomial ring on \(L\) are constant, so \(g=24\) and the bottom row of \(X\) sums to zero. The projection kernel has dimension four. It suffices to prove \(\dim K\le3\).

The linear parts of the five identities show that each \(x_j\) lies in \(H=\{x\in\mathbb C^4:\sum_h x_h=0\}\). Indeed each omitted-column sum of all entries vanishes and hence each individual column sum vanishes. Use the complex bilinear form \(u\cdot v=\sum_hu_hv_h\), without conjugation. Its restriction to \(H\) is nondegenerate because \(H^\perp\) is the all-ones line and the all-ones vector has squared length four. Write \(S=\sum x_j\), \(Y_j=2x_j-S\) and \(Q=S\cdot S\) as a quadratic form on \(K\). The quadratic terms give \(\sum_{h<k,\ h,k\ne j}x_h\cdot x_k=0\) for each \(j\). Summing over the five deletions gives \(\sum_{h<k}x_h\cdot x_k=0\) and thus \(x_j\cdot(S-x_j)=0\). Consequently
\[
Y_j\cdot Y_j=Q,\qquad \sum_jY_j+3S=0.
\]

For \(d=3,4\), write \(M(u_1,\ldots,u_d)\) for the sum of the products of the entries of these vectors on distinct, ordered row indices. The homogeneous identity of degree \(d\) for each deletion says that the sum of \(M\) over all \(d\)-subsets of its four retained columns is zero. This follows by completing the other columns with all-ones entries, in \((4-d)!\) ways. For centered vectors, \(M(u,v,w)=2T(u,v,w)\), with \(T(u,v,w)=\sum_hu_hv_hw_h\), by inclusion–exclusion on row coincidences. If \(D\in K\) consists of \(v,-v\) in columns \(a,b\) and zero elsewhere, the coefficient of the square of the translation parameter in the cubic identity on \(X+tD\) gives
\[
 T(v,v,x_c)=0\qquad(c\notin\{a,b\},\ X\in K).
\]
Indeed deleting each of the three outside columns gives zero on the sum of the other two outside columns. The three pair sums are zero only if each summand is zero.

## Quadratic forms of rank zero or at least two

The six maps \(S,Y_1,\ldots,Y_5\) from \(K\) to \(H\) have the same Gram form \(Q\). If its rank is at least two, each image is nondegenerate. A proper degenerate plane in \(H\) has rank one, and the entire space is nondegenerate. The six maps therefore kill \(\operatorname{rad}Q\). Together they recover each \(x_j\), so \(\operatorname{rad}Q=0\) and \(\dim K=\operatorname{rank}Q\le3\).

When \(Q=0\), each of the six images is at most a fixed isotropic line. If there are \(m\) nonzero images spanning a total space of dimension \(r\), their one vector relation gives \(\dim K\le m-r\). In detail, represent each nonzero image by its scalar coefficient on a fixed generator. The map from these \(m\) scalar coordinates to \(H\) taking the indicated linear combination has rank \(r\), and the space embeds in its kernel. Distinct isotropic lines in \(H\) have nonzero pairing, and any three distinct ones span \(H\). For the latter fact, the projective conic of a nondegenerate ternary quadratic meets a projective line in at most two points. Thus \(\dim K\ge4\) permits at most two distinct isotropic lines.

If there is just one line \(\mathbb Cv\), all columns are \(u_jv\) for linear forms \(u_j\) on \(K\). The nonzero \(v\) has \(e_1(v)=e_2(v)=0\), where \(e_k\) is the elementary symmetric polynomial, so \(e_3(v)\) or \(e_4(v)\) is nonzero. In the latter case each fourfold product of the \(u_j\) vanishes identically, so at most three forms are nonzero. In the former case every \(e_3(u_{\ne j})\) vanishes. Summation gives \(e_3(u)=0\), hence every nonzero \(u_j\) satisfies \(u_j^2-e_1(u)u_j+e_2(u)=0\) in the fraction field of the parameter ring. There are at most two distinct nonzero forms. Either case bounds the dimension by three.

For two lines, \(S=0\) gives dimension at most \(5-2=3\). Otherwise write \(S=2cv\) and partition the five column positions into \(I,B\), according as \(Y_j\) lies on \(\mathbb Cv,\mathbb Cw\). Assign a zero map to \(I\). Then
\[
 x_i=a_i v\quad(i\in I),\qquad x_j=cv+b_jw\quad(j\in B),\qquad
 \sum_Ia_i=(2-|B|)c,\quad \sum_Bb_j=0.
\]
Both sets are nonempty. The presence of \(w\) forces \(B\ne\varnothing\), and \(I=\varnothing\) would give \(2cv=5cv+\sum b_jw\), impossible. These independent equations give a four-dimensional parameter space. If \(\dim K\ge4\), the entire parameter space occurs. Choose \(c=1,b=0,a_i=1\) except for one \(a_i=-2\). Omitting this last position leaves four copies of \(v\), giving \(24\prod_h(1+tv_h)=24\) for all \(t\). This forces \(v=0\), a contradiction.

## A rank-one Gram form

Write \(Q=\ell^2\), with \(\ell\ne0\), and put \(F=\ker\ell\). This normalization uses a square root of a nonzero complex scalar. Suppose \(\dim K\ge4\), so \(\dim F\ge3\). The six maps on \(F\) have images on fixed isotropic lines, including the possibility of the zero map. Since the maps determine all the original columns, they cannot all vanish on \(F\).

If the images span one line \(\mathbb Cv\), the one-line argument above gives \(\dim F=3\), \(e_3(v)=0\), \(e_4(v)\ne0\), and \(F\) contains independent multiples of \(v\) in exactly three column positions. Scaling and permuting coordinates, \(v=(1,i,-1,-i)\), by the monic polynomial with its coordinates as roots. For every column \(c\), two of those three positions avoid \(c\), so the supported pair-difference result puts all \(x_c\) for all \(X\in K\) in \(P=H\cap(v^2)^\perp\), where powers of vectors are coordinatewise. This plane is \(\operatorname{span}(v,v^3)\), with \(v\cdot v^3=4\), hence nondegenerate. A map with Gram rank one into a nondegenerate plane has one-dimensional nonisotropic image. Such a map kills \(F\), the radical of its Gram form. Applying this to \(S\) and all \(Y_j\) is a contradiction.

### Three-dimensional span of the isotropic lines

Apply the same \(m-r\) bound to the images on \(F\). Since \(m-r\ge3\) and \(r=3\), all six images on \(F\) are nonzero and \(F\) is the entire three-dimensional kernel of the relation among these six lines. In particular, zero maps cannot occur in this case. Denote the respective lines of \(S,Y_j\) by \(\mathbb Cv_0,\mathbb Cv_j\). If any \(v_j\) is proportional to \(v_0\), set \(S\ne0,Y_j=-3S\) and all the other \(Y\)'s to zero. Omitting \(j\) gives four equal nonzero columns, impossible as above. Thus \(v_0\) differs from every \(v_j\). At least three distinct \(Y\)-lines must occur, since the span of any two distinct lines excludes the third \(v_0\), whose coefficient occurs nontrivially in the relation.

If all five \(v_j\) have distinct lines, take \(S=0\) and use the unique relation supported on any four of them. It has all four coefficients nonzero. Of the five columns one is zero. On deleting any one of the four active columns the cubic condition therefore forces \(T=0\) on the triple of remaining distinct directions. This works for every triple. For fixed \(i,k\) the three other \(v_j\) span \(H\), whence \(v_iv_k\) (coordinatewise product) is a constant vector. The constant is nonzero since \(v_i\cdot v_k\ne0\). For a given \(i\), this forces every \(v_k,\ k\ne i\), to lie on the reciprocal of \(v_i\)'s line, a contradiction.

Otherwise two positions \(a,b\) share a line \(\mathbb Cv\). Their supported pair difference belongs to \(F\). For all \(d\ne a,b\), we have \(T(v,v,x_d)=0\). Choose such a \(d\) leaving at least three distinct \(Y\)-lines among the four other \(Y\)'s. This holds for any \(d\) if there are four distinct \(Y\)-lines. For multiplicities \((3,1,1)\) take the third copy, and for \((2,2,1)\) take a member of the other doublet. The other four lines span \(H\), so the coefficients of \(S,Y_d\) in the full relation space can be chosen independently. The identity \(2x_d=S+Y_d\) now gives \(T(v,v,v_0)=0\). In turn each \(Y_d\) occurs nontrivially and gives \(T(v,v,v_d)=0\) for every \(d\ne a,b\). Those directions together with \(v_0\) include at least three distinct lines, so \(T(v,v,-)\) vanishes on all \(H\). Thus \(v^2\) is constant, and \(\sum v_h^2=0\) shows this constant is zero. This contradicts \(v\ne0\).

### Two-dimensional span of the isotropic lines

Only two distinct lines \(\mathbb Cv,\mathbb Cw\) can occur. If \(S|_F=0\), then \(\dim F\ge3\) implies all five column positions are active and the coefficients vary subject only to their separate zero sums in each line. Each group needs two active positions, so the group sizes are three and two. The three positions on one line \(\mathbb Cv\) supply a supported pair difference avoiding any given column, again putting all columns of \(K\) in \(P=H\cap(v^2)^\perp\). This is a proper plane since \(v^2\) cannot be constant for an isotropic nonzero \(v\). It contains both \(v\) and \(w\), hence is nondegenerate. The rank-one Gram condition again forces all six maps to kill \(F\).

Suppose now \(S|_F\ne0\) and let \(v\) be its line. The preceding two-line parameterization applies to \(F\), with \(b_j\) nonzero linear forms on precisely the positions in \(B\). It permits at most four dimensions, and the rank-zero result excludes dimension four for this level subspace. Thus \(F\) is a hyperplane in the displayed four-dimensional parameter space. Any zero \(Y_i|_F\) is represented by the permitted special condition \(a_i=c\) on \(F\). We have \(|B|=2,3,4\), because nonzero \(b_j\)'s sum to zero. Write \(M_{hk}\) for \(M\) on \(h\) copies of \(v\) and \(k\) copies of \(w\).

We will use the following fixed moments. If \(M_{30}=0\), then \(e_1(v)=e_2(v)=e_3(v)=0\), so \(v\) is the fourth-root vector above after scaling and permutation. If also \(M_{21}=0\), then \(w\in P=\operatorname{span}(v,v^3)\). The only isotropic lines in this plane are \(\mathbb Cv,\mathbb Cv^3\), so \(w\) is proportional to \(v^3\). Normalize \(w=v^3\). The partition expansion for four centered column vectors gives \(M_{22}=2(v\cdot w)^2-6\sum_hv_h^2w_h^2=8\). Indeed the three pairings have coefficients \(+1\), the block of four has coefficient \(-6\), and all partitions with singleton blocks vanish. The \(v\cdot v,w\cdot w\) term vanishes. Hence \(M_{30}=M_{21}=M_{22}=0\) is impossible.

**Two \(w\)-positions.** The columns are \(av,bv,dv,cv+tw,cv-tw\) with \(a+b+d=0\), \(c,t\ne0\) as forms. Averaging the two identities obtained by omitting one of the last two columns yields
\[
 M_{30}[abd+c e_2(a,b,d)]=0,\qquad M_{40}c\,abd=0.
\]
If \((a,b,c)\) fills three dimensions this gives \(M_{30}=M_{40}=0\), impossible. Otherwise it fills a plane and \(t\) is independent. Suppose \(M_{40}=0\), so \(M_{30}\ne0\). If \((a,b)\) fills two dimensions then \(c\) is linear in them, which would make \(e_2(a,b,-a-b)\) divide \(ab(-a-b)\). Its two root directions are cube-root directions, on which the latter product is nonzero. If \((a,b)\) fills one dimension then \(c\) is independent. Both \(e_2\) and \(abd\) must vanish on a nonzero centered triple, which is impossible. Therefore \(M_{40}\ne0\), so one of \(a,b,d\) vanishes. The other two are \(x,-x\) with \(x,c,t\) independent. The mean cubic now gives \(M_{30}=0\). The difference of the same cubic deletions gives \(t e_2(a,b,d)M_{21}=0\) and hence \(M_{21}=0\). Set \(c=0\) and omit the identically zero column. The quartic is a nonzero multiple of \(M_{22}\), contradicting its value above.

**Three \(w\)-positions.** The columns are \(av,dv,cv+b_1w,cv+b_2w,cv+b_3w\) with \(a+d=-c,\ \sum b_j=0\). If \(b=0,c\ne0\) occurs, omit \(a\) or \(d\). At least one quartic coefficient \(a c^3,d c^3\) is nonzero, and at least one cubic coefficient \(c^2(c+3a),c^2(c+3d)\) is nonzero. This forces \(M_{40}=M_{30}=0\). Thus \(c\) factors through the projection to \(b\). Dimension three now requires the full centered two-plane of \(b\)'s and an independent \(a-d\) coordinate. Subtract the identities omitting two of the three \(w\)-positions and cancel their nonzero difference \(b_i-b_j\). With \(k\) the third index, the cubic and quartic give respectively
\[
 M_{21}(ad-c^2)-M_{12}cb_k=0,\qquad ad(M_{31}c+M_{22}b_k)=0.
\]
Comparing \(k\)'s shows \(M_{12}=M_{22}=0\). The forms \(ad\) and \(ad-c^2\) cannot vanish identically because \(a-d\) is free. Hence \(M_{21}=0\). In the cubic omitting a \(w\)-position, the remaining pure term is \(M_{30}c(2ad-c^2)\), giving \(M_{30}=0\). This contradicts the fixed moments.

**Four \(w\)-positions.** The columns are \(-2cv\) and \(cv+b_jw,\ j=1,\ldots,4\), with \(\sum b_j=0\). If \(b=0,c\ne0\) were allowed, omitting the first column would give four equal nonzero columns. Thus \(F\) is a graph \(c=L(b)\) over the entire centered three-plane of \(b\)'s, with \(L\ne0\). Subtracting two \(w\)-deletions and cancelling \(b_i-b_j\) gives, with \(k,l\) the other two indices,
\[
 -3M_{21}c^2-M_{12}c(b_k+b_l)+M_{03}b_kb_l=0.
\]
Comparing \((k,l)\) and \((k,h)\) gives \(M_{03}b_k=M_{12}c\) for every \(k\). Since the \(b\)'s span three dimensions, \(M_{03}=M_{12}=M_{21}=0\). The cubic omitting the first column gives \(M_{30}=0\). The corresponding quartic difference, divided by \(-2c(b_i-b_j)\), is
\[
 M_{31}c^2+M_{22}c(b_k+b_l)+M_{13}b_kb_l=0.
\]
The same comparison gives \(M_{22}=0\), the final contradiction.

This excludes \(\dim K\ge4\) in every Gram-rank case and proves the bound.
