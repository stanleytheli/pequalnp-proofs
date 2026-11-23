# A dimension bound for additive directions in square permanent level spaces

**Theorem.** Let \(n\ge4\), let \(J\) be the all-ones \(n\times n\) matrix, and let \(L\) be a complex linear space on which \(\operatorname{per}(J+X)=n!\). Let \(d\) be the dimension of the subspace of additive matrices \(X_{ij}=u_i+v_j\) in \(L\). There is an integer \(r\ge\max(0,2d-n+1)\) such that
\[
  2d+1+\binom{r+1}{2}\le 2n.
\]
The inequality is strict if \(r<d\). In particular every 5×5 permanent level space has at most two independent additive directions. Any eight-dimensional example in the 5×5 search problem would have at least six independent doubly centered components.

## Moment identities

Total entry sum is zero by the first derivative of the permanent. Each additive matrix in \(L\) therefore has unique centered offsets \(u,v\in H_n=\{z\in\mathbb C^n:\sum_i z_i=0\}\), given by its row and column means. Write \(W\subset\mathbb C^{2n}\) for the resulting \(d\)-dimensional space of stacked vectors \(w=(u,v)\). Both projections \(W\to H_n\) are injective, since a pure row or column offset would satisfy \(\prod_i(1+t u_i)=1\) for all \(t\), forcing all its coordinates to vanish.

Define the symmetric bilinear form \(Q(w,w')=\sum_i u_i u'_i\). The rank \(r\) of this form is at least \(2d-n+1\), since its radical in the row projection belongs to the orthogonal complement of a \(d\)-space in the nondegenerate \((n-1)\)-space \(H_n\).

For an additive matrix the normalized translated permanent is
\[
  \sum_{j=0}^n \binom nj^{-1}e_{n-j}(\mathbf1+u)e_j(v).
\]
To see this, select the \(j\) rows drawing their factor from \(v\), assign them to distinct columns, then count completions in the remaining square. The degree-two and degree-three identities after centering are \(e_2(u)+e_2(v)=0\) and \(e_3(u)+e_3(v)=0\). The fourth is
\[
 e_4(u)+e_4(v)+\frac{\binom{n-2}{2}}{\binom n2}e_2(u)e_2(v)=0.
\]
Using Newton's identities gives the joint power sums of the \(2n\) coordinates:
\[
 \sum_i w_i^2=\sum_i w_i^3=0,\qquad
 \sum_i w_i^4=\alpha Q(w,w)^2,\qquad
 \alpha=1-\frac{\binom{n-2}{2}}{\binom n2}\ne0.
\]
For \(n=5\), \(\alpha=7/10\).

## The evaluation space and its radical

Use the complex bilinear dot product on \(\mathbb C^{2n}\). For \(x,y\in W\), write \(x y\) for their coordinatewise product. Let \(B\) be the span of all such products, and let \(e=\mathbf1\) in \(\mathbb C^{2n}\). Polarization of the zero second and third moments gives \(W\perp W,\ W\perp B,\ e\perp B\). Also \(e\perp W\) and \(e\cdot e=2n\ne0\). Thus \(W+B+\mathbb Ce\) is contained in \(W^\perp\).

The dot product on \(B\) has rank \(\binom{r+1}{2}\). Indeed its pullback to \(\operatorname{Sym}^2 W\), under the surjection \(xy\mapsto x y\), is the polarized fourth moment
\[
 \frac{\alpha}{3}\{Q(x,y)Q(z,t)+Q(x,z)Q(y,t)+Q(x,t)Q(y,z)\}.
\]
A symmetric square with one factor in the radical of \(Q\) pairs to zero. On the quotient by that radical, choose an orthonormal basis over \(\mathbb C\). Off-diagonal basis products pair nontrivially only with themselves, and the diagonal products have Gram matrix proportional to \(2I+\mathbf1\mathbf1^\mathsf{T}\). Both blocks are nondegenerate, since \(2\) and \(r+2\) are nonzero. This proves the rank claim, including \(r=0\).

Consequently \(B+\mathbb C e\) contains a nondegenerate subspace of dimension \(1+\binom{r+1}{2}\). It is orthogonal to \(W\), hence intersects the isotropic \(W\) trivially. Since \(\dim W^\perp=2n-d\), the theorem's inequality follows.

If equality holds, \(W^\perp=W+B+\mathbb C e\). Suppose \(r<d\) and take a nonzero \(a\in\operatorname{rad}Q\). For every \(w\in W\), the product \(a w\) is orthogonal to \(W,e\) by the zero moments, and to \(B\) by the polarized fourth moment. Hence \(a w\in(W^\perp)^\perp=W\). The diagonal map multiplying by the coordinates of \(a\) preserves \(W\). Choose a nonzero coordinate value \(\lambda\) of \(a\). Polynomial interpolation gives its spectral projection, which also preserves \(W\). Applied to \(a\) it yields \(\lambda\) times the indicator of the nonempty set of coordinates where \(a_i=\lambda\). This indicator cannot belong to \(W\), since every vector in \(W\) has total coordinate sum zero. Thus equality requires \(r=d\).

For \(n=5\), if the additive part had dimension at least three, take a three-dimensional subspace. It would have \(r\ge2\). The inequality forces \(r=2\) and equality, contradicting \(r<3\). The kernel of double centering is the space of additive matrices, giving the stated consequence by rank-nullity.
