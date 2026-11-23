# A fourth-moment bound for additive directions in rectangular permanent level spaces

**Theorem.** Suppose \(4\le p\le q\) and a complex linear space \(L\) of \(p\times q\) matrices has translated injective permanent \(P(J+X)=q!/(q-p)!\) for all \(X\in L\). Let \(d\) be the dimension of its subspace of additive matrices \(X_{ij}=u_i+v_j\). Put \(t=\max(0,2d-q+1)\). Then
\[
  \frac{t(t+3)}2\le 2p,\qquad
  2d\le q-1+\left\lfloor\frac{\sqrt{16p+9}-3}{2}\right\rfloor.
\]
For square matrices the right hand side of the first inequality improves to \(p\). The proof uses coefficients only through degree four.

## Pooled row and column moments

The first derivative forces \(\sum X_{ij}=0\), so each additive matrix has unique centered row and column offsets. Their respective lists of coordinates on the parameter space have power sums \(A_j=\sum u_i^j\) and \(B_j=\sum v_i^j\). Write \(a_j=\binom pj/\binom qj\) and \(b=\binom{p-2}{2}/\binom q2\).

In the normalized permanent the pure degree-\(j\) contributions are \(e_j(u)+a_je_j(v)\). The additional mixed contribution in degree four is \(b\,e_2(u)e_2(v)\), and all mixed terms in degrees two and three vanish by centering. For instance one obtains all coefficients by expanding
\[
 \frac{P((1+u_i+v_j)_{ij})}{P(J)}
   =\sum_{j=0}^p \binom qj^{-1}e_{p-j}(\mathbf 1+u)e_j(v).
\]
Newton's identities give
\[
 A_2+a_2 B_2=0,\quad A_3+a_3 B_3=0,\quad A_4+a_4 B_4=k A_2^2,\qquad
 k=\tfrac12(1+a_4/a_2^2-2b/a_2).
\]
In particular \(k>0\). Indeed \(b/a_2=(p-2)(p-3)/(p(p-1))<1\) and \(a_4/a_2^2=(b/a_2)q(q-1)/((q-2)(q-3))>b/a_2\).

Set \(\lambda=a_3/a_2=(p-2)/(q-2)>0\) and \(w=a_2/\lambda^2>0\). Embed the additive parameter space as \(W=\{(u,\lambda v)\}\subset\mathbb C^{p+q}\). Give its ambient space the nondegenerate bilinear form with unit weights on the row coordinates and common weight \(w\) on the column coordinates, with no complex conjugation. Write \(S_j=A_j+w\lambda^j B_j\) for the weighted pooled moments. Then \(S_2=S_3=0\), and
\[
 S_4=\rho k A_2^2+(1-\rho)A_4,\qquad
 \rho=\frac{a_2\lambda^2}{a_4}
      =\frac{(p-2)(q-3)}{(p-3)(q-2)}>0.
\]

## Rank count

The quadratic form \(A_2\) on \(W\) has rank \(r\ge t\). To see this, projection to the centered column offsets is injective: if \(v=0\), scaling the pure row offset gives \(\prod_i(1+s u_i)=1\) and hence \(u=0\). Since \(A_2=-a_2 B_2\), its radical identifies with a subspace of the orthogonal complement of a \(d\)-space in the nondegenerate centered column space of dimension \(q-1\). Thus \(r\ge2d-q+1\).

Let \(D\) be the span of coordinatewise products of pairs of vectors of \(W\), and let \(e\) be the all-ones vector. By polarization of the pooled moments, \(W\) is isotropic, \(W\perp D\), and \(e\perp W,D\). Also \(\langle e,e\rangle=p+wq>0\).

The rank of the bilinear form on \(D\) is at least \(\binom{r+1}2-p\). Its pullback along the surjection \(\operatorname{Sym}^2 W\to D\) is the middle bilinear form of the polarized quartic \(S_4\). The contribution from \(A_2^2\) has rank \(\binom{r+1}2\). After taking the radical quotient, choose an orthonormal basis of its \(r\)-space. The off-diagonal pair products give a nondegenerate diagonal block, and the diagonal products give a scalar multiple of \(2I+\mathbf1\mathbf1^\mathsf{T}\), also nondegenerate. The contribution from \(A_4\) is a sum of \(p\) rank-one forms, one for each row coordinate. The claimed lower bound follows from rank subadditivity and \(\rho k\ne0\).

Inside \(W^\perp\) the sum of \(W\) and a nondegenerate space from \(D+\mathbb C e\) is direct. Therefore
\[
 2d+1+\binom{r+1}2-p\le p+q.
\]
If \(t>0\), substitute \(2d=q-1+t\) and \(r\ge t\) to get \(t+\binom{t+1}{2}\le2p\). If \(t=0\), this bound holds immediately. Solving the quadratic proves the theorem.

When \(p=q\), \(\rho=1\), so the rank loss of \(p\) from the \(A_4\) term disappears. The improved bound with right hand side \(p\) follows by the same argument. In this square case equality in \(2d+1+\binom{r+1}2\le2p\) also forces \(r=d\); the separate square argument proves this using coordinatewise multiplication and spectral projections.
