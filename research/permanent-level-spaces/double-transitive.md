# Classification under a doubly transitive row action

For m≥2 and 1≤q≤m, let G act doubly transitively on the m rows of complex m×q matrices. Use the rectangular permanent that matches every column to a different row. If a G-invariant complex linear space L has constant translated permanent, then either L=0 or it is the entire space of centred vectors in one column (dimension m−1). This applies to all square sizes, including composite orders. Only double transitivity is required; G need not contain a transposition.

For vectors u∈ℂᵐ, v∈ℂᑫ, the degree-k term at J in the direction u vᵀ equals a nonzero combinatorial factor times e_k(u)e_k(v). In particular e_d(v) is the product of the nonzero entries of v if its support has cardinality d. Any constant-row matrix in L therefore vanishes: choose d≥1 and use e_d(1)>0.

Averaging any T in L over G gives the zero matrix, so each column sum in T is zero. Fix a row r. Its stabilizer is transitive on the m−1 other rows. Averaging T over this stabilizer and normalizing gives h_r⊗T_r∈L, where h_r(r)=m−1 and h_r(i)=−1 at every other row. For 2≤d≤m,
  
    e_d(h_r) = (−1)^(d−1) (d−1) binom(m,d) ≠ 0.

This follows by choosing whether the subset contains r; equivalently, sum the identity h_r = −1 + m·1_{r} inside each product (only one position in a subset can equal r). If T_r had d≥2 nonzero coordinates, degree d would now contradict the level condition. Every row of every T therefore has at most one nonzero entry.

For a fixed r, the row projection of L is a vector space contained in the union of the coordinate axes. Any two vectors supported on different axes would have a sum on two axes, so at most one axis occurs. Transitivity gives the same column j for every row. L lies inside the centred j-th column. If L is nonzero, the stabilizer-averaged h_r multiples and their G-translates put h_i⊗e_j in L for every i. Since Σ_i c_i h_i=m c whenever Σ_i c_i=0, these vectors span that whole column space. Conversely the rectangular permanent varies only to first order when a single column is changed, and the first-order term is zero for a centred column.
