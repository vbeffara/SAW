# Summary of changes
I formalized the main result of the Duminil-Copin & Smirnov paper in `RequestProject/SAW.lean`, continuing from the existing formalization of the algebraic and analytic supporting lemmas.

## New definitions (all sorry-free)

1. **`HexVertex`** (`ℤ × ℤ × Bool`): Vertices of the hexagonal lattice with two sublattices.
2. **`hexOrigin`**: The origin vertex `(0, 0, false)`.
3. **`hexGraph`**: The honeycomb lattice as a `SimpleGraph`, where each vertex `(x, y, false)` is adjacent to `(x, y, true)`, `(x+1, y, true)`, and `(x, y+1, true)`, giving a 3-regular bipartite planar graph. Symmetry and irreflexivity are proved (not sorry'd).
4. **`SAW v n`**: The set of n-step self-avoiding walks from vertex `v` — injective functions `Fin (n+1) → HexVertex` with correct starting point and adjacency.
5. **`saw_count n`**: The number of n-step SAWs from the origin (`Set.ncard` of `SAW hexOrigin n`).
6. **`connective_constant`**: Defined as `sInf` of `{c_n^{1/n} | n ≥ 1}`, which by Fekete's lemma equals `lim c_n^{1/n}`.

## New theorem statements (with sorry proofs)

- **`saw_finite`**: The set of n-step SAWs is finite.
- **`saw_count_pos`**: `c_n > 0` for all n.
- **`saw_count_submult`**: `c_{n+m} ≤ c_n · c_m` (submultiplicativity).
- **`connective_constant_is_limit`**: The connective constant is the limit of `c_n^{1/n}`.
- **`connective_constant_pos`**: `μ > 0`.
- **`connective_constant_eq`** (**Main Theorem**): `μ = √(2+√2)`.
- **`connective_constant_eq_inv_xc`**: Equivalent formulation `μ = x_c⁻¹`.
- **`partition_function_diverges_above_xc`**: Z(x) = ∞ for x > x_c (lower bound).
- **`partition_function_converges_below_xc`**: Z(x) < ∞ for x < x_c (upper bound).

The file builds successfully with only the expected sorry warnings on the proof obligations.