# Summary: Continued Formalization of SAW.tex

## New files created

### `RequestProject/SAWSubmult.lean` (sorry-free, ~475 lines)
Formalizes the **submultiplicativity** of self-avoiding walk counts: `c_{n+m} ≤ c_n · c_m`.

**Key proved results:**
- **Graph automorphisms**: `hexTranslate` (translation) and `hexFlip` (sublattice swap) are graph automorphisms of the hexagonal lattice, preserving adjacency, walks, and paths
- **Walk splitting**: `walk_take_isPath` and `walk_drop_isPath` — splitting a path at any position preserves the path property
- **SAW vertex independence**: `saw_count_vertex_independent` — the number of n-step SAWs is the same from any vertex (using translation + flip)
- **Submultiplicativity injection**: `sawSplit` splits an (n+m)-step SAW into a sigma pair of n-step and m-step SAWs; proved injective via `sawSplit_injective`
- **Main result**: `saw_count_submult'` — `∀ n m, saw_count (n + m) ≤ saw_count n * saw_count m`

All 25+ lemmas in this file are fully proved (no sorry, standard axioms only).

### `RequestProject/SAWMain.lean` (sorry-free, ~240 lines)
Formalizes results about the **connective constant** and **conjectures from Section 4**.

**Key proved results:**
- **`connective_constant_is_limit'`**: The connective constant equals `lim_{n→∞} c_n^{1/n}`, proved from scratch using Fekete's lemma + submultiplicativity + a direct infimum argument
- **`connective_constant_pos'`**: The connective constant is positive (μ ≥ 1 > 0)

**Formalized conjectures from Section 4 of the paper:**
- **Nienhuis' asymptotic formula**: `nienhuis_asymptotic_conjecture` — `c_n ~ A · n^{γ-1} · μ^n` with γ = 43/32
- **Flory exponent conjecture**: `flory_exponent_conjecture` — mean-square displacement grows as `n^{3/2}`
- **SLE parameter**: κ = 8/3 for the conjectured scaling limit
- **Bridge decay conjecture**: `B_T^{x_c} ~ T^{-1/4}`
- **Hammersley-Welsh bound statement**: `c_n ≤ exp(κ√n) · μ^n`

**New definitions:**
- `gamma_SAW`, `nu_SAW`, `kappa_SAW` — critical exponents from the physics literature
- `mean_square_displacement` — formalized using the hex lattice embedding
- `bridge_decay_conjecture`, `hammersley_welsh_bound_statement` — formal statements of conjectures

## Changes to existing files

### `RequestProject/SAW.lean`
- The sorry'd `connective_constant_is_limit` and `connective_constant_pos` were removed (replaced by comments pointing to SAWMain.lean where they're proved)
- `saw_count_submult` remains as a sorry'd forward declaration (proved in SAWSubmult.lean as `saw_count_submult'`)

## Remaining sorry statements in SAW.lean (5)
These represent the deepest mathematical content requiring full strip-domain analysis:
1. `saw_count_submult` — proved in SAWSubmult.lean (forward declaration kept for reference)
2. `connective_constant_eq` — **Main Theorem** μ = √(2+√2)
3. `connective_constant_eq_inv_xc` — μ = x_c⁻¹
4. `partition_function_diverges_above_xc` — Z(x) = ∞ for x > x_c
5. `partition_function_converges_below_xc` — Z(x) < ∞ for x < x_c

## Summary of sorry-free content across all files

| File | Lines | Sorry-free theorems | Description |
|------|-------|-------------------|-------------|
| SAW.lean | 742 | 18+ | Constants, algebraic identities, Fekete's lemma, bridge bounds, SAW finiteness, SAW count positivity |
| SAWStrip.lean | 424 | 10+ | Hex lattice properties, geometric embedding, strip domains, boundary coefficients |
| SAWSubmult.lean | 475 | 25+ | Graph automorphisms, walk splitting, vertex independence, submultiplicativity |
| SAWMain.lean | 240 | 5+ | Connective constant limit/positivity, Section 4 conjectures |

Total: **58+ sorry-free theorems** covering the algebraic, combinatorial, and analytic foundations of the paper.
