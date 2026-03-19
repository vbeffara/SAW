# Summary of changes
## Continued Formalization of SAW.tex

I significantly advanced the formalization of the Duminil-Copin & Smirnov paper "The connective constant of the honeycomb lattice equals √(2+√2)" by creating two new files and proving several key results.

### New File: `RequestProject/SAWSubmult.lean` (fully sorry-free)
Proves the **submultiplicativity** of self-avoiding walk counts (`c_{n+m} ≤ c_n · c_m`), which is a fundamental result for the existence of the connective constant. This required formalizing:

- **Graph automorphisms** of the hexagonal lattice: translation (`hexTranslate`) and sublattice flip (`hexFlip`), both proved to preserve adjacency, walks, and paths
- **Walk splitting**: `walk_take_isPath` and `walk_drop_isPath` — splitting a path at any position preserves the path property
- **SAW vertex independence**: the SAW count is the same from any starting vertex (using the graph automorphisms)
- **Submultiplicativity injection**: `sawSplit` maps (n+m)-step SAWs to pairs of (n-step, m-step) SAWs via a sigma-type injection

All 25+ lemmas are fully proved with standard axioms only.

### New File: `RequestProject/SAWMain.lean` (fully sorry-free)
Contains two major proved results and formalizes Section 4 of the paper:

- **`connective_constant_is_limit'`**: The connective constant equals `lim c_n^{1/n}`, proved from scratch using Fekete's lemma + submultiplicativity + a direct sInf argument
- **`connective_constant_pos'`**: The connective constant is positive (μ ≥ 1)
- **Section 4 conjectures formalized**: Nienhuis' asymptotic formula (γ = 43/32), Flory exponent (ν = 3/4), SLE(8/3) parameter, bridge decay conjecture (T^{-1/4}), and the Hammersley-Welsh bound statement

### Changes to `RequestProject/SAW.lean`
- Removed sorry'd `connective_constant_is_limit` and `connective_constant_pos` (now proved in SAWMain.lean)
- Added comments pointing to the proved versions

### Remaining sorry statements
5 remain in SAW.lean, representing the deepest results:
1. `saw_count_submult` (forward declaration; proved in SAWSubmult.lean as `saw_count_submult'`)
2. `connective_constant_eq` (main theorem μ = √(2+√2))
3. `connective_constant_eq_inv_xc` (μ = x_c⁻¹)
4. `partition_function_diverges_above_xc`
5. `partition_function_converges_below_xc`

The full project builds successfully with `lake build`.