# Summary of changes
## Continued Formalization of SAW.tex

I continued the formalization of "The connective constant of the honeycomb lattice equals √(2+√2)" by Duminil-Copin and Smirnov (2012), creating new files and proving a key lemma, reducing the sorry count from 5 to 4.

### New Files Created

1. **`RequestProject/SAWCutting.lean`** (518 lines, 0 sorries) — Formalizes the cutting argument from Section 3:
   - Bridge pair weight identity: x^{ℓ₁+ℓ₂-1} = x⁻¹ · x^{ℓ₁} · x^{ℓ₂}
   - Abstract Hammersley-Welsh injection bound
   - Decreasing sequence length bound for bridge widths
   - Numerical approximation: 1.84 < √(2+√2) < 1.85
   - Imports `SAWStrip.lean`

2. **`RequestProject/SAWLowerBound.lean`** (132 lines, 0 sorries) — Complete lower bound proof structure:
   - Case 2 bridge lower bound: E=0 ⟹ B_T ≥ c/T
   - Bridge recurrence holds in both cases
   - Bridge series always diverges (combining cases)
   - Geometric bridge sum convergence for x < x_c
   - Imports `SAWProof.lean`

### Key Proof Completed: `saw_count_step_le_mul_two`

Previously sorry'd, now fully proved: **c_{n+1} ≤ 2·c_n for n ≥ 1**.

The proof uses fiber counting via the truncation map. Three helper lemmas were added and proved:
- `saw_eq_of_trunc_and_last`: SAW determined by truncation + last vertex
- `saw_last_adj`: Last vertex is adjacent to n-th vertex
- `saw_last_not_in_trunc`: Last vertex not in truncation's support
- Also added `SAW.instDecidableEq` for the fiber counting to work

This also enables `saw_count_upper_bound: c_n ≤ 3·2^{n-1}` (elementary bound from Section 1).

### Remaining Sorries (4, down from 5)

| File | Theorem | Description |
|------|---------|-------------|
| SAWBridge.lean:349 | `hammersley_welsh_bound` | Z(x) converges for x < x_c |
| SAWBridge.lean:377 | `lower_bound_from_strip_identity` | Z(x_c) diverges |
| SAWFinal.lean:79 | `connective_constant_eq` (lower) | Depends on above |
| SAWFinal.lean:84 | `connective_constant_eq` (upper) | Depends on above |

These require connecting the abstract proof structure to concrete graph-theoretic bridge decomposition, which is the main remaining gap.

### Project Size: 6,467 lines across 19 Lean files, 17 of which are sorry-free.