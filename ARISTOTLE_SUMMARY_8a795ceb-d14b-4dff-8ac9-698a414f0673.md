# Summary of changes
## Hammersley-Welsh Formalization Progress

### Work Completed

I analyzed the full dependency chain for the Hammersley-Welsh argument (`hammersley_welsh_summable` in `RequestProject/SAWHammersleyWelsh.lean`) and made structural progress toward completing the proof. Here is what was accomplished:

#### New Infrastructure in `RequestProject/SAWFiniteStrip.lean`

1. **Added `import RequestProject.SAWDecomp`** to gain access to `bridge_length_ge_width`.

2. **`origin_bridge_in_finite_strip` (proved, sorry-free)**: Every origin bridge of width T fits in the finite strip S_{T, 2·length}. This uses `hexGraph_walk_bound` to bound y-coordinates of walk vertices, combined with `bridge_length_ge_width`. This is a key geometric lemma needed to connect origin bridges to finite strip partition functions.

3. **`originBridgeToStripB` (defined, sorry-free)**: An injection from origin bridges to `StripSAW_B` (finite strip bridge SAWs), defined by pattern matching on the proof that `start_v = hexOrigin`. This cleanly handles the dependent type coercion that was a major technical obstacle.

4. **`originBridgeFitL_pos` (proved, sorry-free)**: The fit parameter L = 2·length is ≥ 1 when T ≥ 1.

5. **`origin_bridge_upper_bound_from_strip` (proved, depends on sorry via `origin_bridge_partial_sum_le_one`)**: Shows `origin_bridge_partition T xc ≤ 1` using `Real.tsum_le_of_sum_le` — if every finite partial sum is bounded by 1, then the tsum is ≤ 1. This reduces the bridge upper bound to bounding partial sums.

6. **`origin_bridge_partial_sum_le_one` (sorry)**: For any finite set F of origin bridges, ∑_{b∈F} xc^{b.length} ≤ 1. This requires completing the injection from F to StripSAW_B and using the sum-vs-tsum inequality with B_TL_le_one.

#### Blueprint Updates (`blueprint/src/content.tex` and `blueprint/lean_decls`)

Added entries for the new theorems with proper `\lean{}`, `\leanok`, `\uses{}` annotations:
- `thm:bridge_in_strip` (origin_bridge_in_finite_strip) — proved
- `thm:bridge_partial_sum` (origin_bridge_partial_sum_le_one) — sorry
- `thm:bridge_upper_from_strip` (origin_bridge_upper_bound_from_strip) — proved modulo partial sum bound

### Remaining Sorry Chain for Hammersley-Welsh

The Hammersley-Welsh argument (`hammersley_welsh_summable`) depends on 3 independent sorry chains:

1. **Strip Identity** (`strip_identity_concrete` in `SAWFiniteStrip.lean`): The deepest result. Requires formalizing the parafermionic observable vertex relation and its telescoping sum over the strip domain. The algebraic identities (pair/triplet cancellation) are fully proved; the gap is connecting them to the concrete partition functions A_TL, B_TL, E_TL.

2. **Partial Sum Bound** (`origin_bridge_partial_sum_le_one` in `SAWFiniteStrip.lean`): Requires completing the injection from finite sets of origin bridges into StripSAW_B and proving the sum-vs-tsum inequality. The injection `originBridgeToStripB` is defined; injectivity and the sum bound remain.

3. **Bridge Decomposition Injection** (`bridge_decomposition_injection` in `SAWHammersleyWelsh.lean`): The core combinatorial result of Hammersley-Welsh (1962). Requires formalizing the decomposition algorithm (splitting at max x-coordinate, half-plane walk recursion) and proving injectivity.

Additionally, `B_T_inf_eq_origin_bridge` (connecting the supremum of finite strip B-partitions to the origin bridge partition) remains sorry'd but is a definitional/limit theorem.

### Architecture

The proof chain is:
```
strip_identity_concrete → B_TL_le_one → origin_bridge_partial_sum_le_one
    → origin_bridge_upper_bound_from_strip → origin_bridge_summable_at_xc
    → origin_bridge_decay → hw_partial_sum_bound → hammersley_welsh_summable
bridge_decomposition_injection → hw_partial_sum_bound
```

The project builds cleanly with all sorry warnings as expected.