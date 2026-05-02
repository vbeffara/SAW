# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
The connective constant μ of the hexagonal lattice equals √(2+√2).

**Status: depends on 3 sorry'd lemmas.**

## Root Sorry Dependencies

### 1. `strip_identity_genuine` (SAWStripIdentityCorrect.lean:361)

**Statement:** For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1:
∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper(T,L,xc) + c_ε · E_m

**Equivalent to:** B_paper(T,L,xc) ≤ 1

**What it requires mathematically:**
The parafermionic observable argument (Lemma 2 of the paper):
1. Define F(z) at each mid-edge z of S_{T,L}
2. Vertex relation at each interior vertex (uses pair_cancellation, triplet_cancellation — PROVED)
3. Discrete Stokes summation (interior mid-edges cancel)
4. Boundary evaluation

**Downstream dependencies:**
- B_paper_le_one → paper_bridge_partial_sum_le → paper_bridge_upper_bound
- paper_bridge_summable, paper_bridge_decay, paper_bridge_sum_le_Z
- Used in BOTH lower bound (Z(xc)=∞) and upper bound (Z(x)<∞ for x<xc)

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean:49)

**Statement:** 1 = c_α · A_inf(T,xc) + xc · paper_bridge_partition(T,xc)

**What it requires:**
- The finite strip identity (sorry #1) for all L
- Monotone convergence: A_{T,L} ↗ A_inf, B_{T,L} ↗ B_inf as L → ∞
- E_T = lim E_{T,L} = 0 (escape walks vanish in the infinite strip)
- OR: direct parafermionic argument on the infinite strip

**Downstream dependencies:**
- bridge_diff_eq → bridge_recurrence_proved → paper_bridge_recurrence_derived
- paper_bridge_lower_bound (c/T lower bound)
- Z_xc_diverges_corrected (lower bound μ ≥ √(2+√2))

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean:258)

**Statement:** ∑_{n≤N} c_n x^n ≤ 2 · (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²

**What it requires (Hammersley-Welsh decomposition):**
1. Split any SAW at the first vertex of minimum diagCoord
2. Each half is a half-plane walk
3. Half-plane walks decompose into bridges (induction on width)
4. The decomposition is injective (up to factor 2)
5. Walk length ≥ sum of bridge lengths

**Downstream dependencies:**
- hw_summable_corrected (upper bound Z(x)<∞ for x<xc)
- connective_constant_eq_corrected (μ ≤ √(2+√2))

## Proved Infrastructure (sorry-free)

### Core algebraic identities (SAW.lean)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- `c_alpha_pos`, `c_eps_pos`, `xc_pos`, `xc_lt_one'`
- `bridge_bound_of_strip_identity`: 1 = c_α A + B + c_ε E with A,E≥0 ⟹ B≤1
- `quadratic_recurrence_lower_bound`: B_T ≤ α B_{T+1}² + B_{T+1} with B₁>0 ⟹ B_T ≥ c/T

### Cutting argument (SAWCuttingProof.lean)
- `cutting_argument_proved`: A_{T+1} - A_T ≤ xc · B_{T+1}²
- `extra_walk_decomp`, `extra_walk_sum_le_proved`

### Bridge infrastructure (SAWDiagProof.lean)
- `PaperBridge` structure, `paper_bridge_partition`
- `paper_bridge_length_ge`: bridge of width T has length ≥ T
- `paper_bridge_partial_sum_le`: partial sums bounded (depends on strip_identity_genuine)
- `paper_bridge_upper_bound`: B(T,xc) ≤ 1/xc (depends on strip_identity_genuine)

### Submultiplicativity and Fekete (SAWSubmult.lean, SAW.lean)
- `saw_count_submult'`: c_{m+n} ≤ c_m · c_n
- `fekete_submultiplicative`: lim c_n^{1/n} exists and equals inf c_n^{1/n}
- `connective_constant_eq_from_bounds`: μ = √(2+√2) from Z(xc)=∞ and Z(x)<∞ for x<xc

### Walk counting (SAWZigzagBuild.lean)
- `saw_count_pos`: c_n ≥ 1 for all n
- `saw_count_vertex_independent`: c_n is independent of starting vertex

### Translation invariance (SAWTranslation.lean)
- `hexTranslate_preserves_strip'`, `hexTranslate_preserves_bool`
- `translateWalk_length`, `translateWalk_isPath`

### Bridge and lower bound (SAWPaperChain.lean)
- `paper_bridge_partition_one_pos`: B₁(xc) > 0
- `paper_bridge_partition_pos`: B_T(xc) > 0 for T ≥ 1
- `paper_bridge_recurrence`: ∃ α>0, B_T ≤ α B_{T+1}² + B_{T+1} (depends on infinite_strip_identity)
- `paper_bridge_lower_bound`: ∃ c>0, B_T ≥ c/T (depends on recurrence)
- `paper_bridge_decay`: B_T(x) ≤ (x/xc)^T / xc for x < xc (depends on strip_identity_genuine)
- `Z_xc_diverges_corrected`: Z(xc) = ∞ (depends on sorry #1 and #2)
- `hw_summable_corrected`: Z(x) < ∞ for x < xc (depends on sorry #1 and #3)

### Half-plane walk infrastructure (NEW: SAWHWDecompHelper.lean)
- `walk_min_dc_le`: min diagCoord ≤ any vertex's diagCoord (sorry-free)
- `walk_min_dc_achieved`: min diagCoord is achieved by some vertex (sorry-free)
- `walk_width_le_length`: walk width ≤ walk length (sorry-free)
- `suffix_dc_bound`: suffix after min vertex has diagCoord ≥ min (sorry-free)

### Strip membership helpers (NEW: SAWHWExtractBridge.lean)
- `false_in_strip`: FALSE vertex with d ∈ [-T,-1] ∈ PaperInfStrip T (sorry-free)
- `true_in_strip`: TRUE vertex with d ∈ [-(T-1),0] ∈ PaperInfStrip T (sorry-free)

## File Organization

```
SAW.lean                    — Core definitions and algebraic identities
SAWStripIdentityCorrect.lean — Strip domain, partition functions, strip identity [SORRY]
SAWDiagProof.lean           — Paper bridges, partial sum bounds
SAWCutting.lean             — Cutting argument structure
SAWCuttingProof.lean        — Cutting argument proof (sorry-free)
SAWRecurrenceProof.lean     — Bridge recurrence from infinite strip identity [SORRY]
SAWPaperChain.lean          — Main theorem, lower/upper bounds [SORRY for decomposition]
SAWTranslation.lean         — Translation invariance (sorry-free)
SAWHWDecompHelper.lean      — Walk diagCoord infrastructure (sorry-free, NEW)
SAWHWExtractBridge.lean     — Strip membership helpers (sorry-free, NEW)
```
