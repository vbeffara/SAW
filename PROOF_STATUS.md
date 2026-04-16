# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 3 sorry's remaining on the critical path.**

## Critical path (dependency tree)

```
SAW.lean (constants, algebraic identities) ✓
├── SAWSubmult.lean (submultiplicativity: c_{n+m} ≤ c_n·c_m) ✓
│   └── SAWMain.lean (Fekete's lemma → connective constant is a limit) ✓
│       └── SAWBridge.lean (partition function, connective_constant_eq_from_bounds) ✓
│           └── SAWBridgeFix.lean (OriginBridge definition, corrections) ✓
│               └── SAWStripIdentityCorrect.lean (Paper strip domain, partition functions)
│                   ├── strip_identity_genuine ⚠️ [sorry — Lemma 2]
│                   └── B_paper_le_one_obs ✓ [proved FROM strip_identity_genuine]
│                       └── SAWDiagProof.lean (Paper bridge infrastructure) ✓
│                           └── SAWPaperChain.lean (main theorem assembly)
│                               ├── paper_bridge_recurrence ⚠️ [sorry — recurrence]
│                               ├── paper_bridge_decomp_injection ⚠️ [sorry — HW decomposition]
│                               ├── paper_bridge_lower_bound ✓ (from recurrence)
│                               ├── hw_summable_corrected ✓ (from decomposition + decay)
│                               ├── Z_xc_diverges_corrected ✓ (from lower bound)
│                               └── connective_constant_eq_corrected ✓ (from above)
└── SAWDecomp.lean (quadratic recurrence, abstract bridge bounds) ✓
    └── SAWDecompHelpers.lean (diagonal coordinate, walk splitting) ✓
```

## Remaining 3 critical-path sorries

### 1. `strip_identity_genuine` (SAWStripIdentityCorrect.lean, line 361)
**∃ A E ≥ 0, 1 = c_α·A + B_paper T L xc + c_ε·E**

This is Lemma 2 (the strip identity) of Duminil-Copin & Smirnov (2012).
Equivalent to B_paper T L xc ≤ 1.

**Proved algebraic ingredients:**
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- `boundary_cos_pos`: cos(3θ/8) > 0 for |θ| ≤ π

**Remaining infrastructure needed (parafermionic observable proof):**
1. Observable definition: Define F(z) at each mid-edge z as
   ∑_{γ: SAW from a to z} xc^{ℓ(γ)} · exp(-iσW(γ))
2. Vertex relation: At each interior vertex v,
   ∑_{w~v} (embed(w) - embed(v)) · F(mid(v,w)) = 0
   This requires the pair/triplet partition of walks at each vertex.
3. Discrete Stokes: Sum over all vertices → interior mid-edges cancel,
   boundary mid-edges survive. This is a standard telescoping argument.
4. Boundary evaluation: Starting mid-edge → -1, left boundary → c_α·A,
   right boundary → B, escape boundary → c_ε·E.
5. Conclusion: 0 = -1 + c_α·A + B + c_ε·E → B ≤ 1.

The observable definition exists in SAWStokesSkeleton.lean and
SAWObservableProof.lean. The vertex relation is sorry'd in
SAWStokesSkeleton.lean (vertex_relation_observable).

**Consequence:** `B_paper_le_one_obs` (B_paper ≤ 1) is PROVED from this lemma.

### 2. `paper_bridge_recurrence` (SAWPaperChain.lean, line 131)
**∃ α > 0, ∀ T, B_T ≤ α·B_{T+1}² + B_{T+1}**

**Proof strategy (from the paper, Section 3):**
1. Take L→∞ in strip_identity_genuine to get infinite strip identity:
   1 = c_α·A_T + B_T + c_ε·E_T
2. Subtract identities at T and T+1:
   B_T - B_{T+1} = c_α·(A_{T+1} - A_T) + c_ε·(E_{T+1} - E_T)
3. Monotonicity: E_{T+1} ≤ E_T (wider strip has fewer escapes)
4. Cutting argument: A_{T+1} - A_T ≤ xc·B_{T+1}²
   (walks in the wider strip reaching the left boundary that cross
   diagCoord = -(T+1) can be cut into two bridges of width T+1)
5. Conclusion: B_T ≤ c_α·xc·B_{T+1}² + B_{T+1}, so α = c_alpha·xc

**Depends on:** strip_identity_genuine (sorry #1)

The abstract recurrence machinery (`recurrence_from_strip` in SAWDecomp.lean)
is fully proved.

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean, line 257)
**∑_{n≤N} c_n·x^n ≤ 2·(∑_{S⊆{0,...,N-1}} ∏_{T∈S} B_{T+1}(x))²**

**Proof strategy (Hammersley-Welsh decomposition):**
1. For each SAW γ of length n ≤ N from paperStart:
   a. Find the first vertex with minimum diagCoord d(v) = v.1 + v.2.1
   b. Split γ at this vertex into two half-plane walks
2. Each half-plane walk decomposes into bridges of strictly decreasing widths:
   a. Find the last vertex with maximum diagCoord
   b. The prefix is a bridge of width W = max_diag - min_diag
   c. The suffix starts a new half-plane walk of width < W
   d. Recurse
3. The decomposition is injective (given starting mid-edge choice)
4. Weight bound: x^n ≤ ∏ x^{bridge_lengths} since x ≤ 1 and
   the connecting edges between bridges only reduce the total length
5. Factor 2: two choices for first vertex from starting mid-edge
6. Summing: Z_N(x) ≤ 2·(∑_S ∏_{T∈S} B_T(x))² = 2·(∏ (1+B_T))²

**Independent of:** sorries #1 and #2, but requires summability of bridge
partition functions for the tsum in paper_bridge_partition to be well-defined
(not just zero by convention).

**Available infrastructure:**
- SAWDecompHelpers.lean: diagCoord, walk splitting, weight bounds
- SAWBridgeDecomp.lean: powerset_prod_eq, half-plane walk definition
- paper_bridge_length_ge: bridges have length ≥ width
- paperBridge_toSAW: bridges map injectively to SAWs

## Proved infrastructure summary

### Algebraic (SAW.lean) ✓
- Key constants: xc, λ, j, σ, c_α, c_ε
- pair_cancellation, triplet_cancellation
- sqrt_two_add_sqrt_two_eq, xc_inv, xc_pos
- c_alpha_pos, c_eps_pos
- bridge_bound_of_strip_identity

### Combinatorial (SAWSubmult.lean, SAWMain.lean) ✓
- saw_count_submult' (submultiplicativity)
- connective_constant definition
- fekete_submultiplicative
- connective_constant_eq_from_bounds

### Bridge infrastructure (SAWBridge.lean, SAWBridgeFix.lean, SAWDiagProof.lean) ✓
- Bridge, OriginBridge, PaperBridge definitions
- paper_bridge_partition definition
- paper_bridge_length_ge
- paper_bridge_upper_bound (from B_paper_le_one)
- paper_bridge_partial_sum_le
- paperSAW_B_finite'

### Analysis (SAWDecomp.lean) ✓
- recurrence_from_strip
- quadratic_recurrence_lower_bound
- harmonic_not_summable
- not_summable_of_lower_bound
- bridge_product_converges

### Lower bounds (SAWZigzagBuild.lean, SAWLowerCount.lean) ✓
- saw_count_even_lower_proved (2^k ≤ c_{2k})
- saw_count_sq_ge_two_pow (2^n ≤ c_n²)
- connective_constant_pos'

### Decomposition helpers (SAWDecompHelpers.lean) ✓
- diagCoord', diagCoord_adj_bound'
- powerset_prod_eq'
- pow_le_pow_of_le_one_ge
- path_split_length
- hexTranslate_diagCoord'

### Main theorem assembly (SAWPaperChain.lean) ✓ (modulo 3 sorries)
- paper_bridge_partition_one_pos
- paper_bridge_lower_bound (from paper_bridge_recurrence)
- paper_bridge_decay (from partial sum bounds)
- Z_xc_diverges_corrected (from lower bound)
- hw_summable_corrected (from decomposition + decay)
- connective_constant_eq_corrected (from above)

## Non-critical-path sorries

These are in auxiliary files and do NOT affect the main theorem:
- SAWBridgeDecomp.lean: paper_bridge_decomp_injection_v2 (duplicate)
- SAWFiniteStrip.lean: B_T_inf_eq_origin_bridge, origin_bridge_partial_sum_le_one
  (uses different bridge/strip definitions than the critical path)
- SAWHWAlgorithm.lean, SAWHWBridge.lean, SAWHWDecomp.lean, SAWHWInject.lean:
  Alternative formulations of the HW decomposition
- SAWHammersleyWelsh.lean: Early attempts at HW
- SAWStokesSkeleton.lean: vertex_relation_observable (building block for #1)
- SAWStripIdentity.lean: Old strip identity (superseded)
- SAWZigzag.lean: saw_count_even_lower, saw_count_odd_lower
  (proved versions exist in SAWZigzagBuild.lean)
