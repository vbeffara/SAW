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

**Statement:** ∃ A E ≥ 0, 1 = c_α·A + B_paper T L xc + c_ε·E

**Equivalence:** This is equivalent to B_paper T L xc ≤ 1.

**Mathematical content (Lemma 2 of the paper):**
This is proved via the parafermionic observable. The proof requires:

1. **Observable definition:** F(z) at each mid-edge z, summing over SAWs with
   complex weights exp(-iσW) · xc^ℓ.

2. **Key geometric fact (proved in SAWWindingProof.lean):** On the hex lattice,
   the winding from the starting mid-edge to any other mid-edge is
   PATH-INDEPENDENT for self-avoiding walks. The winding equals the angle of
   the final half-edge direction minus the initial half-edge direction.
   This means F(z) = (complex phase) · (real partition function).

3. **Vertex relation (Lemma 1):** At each interior vertex v,
   Σ d_i · F(z_i) = 0
   This is proved by partitioning walks into "pairs" and "triplets":
   - **Triplet:** A walk γ not visiting v, ending at neighbor w_k, paired with
     its extensions γ·[w_k→v→w_j] for each available j.
   - **Pair:** A walk passing through v using two edges, paired with the walk
     using the same edges in reverse at v.
   The algebraic cancellation follows from:
   - `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0 ✓
   - `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0 ✓

4. **Discrete Stokes:** Sum vertex relations over all interior vertices.
   Interior mid-edges cancel (each appears with opposite signs from its two
   endpoints). Boundary mid-edges survive.

5. **Boundary evaluation:**
   - Starting mid-edge a: direction = -1, F(a) = 1 → contribution = -1
   - Right boundary β: winding = 0 → contribution = B_edge
   - Left boundary α: winding = ±π → contribution = cos(σπ)·A = -c_α·A
   - Escape boundary ε: winding = ±2π/3 → contribution = c_ε·E

6. **Conclusion:** 0 = -1 + c_α·A + B_edge + c_ε·E → 1 = c_α·A + B_edge + c_ε·E

**What remains to formalize:**
- The combinatorial partition of walks into pairs/triplets at each vertex
  (the most complex part — requires careful case analysis on walk structure)
- The exhaustiveness of the partition (every walk falls into exactly one
  pair or triplet)
- The discrete Stokes summation argument
- The boundary winding evaluation (partially done in SAWWindingProof.lean)

### 2. `paper_bridge_recurrence` (SAWPaperChain.lean, line 131)

**Statement:** ∃ α > 0, ∀ T, B_T ≤ α·B_{T+1}² + B_{T+1}

**Depends on:** strip_identity_genuine (sorry #1)

**Proof strategy (from the paper, Section 3):**
1. From strip_identity_genuine (infinite strip version):
   1 = c_α·A_T + B_T + c_ε·E_T
2. Subtract identities at T and T+1:
   B_T - B_{T+1} = c_α·(A_{T+1} - A_T) + c_ε·(E_{T+1} - E_T)
3. Monotonicity: E_{T+1} ≤ E_T (wider strip has fewer escapes)
4. **Cutting argument:** A_{T+1} - A_T ≤ xc·B_{T+1}²
   (A walk in S_{T+1} reaching α that doesn't fit in S_T must visit
   a FALSE vertex at diagCoord -(T+1). Cut at the first such vertex
   → two bridges of width T+1.)
5. Conclusion: B_T ≤ c_α·xc·B_{T+1}² + B_{T+1}, so α = c_α·xc

**Helper infrastructure (SAWCutting.lean):**
- PaperSAW_A_inf: walks to left boundary in infinite strip
- A_inf: partition function for left boundary walks
- A_inf_diff_reaches_boundary: walks in A_{T+1}\A_T reach diagCoord -(T+1) [sorry]
- cutting_argument: A_{T+1} - A_T ≤ xc · B_{T+1}² [sorry]
- bridge_recurrence_from_identity: derives recurrence from strip identity + cutting [sorry]

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean, line 257)

**Statement:** ∑_{n≤N} c_n·x^n ≤ 2·(∑_{S⊆{0,...,N-1}} ∏_{T∈S} B_{T+1}(x))²

**Independent of:** sorries #1 and #2

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

**What remains to formalize:**
- The decomposition algorithm (split at deepest + recursive bridge extraction)
- Proof that bridge widths are strictly monotone
- Injectivity of the decomposition
- The weight bound (x^n ≤ product of bridge weights)
- Assembly of the counting bound

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

### Winding properties (SAWWindingProof.lean) ✓ [NEW]
- starting_mid_edge_dir: direction from hexOrigin to paperStart is +1
- dir_false_to_true_same': direction from FALSE(x,y) to TRUE(x,y) is +1
- dir_true_to_false_same': direction from TRUE(x,y) to FALSE(x,y) is -1
- right_boundary_winding_zero: right boundary exit = starting direction
- right_boundary_phase: e^{-iσ·0} = 1
- c_alpha_eq_neg_cos: c_α = -cos(5π/8)

### Cutting argument infrastructure (SAWCutting.lean) [NEW, 3 sorries]
- PaperSAW_A_inf, A_inf: left boundary walks in infinite strip
- A_inf_nonneg
- A_inf_diff_reaches_boundary [sorry]
- cutting_argument [sorry]
- bridge_recurrence_from_identity [sorry]

### Main theorem assembly (SAWPaperChain.lean) ✓ (modulo 3 sorries)
- paper_bridge_partition_one_pos
- paper_bridge_lower_bound (from paper_bridge_recurrence)
- paper_bridge_decay (from partial sum bounds)
- Z_xc_diverges_corrected (from lower bound)
- hw_summable_corrected (from decomposition + decay)
- connective_constant_eq_corrected (from above)
