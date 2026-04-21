# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 2 independent sorry chains remain (3 sorry lemmas on the critical path).**

## Fully proved infrastructure

The following are fully proved (no sorry):
- **Hexagonal lattice**: `hexGraph`, decidable adjacency, local finiteness
- **SAW infrastructure**: `SAW`, `saw_count`, finiteness, vertex independence
- **Submultiplicativity**: `saw_count_submult'` — c_{n+m} ≤ c_n · c_m
- **Fekete's lemma**: `fekete_submultiplicative` — submultiplicative sequences converge
- **Connective constant**: `connective_constant`, `connective_constant_is_limit'`, positivity
- **Partition function radius**: `partition_converges_below_inv_cc`, `partition_diverges_above_inv_cc`
- **Algebraic identities** (Lemma 1 of the paper):
  - `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
  - `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
- **Direction vectors** (vertex relation infrastructure):
  - `false_to_true_dir`, `false_to_true_xp1_dir`, `false_to_true_yp1_dir`
- **Walk extension/retraction**: `walkExtend`, `walkRetract`, round-trip lemmas
- **Adjacency lemmas**: `adj_false_true_same/xp1/yp1`, `adj_true_false_same/xm1/ym1`
- **Bridge infrastructure**: PaperBridge, paper_bridge_partition, paper_bridge_length_ge
- **Cutting argument**: `cutting_argument_proved` — A_{T+1} - A_T ≤ xc · B_{T+1}²
- **Bridge recurrence**: `paper_bridge_recurrence` — from infinite strip identity + cutting
- **Bridge decay**: `paper_bridge_decay` — B_T^x ≤ (x/xc)^T / xc for x < xc
- **Bridge partial sum bound**: `paper_bridge_partial_sum_le` — Σ xc^{len} ≤ 1/xc
- **Bridge lower bound**: `paper_bridge_lower_bound` — ∃ c > 0, B_T ≥ c/T
- **Bridge-SAW injection**: `paperBridge_toSAW_sigma_injective`
- **Zigzag construction**: `saw_count_even_lower_proved`, `saw_count_sq_ge_two_pow_proved`
- **Quadratic recurrence lower bound**: `quadratic_recurrence_lower_bound`
- **Main theorem assembly**: `connective_constant_eq_from_bounds` (modulo sorry dependencies)
- **Winding analysis**: boundary coefficients c_α, c_ε computed
- **Boundary coefficient positivity**: `c_alpha_pos`, `c_eps_pos`
- **Powerset product identity**: from Mathlib's `Finset.prod_one_add`
- **Diagonal coordinate**: `diagCoord`, `diagCoord_step_bound`, SAW depth bounds
- **Walk max/min diagCoord**: `walkMinDiagCoord`, `walkMaxDiagCoord` with bounds
- **Half-plane walk width**: `halfPlaneWidth`, zero characterization
- **SAW count upper bound**: `saw_count_upper_bound'` — c_n ≤ 3·2^{n-1}
- **Walk splitting**: `takeUntil`, `dropUntil`, `walk_split_length'`

## Critical path (dependency tree)

```
SAW.lean (constants, algebraic identities) ✓
├── SAWSubmult.lean (submultiplicativity) ✓
│   └── SAWMain.lean (Fekete's lemma → connective constant exists) ✓
│       └── SAWBridge.lean (partition function) ✓
│           └── SAWBridgeFix.lean ✓
│               └── SAWStripIdentityCorrect.lean
│                   ├── strip_identity_genuine ⚠️ [SORRY — Lemma 2]
│                   └── B_paper_le_one ✓ (from strip_identity_genuine)
│                       └── SAWDiagProof.lean ✓
│                           └── SAWCuttingProof.lean ✓
│                               └── SAWRecurrenceProof.lean
│                                   ├── infinite_strip_identity ⚠️ [SORRY — same chain]
│                                   └── bridge_recurrence_proved ✓
│                                       └── SAWPaperChain.lean
│                                           ├── paper_bridge_recurrence ✓
│                                           ├── paper_bridge_lower_bound ✓
│                                           ├── Z_xc_diverges_corrected ✓
│                                           ├── paper_bridge_decomp_injection ⚠️ [SORRY — HW]
│                                           ├── hw_summable_corrected ✓ (from decomp injection)
│                                           └── connective_constant_eq_corrected ✓ (from above)
```

## Remaining sorry chains (2 independent chains, 3 sorry lemmas)

### Sorry Chain 1: Parafermionic Observable (Lemma 2)

**Two sorry manifestations of the same underlying gap:**

#### 1a. `strip_identity_genuine` in `SAWStripIdentityCorrect.lean`
**Statement:** For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1,
  ∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper T L xc + c_ε · E_m

#### 1b. `infinite_strip_identity` in `SAWRecurrenceProof.lean`
**Statement:** For the infinite strip S_T with T ≥ 1,
  1 = c_α · A_inf T xc + xc · paper_bridge_partition T xc

**What it blocks:** Both directions of the main theorem.

**Why it's hard:** Requires formalizing:
1. Mid-edge walk model (vertex walk + exit direction)
2. Walk classification at each vertex (1, 2, or 3 mid-edges visited)
3. Triplet grouping: 1-mid-edge ↔ two 2-mid-edge walks (via extension)
4. Pair grouping: 3-mid-edge walks paired via loop reversal
5. Exhaustiveness of the partition
6. Discrete Stokes summation (interior cancels, boundary survives)
7. Boundary evaluation (starting, left, right, escape contributions)

**Available algebraic infrastructure (all proved):**
- pair_cancellation, triplet_cancellation
- c_alpha_pos, c_eps_pos
- direction vectors, correctHexEmbed, hexEdgeAngle

### Sorry Chain 2: Hammersley-Welsh Decomposition

**Location:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean`
**Statement:** Σ_{n≤N} c_n x^n ≤ 2 × (Σ_{S⊆range(N)} Π_{T∈S} B_{T+1}^x)²

**What it blocks:** Upper bound μ ≤ √(2+√2) (via hw_summable_corrected)

**Existing infrastructure (in SAWHWDecompFinal.lean, SAWHWDecompNew.lean):**
- `walkMinDiagCoord`, `walkMaxDiagCoord` with bounds
- `halfPlaneWidth`, zero characterization
- `saw_suffix_half_plane` — suffix of split walk is half-plane
- `bridge_weight_le_walk_weight` — weight monotonicity
- `saw_count_upper_bound'` — c_n ≤ 3·2^{n-1}
- `hexShift`, `shiftWalk` — walk translation
- `diagCoord_step_bound` — each step changes diagCoord by ≤ 1

**What's needed:**
1. Half-plane walk bridge extraction (by strong induction on width)
2. Mapping extracted bridges to PaperBridges (via graph automorphism)
3. Full SAW splitting into two half-plane walks
4. Injectivity of the decomposition map
5. Weight factorization: walk length = sum of bridge lengths

## File organization

### Core files (on critical path)
- `SAW.lean` — Constants, algebraic identities
- `SAWSubmult.lean` — Submultiplicativity of c_n
- `SAWMain.lean` — Connective constant via Fekete's lemma
- `SAWBridge.lean` — Partition function, abstract main theorem
- `SAWBridgeFix.lean` — Corrected bridge definitions
- `SAWStripIdentityCorrect.lean` — Strip identity (**strip_identity_genuine: SORRY**)
- `SAWDiagProof.lean` — Diagonal bridge infrastructure
- `SAWCuttingProof.lean` — Cutting argument (proved)
- `SAWRecurrenceProof.lean` — Bridge recurrence (**infinite_strip_identity: SORRY**)
- `SAWPaperChain.lean` — Main theorem assembly (**paper_bridge_decomp_injection: SORRY**)

### Infrastructure files
- `SAWHWPaperProof.lean` — HW decomposition infrastructure (powerset identity, diagCoord)
- `SAWHWDecompNew.lean` — Walk splitting, half-plane SAWs, walkMinDiagCoord
- `SAWHWDecompFinal.lean` — walkMaxDiagCoord, halfPlaneWidth, SAW count bound
- `SAWHWAlgorithm.lean` — Walk translation (hexShift, shiftWalk)
- `SAWParafermionic.lean` — Parafermionic observable infrastructure
- `SAWObservableProof.lean` — Observable definitions
- `SAWStokesSkeleton.lean` — Discrete Stokes skeleton
- `SAWVertexRelFull.lean` — Direction vector proofs
- `SAWWalkExtension.lean` — Walk extension/retraction
- `SAWWalkHelpers.lean` — Walk splitting helpers
