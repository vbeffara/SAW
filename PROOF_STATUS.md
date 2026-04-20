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
- **Bridge infrastructure**: PaperBridge, paper_bridge_partition, paper_bridge_length_ge
- **Cutting argument**: `cutting_argument_proved` — A_{T+1} - A_T ≤ xc · B_{T+1}²
- **Bridge recurrence**: `paper_bridge_recurrence` — derived from
  infinite strip identity + cutting argument (via `SAWRecurrenceProof.lean`)
- **Bridge decay**: `paper_bridge_decay` — B_T^x ≤ (x/xc)^T / xc for x < xc
- **Bridge partial sum bound**: `paper_bridge_partial_sum_le` — Σ xc^{len} ≤ 1/xc
- **Bridge lower bound**: `paper_bridge_lower_bound` — ∃ c > 0, B_T ≥ c/T
- **Bridge-SAW injection**: `paperBridge_toSAW_sigma_injective`
- **Zigzag construction**: saw_count_even_lower_proved, saw_count_sq_ge_two_pow_proved
- **Quadratic recurrence lower bound**: `quadratic_recurrence_lower_bound`
- **Main theorem assembly**: `connective_constant_eq_from_bounds` (modulo sorry dependencies)
- **Winding analysis**: boundary coefficients c_α, c_ε computed
- **Direction vectors**: false_to_true_dir, starting_direction, right_boundary_exit_angle
- **Boundary coefficient positivity**: c_alpha_pos, c_eps_pos, boundary_cos_pos
- **Powerset product identity**: `powerset_prod_identity` (from Mathlib's Finset.prod_one_add)
- **Diagonal coordinate**: `diagCoord`, `diagCoord_step_bound`, SAW depth bounds

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

**What it blocks:** Both directions of the main theorem:
- Lower bound μ ≥ √(2+√2) via bridge recurrence + lower bound
- Upper bound μ ≤ √(2+√2) via B_paper ≤ 1 → bridge decay

**Why it's hard:** This is the core mathematical innovation of the paper.
The proof requires:
1. **Vertex relation** (Lemma 1): pair/triplet partition of walks at each vertex
2. **Discrete Stokes** summation over all vertices (interior cancel, boundary survive)
3. **Boundary evaluation** computing winding contributions

**Available algebraic infrastructure (all proved):**
- pair_cancellation, triplet_cancellation
- boundary_cos_pos, c_alpha_pos, c_eps_pos
- direction vectors: false_to_true_dir, starting_direction
- correctHexEmbed, hexEdgeAngle

**Missing combinatorial infrastructure:**
- Walk pairing: partition SAWs at each vertex into pairs/triplets
- Exhaustiveness: every contributing SAW belongs to exactly one pair/triplet
- Discrete Stokes summation (trivially follows from vertex relation)
- Boundary evaluation (winding from a to each boundary type)

### Sorry Chain 2: Hammersley-Welsh Decomposition

**Location:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean`
**Statement:** Σ_{n≤N} c_n x^n ≤ 2 × (Σ_{S⊆range(N)} Π_{T∈S} B_{T+1}^x)²

**What it blocks:** Upper bound μ ≤ √(2+√2) (via hw_summable_corrected)

**Independent of Sorry Chain 1** (does not use the strip identity).

**Existing infrastructure:**
- `powerset_prod_identity` — from Mathlib (in SAWHWPaperProof.lean)
- `diagCoord`, `diagCoord_step_bound` — diagonal coordinate (in SAWHWPaperProof.lean)
- `saw_diagCoord_le_length` — depth bounds for SAWs
- hexShift, shiftWalk, shiftWalk_isPath — walk translation
- walk_max_x_bound, walk_max_x_achieved — x-coordinate analysis
- path_split_length, takeUntil/dropUntil — walk splitting

**What's needed:**
1. **Half-plane walk decomposition**: by strong induction on width
2. **General SAW splitting**: split at first vertex of minimum diagCoord
3. **Bridge translation**: map extracted bridges to PaperBridges
4. **Injectivity**: the decomposition uniquely determines the walk
5. **Weight accounting**: walk length ≥ sum of bridge lengths

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
- `SAWHWAlgorithm.lean` — Walk translation, bipartiteness
- `SAWDecomp.lean` — Abstract bridge decomposition theory
- `SAWWalkHelpers.lean` — Walk splitting helpers
- `SAWParafermionic.lean` — Parafermionic observable infrastructure
- `SAWObservableProof.lean` — Observable definitions
- `SAWStokesSkeleton.lean` — Discrete Stokes skeleton

### Non-critical files with sorries
These files contain sorries that are NOT on the critical path (superseded or unused):
- `SAWCutting.lean` — superseded by SAWCuttingProof.lean
- `SAWFiniteStrip.lean` — early versions, superseded
- `SAWBridgeDecomp.lean` — duplicate of paper_bridge_decomp_injection
- `SAWHWDecomp.lean` — x-coordinate version, superseded
- `SAWHWBridge.lean` — superseded infrastructure
- `SAWHammersleyWelsh.lean` — early version, superseded
- `SAWHWInject.lean` — origin_bridge_lower_bound superseded
- `SAWStokesSkeleton.lean` — vertex_relation_observable (placeholder)
- `SAWStripIdentity.lean` — early version, superseded
