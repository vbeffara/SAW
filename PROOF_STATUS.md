# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main theorem

`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
```
μ = √(2+√2)
```

**Status: 3 independent sorry chains remain.**

## Fully proved infrastructure

The following are fully proved (no sorry):
- **Hexagonal lattice**: `hexGraph`, decidable adjacency, local finiteness
- **SAW infrastructure**: `SAW`, `saw_count`, finiteness, vertex independence
- **Submultiplicativity**: `saw_count_submult'` — c_{n+m} ≤ c_n · c_m
- **Fekete's lemma**: `fekete_submultiplicative` — submultiplicative sequences converge
- **Connective constant**: `connective_constant`, `connective_constant_is_limit'`, positivity
- **Algebraic identities** (Lemma 1 of the paper):
  - `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
  - `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0
- **Bridge infrastructure**: PaperBridge, paper_bridge_partition, paper_bridge_length_ge
- **Cutting argument**: `cutting_argument_proved` — A_{T+1} - A_T ≤ xc · B_{T+1}²
- **Bridge decay**: `paper_bridge_decay` — B_T^x ≤ (x/xc)^T / xc for x < xc
- **Bridge partial sum bound**: `paper_bridge_partial_sum_le` — Σ xc^{len} ≤ 1/xc
  (depends on strip_identity_genuine via B_paper_le_one)
- **Bridge lower bound**: `paper_bridge_lower_bound` — ∃ c > 0, B_T ≥ c/T
  (depends on paper_bridge_recurrence)
- **Bridge-SAW injection**: `paperBridge_toSAW_sigma_injective`
- **Zigzag construction**: saw_count_even_lower_proved, saw_count_sq_ge_two_pow_proved
- **Main theorem assembly**: `connective_constant_eq_corrected` (modulo sorry dependencies)

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
│                               └── SAWPaperChain.lean
│                                   ├── paper_bridge_recurrence ⚠️ [SORRY]
│                                   ├── paper_bridge_decomp_injection ⚠️ [SORRY]
│                                   ├── paper_bridge_lower_bound ✓ (from recurrence)
│                                   ├── Z_xc_diverges_corrected ✓ (from lower bound)
│                                   ├── hw_summable_corrected ✓ (from decomp injection)
│                                   └── connective_constant_eq_corrected ✓ (from above)
```

## Remaining sorry chains

### Sorry 1: Strip identity (Lemma 2)
**Location:** `strip_identity_genuine` in `SAWStripIdentityCorrect.lean`
**Statement:** For the finite strip S_{T,L} with T ≥ 1 and L ≥ 1,
  ∃ A_m E_m ≥ 0, 1 = c_α · A_m + B_paper T L xc + c_ε · E_m

**What it blocks:** B_paper ≤ 1 → bridge partial sum bounds → paper_bridge_recurrence

**What's needed to prove it:**
1. The vertex relation (Lemma 1): at each vertex v in the strip, the weighted
   sum of the parafermionic observable over v's three mid-edges vanishes.
   - Algebraic part: PROVED (pair_cancellation, triplet_cancellation)
   - Combinatorial part: NOT PROVED (partitioning walks into pairs/triplets,
     proving exhaustiveness of the partition)
2. Discrete Stokes theorem: summing vertex relations over all vertices,
   interior mid-edges cancel, only boundary mid-edges survive.
   - This is a straightforward rearrangement of sums (interior edge contributions
     cancel by symmetry).
3. Boundary evaluation: computing the winding and direction factors for each
   boundary type (starting, left, right, escape boundaries).
   - Direction factors: PROVED (false_to_true_dir, starting_direction,
     right_boundary_exit_angle)
   - Boundary coefficient positivity: PROVED (c_alpha_pos, c_eps_pos,
     boundary_cos_pos)

### Sorry 2: Bridge recurrence
**Location:** `paper_bridge_recurrence` in `SAWPaperChain.lean`
**Statement:** ∃ α > 0, ∀ T, paper_bridge_partition T xc ≤ α · B_{T+1}² + B_{T+1}

**What it blocks:** paper_bridge_lower_bound → Z_xc_diverges → main theorem (lower bound)

**What's needed to prove it:**
- The infinite strip identity: 1 = c_α A_T + xc · B_T + c_ε E_T (for L → ∞)
  - This follows from strip_identity_genuine by monotone convergence
- The cutting argument: A_{T+1} - A_T ≤ xc · B_{T+1}²
  - PROVED as `cutting_argument_proved`
- E monotonicity: E_{T+1} ≤ E_T (wider strip has fewer escape walks)
- The paper's argument actually handles two cases separately:
  - Case 1: E_T > 0 for some T → Z(xc) = ∞ directly
  - Case 2: E_T = 0 for all T → recurrence with α = c_alpha

### Sorry 3: Hammersley-Welsh decomposition
**Location:** `paper_bridge_decomp_injection` in `SAWPaperChain.lean`
**Statement:** ∑_{n≤N} c_n x^n ≤ 2 × (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}^x)²

**What it blocks:** hw_summable_corrected → main theorem (upper bound)

**What's needed to prove it:**
1. Half-plane walk decomposition: by strong induction on width, each half-plane
   SAW decomposes into bridges of strictly decreasing widths.
2. General SAW splitting: split at the first vertex of maximum diagonal depth
   into two half-plane walks.
3. Injectivity: the decomposition uniquely determines the walk (given the bridge
   sequence and the starting mid-edge choice, the walk is reconstructable).
4. Weight accounting: walk length ≥ sum of bridge lengths, so x^n ≤ ∏ x^{len_i}
   for 0 < x ≤ 1.
5. Counting: the injection gives ∑ c_n x^n ≤ 2 × (∏(1 + B_T))² .

## Files with sorry's NOT on the main critical path

These sorry's exist but are either superseded by proved versions elsewhere
or are not imported by the main theorem:

- `SAWCutting.lean:100` — `cutting_argument` (superseded by `cutting_argument_proved`)
- `SAWZigzag.lean:142,147` — zigzag bounds (proved in SAWZigzagBuild.lean)
- `SAWBridge.lean:357` — old bridge summability (superseded)
- `SAWFiniteStrip.lean` — old finite strip infrastructure
- `SAWStokesSkeleton.lean:82` — vertex_relation_observable (scaffolding)
- `SAWHWAlgorithm.lean`, `SAWHWDecomp.lean` — old HW decomposition attempts
- `SAWBridgeDecomp.lean`, `SAWHWBridge.lean`, `SAWHammersleyWelsh.lean` — old infrastructure
- `SAWStripIdentity.lean` — old strip identity attempt
