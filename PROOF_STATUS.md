# Proof Status: SAW Connective Constant

## Main Theorem
`connective_constant_eq` (SAWFinal.lean): μ = √(2+√2)

**Status: Depends on `sorryAx`** — three root sorry lemmas remain.

## Root Sorry Lemmas

### 1. `strip_identity_genuine` (SAWStripIdentityCorrect.lean)
**Statement:** For the finite strip S_{T,L}, ∃ A_m E_m ≥ 0, 1 = c_α·A_m + B_paper T L xc + c_ε·E_m
**Equivalent to:** B_paper T L xc ≤ 1
**Required for:** paper_bridge_partial_sum_le → paper_bridge_summable → paper_bridge_decay → hw_summable_corrected
**Proof approach:** Parafermionic observable (Lemma 2 of Duminil-Copin & Smirnov 2012)
**What's proved:**
- T=1 case: `strip_identity_genuine_T1'` (SAWStripT1Direct.lean) ✓
- Algebraic ingredients: `pair_cancellation`, `triplet_cancellation` ✓
- Vertex phase identity: `vertex_phase_identity` ✓ (NEW: SAWVertexIdentity.lean)
  - e^{-i5π/8} + xc·e^{iπ/4} + xc·e^{iπ/2} = 0
  - This is the algebraic core of the vertex relation (Lemma 1)
- Boundary coefficients: ✓ (NEW: SAWVertexIdentity.lean)
  - Left boundary: cos((1-σ)π) = c_alpha ✓
  - Right boundary: Re[1] = 1 ✓
  - Escape boundary: cos((1-σ)·2π/3) = c_eps ✓
- Boundary cos positivity: `boundary_cos_pos` ✓
- Hex direction cos positivity: `hex_dir_cos_pos` ✓ (NEW: SAWBoundarySum.lean)
- Reduction to `boundary_sum_identity`: SAWStripProofDirect.lean ✓
**What remains:**
- Defining the parafermionic observable F at each mid-edge
- Proving that the vertex relation holds for each vertex (using the walk grouping)
- Proving interior edge cancellation in the vertex sum
- Computing the boundary sum

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** 1 = c_α · A_inf T xc + xc · paper_bridge_partition T xc
**Required for:** bridge_recurrence → paper_bridge_lower_bound → Z_xc_diverges
**Proof approach:** Pass finite strip identity to L→∞ limit (or apply parafermionic to infinite strip)
**What's proved:**
- T=1 case (modulo A_inf_1_exact): `infinite_strip_identity_T1_clean` (SAWInfStripT1.lean)
- A_inf_1_exact: sorry (needs walk enumeration in strip-1 path graph)
- paper_bridge_partition_1_eq: proved ✓
- Cutting argument: `cutting_argument_proved` (SAWCuttingProof.lean) ✓
- Bridge recurrence from identity: `bridge_recurrence_proved` ✓

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**Statement:** ∑ c_n x^n ≤ 2·(∑_{S} ∏_{T∈S} B_{T+1}(x))²
**Required for:** hw_summable_corrected → Z(x) < ∞ for x < xc
**Proof approach:** Hammersley-Welsh bridge decomposition
**Note:** This requires bridge summability (from #1) for the bound to be meaningful.

## Newly Proved Lemmas (This Session)

### SAWVertexIdentity.lean (NEW FILE, fully proved)
- `vertex_phase_identity`: e^{-i5π/8} + xc·e^{iπ/4} + xc·e^{iπ/2} = 0
  This is the key algebraic identity for the vertex relation, equivalent to
  triplet_cancellation multiplied by e^{-i5π/8}.
- `vertex_phase_from_triplet`: derives vertex_phase_identity from triplet_cancellation
- `right_boundary_re_coeff`: Re coefficient for right boundary = 1
- `left_boundary_re_coeff`: cos((1-σ)π) = c_alpha
- `escape_boundary_re_coeff_pos`: cos((1-σ)·2π/3) = c_eps
- `escape_boundary_re_coeff_neg`: cos((1-σ)·(-2π/3)) = c_eps

### SAWBoundarySum.lean (NEW FILE, fully proved)
- `hexDirAngle`: direction angle definition for hex edges
- `hex_dir_cos_pos`: cos(3θ/8) > 0 for all hex edge directions
- `right_boundary_cos_one`: cos(3·0/8) = 1 for right boundary edges
- `starting_edge_angle`: direction angle from paperStart to hexOrigin = π

## Dependency Structure

```
strip_identity_genuine (#1)
  → B_paper_le_one → paper_bridge_partial_sum_le
  → paper_bridge_summable → paper_bridge_decay
  → Also needed for paper_bridge_decomp_injection (#3) to be meaningful

infinite_strip_identity (#2)
  → bridge_recurrence → paper_bridge_lower_bound
  → Z_xc_diverges_corrected

paper_bridge_decomp_injection (#3) + paper_bridge_decay (from #1)
  → hw_summable_corrected → Z(x) < ∞ for x < xc

Both Z_xc_diverges + hw_summable → connective_constant_eq
```

## Proved Infrastructure (sorry-free)

### Core Definitions (SAW.lean)
- Hexagonal lattice, SAW definition, connective constant ✓
- Algebraic constants: xc, c_alpha, c_eps, j, λ ✓
- `pair_cancellation`, `triplet_cancellation` ✓
- `xc_inv` ✓

### Submultiplicativity (SAWSubmult.lean)
- `saw_count_submult'` ✓
- `saw_count_pos` ✓

### Fekete's Lemma (SAWMain.lean)
- `connective_constant_is_limit'` ✓
- `connective_constant_pos'` ✓

### Bridge Infrastructure (SAWBridge.lean, SAWBridgeFix.lean)
- Bridge definition, partition functions ✓
- `connective_constant_eq_from_bounds` ✓

### Strip Infrastructure (SAWStripIdentityCorrect.lean)
- PaperInfStrip, PaperFinStrip, PaperSAW_A/B/E definitions ✓
- Finiteness of PaperSAW_B ✓
- Non-negativity lemmas ✓
- B_paper ≤ 1 from strip identity ✓ (depends on sorry)

### Vertex Relation Algebra (SAWVertexIdentity.lean) — NEW
- `vertex_phase_identity` ✓
- Boundary coefficient lemmas ✓

### Boundary Sum Infrastructure (SAWBoundarySum.lean) — NEW
- `hexDirAngle` definition ✓
- `hex_dir_cos_pos` ✓
- Boundary direction lemmas ✓

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved` ✓
- `extra_walk_sum_le_proved` ✓

### Bridge Recurrence (SAWRecurrenceProof.lean)
- `bridge_recurrence_proved` ✓ (depends on infinite_strip_identity)
- `paper_bridge_recurrence_derived` ✓ (depends on infinite_strip_identity)

### Walk Infrastructure (SAWWalkSplit.lean)
- Walk splitting lemmas ✓
- PaperFinStrip monotonicity ✓
- B_paper monotonicity in L ✓

### T=1 Special Case
- `paper_bridge_partition_1_eq` (SAWStripT1Exact.lean) ✓
- `strip_identity_genuine_T1'` (SAWStripT1Direct.lean) ✓
- `B_paper_1_lt_one'` (SAWStripT1Direct.lean) ✓

### Lower Counting Bounds (SAWZigzagBuild.lean)
- `saw_count_even_lower_proved` ✓
- `saw_count_sq_ge_two_pow_proved` ✓

### Paper Chain (SAWPaperChain.lean)
- `paper_bridge_summable` ✓ (depends on strip_identity_genuine)
- `paper_bridge_partition_one_pos` ✓ (depends on strip_identity_genuine)
- `paper_bridge_lower_bound` ✓ (depends on infinite_strip_identity)
- `paper_bridge_decay` ✓ (depends on strip_identity_genuine)
- `Z_xc_diverges_corrected` ✓ (depends on both #1 and #2)
- `hw_summable_corrected` ✓ (depends on #1 and #3)
- `connective_constant_eq_corrected` ✓ (depends on all three)

## What Remains for the Full Proof

The three root sorry lemmas (#1, #2, #3) are deeply mathematical results:

1. **Parafermionic observable (B_paper ≤ 1)**: All algebraic ingredients are proved
   (pair/triplet cancellation, vertex phase identity, boundary coefficients, direction
   cosine positivity). What remains is the combinatorial infrastructure:
   - Defining the observable at each mid-edge as a sum over walks
   - Grouping walks at each vertex into pairs/triplets that cancel
   - Proving exhaustiveness of the grouping
   - The discrete Stokes summation (interior cancellation + boundary evaluation)

2. **Infinite strip identity**: Follows from #1 by taking L→∞ or by applying the
   parafermionic argument directly to the infinite strip.

3. **Hammersley-Welsh decomposition**: A combinatorial argument about decomposing SAWs
   into bridges at height records. Requires:
   - Defining the canonical bridge decomposition
   - Proving injectivity of the decomposition
   - Bounding the weight by the product formula
