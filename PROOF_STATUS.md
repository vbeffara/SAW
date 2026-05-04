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
- Vertex phase identity: `vertex_phase_identity` ✓ (SAWVertexIdentity.lean)
- Boundary coefficients: ✓ (SAWVertexIdentity.lean)
- Boundary cos positivity: `boundary_cos_pos` ✓
- Hex direction cos positivity: `hex_dir_cos_pos` ✓ (SAWBoundarySum.lean)
**What remains:**
- Defining the parafermionic observable F at each mid-edge with correct winding
- Proving that the vertex relation holds for each vertex (using the walk grouping)
- Proving interior edge cancellation in the vertex sum
- Computing the boundary sum
**Technical issue (winding convention):** The walkWindingInt definition in SAWObservableProof.lean
uses integer multiples of π/3 as the winding unit. While this works for triplet cancellation
(which involves λ^{±1}), the pair cancellation identity j·conj(λ)^4 + conj(j)·λ^4 = 0
requires a winding difference of ±4 units between entering and exiting mid-edges at a vertex,
but a single SAW turn changes the winding by only ±1 unit. The correct winding convention
for the Duminil-Copin & Smirnov observable needs to be identified and implemented. This
is the key remaining technical obstacle for the parafermionic approach.

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** 1 = c_α · A_inf T xc + xc · paper_bridge_partition T xc
**Required for:** bridge_recurrence → paper_bridge_lower_bound → Z_xc_diverges
**Proof approach:** Parafermionic observable on infinite strip (no escape boundary)
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
**What remains:**
- Defining the canonical bridge decomposition (cut SAW at diagonal height records)
- Proving injectivity of the decomposition
- Bounding the weight by the product formula

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

### Vertex Relation Algebra (SAWVertexIdentity.lean)
- `vertex_phase_identity` ✓
- Boundary coefficient lemmas ✓

### Boundary Sum Infrastructure (SAWBoundarySum.lean)
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

The three root sorry lemmas (#1, #2, #3) represent three independent
deep mathematical results:

1. **Parafermionic observable (B_paper ≤ 1)**: The key technical obstacle
   is the winding convention. The existing walkWindingInt definition
   (integer units of π/3) does not correctly capture the pair cancellation
   identity, which requires winding differences of ±4 units. The correct
   winding convention needs to incorporate the lattice geometry more
   carefully. All other algebraic ingredients (pair/triplet cancellation,
   boundary coefficients, direction cosine positivity) are proved.

2. **Infinite strip limit (1 = c_α·A + xc·B)**: Follows from #1 by
   taking L→∞ in the finite strip identity, or by applying the
   parafermionic argument directly to the infinite strip. The T=1 case
   is proved modulo A_inf_1_exact (walk enumeration).

3. **Hammersley-Welsh decomposition**: A purely combinatorial argument
   about decomposing SAWs into bridges at diagonal height records. 
   Independent of #1 and #2 but requires #1 for the final summability
   conclusion.
