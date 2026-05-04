# Proof Status: SAW Connective Constant

## Main Theorem
`connective_constant_eq_corrected` (SAWPaperChain.lean): μ = √(2+√2)

**Status: Depends on `sorryAx`** — three root sorry lemmas remain in the code,
reducing to **two logically independent** mathematical results.

## Critical Sorry Lemmas

### 1. `strip_identity_genuine` (SAWStripIdentityCorrect.lean)
**Statement:** For the finite strip S_{T,L}, ∃ A_m E_m ≥ 0, 1 = c_α·A_m + B_paper T L xc + c_ε·E_m
**Equivalent to:** B_paper(T,L,xc) ≤ 1
**Logically follows from:** `infinite_strip_identity` (proved in SAWParafermionicProof.lean)
**Required for:** paper_bridge_partial_sum_le → paper_bridge_summable → paper_bridge_decay → hw_summable_corrected
**Proof approach:** Parafermionic observable (Lemma 2 of Duminil-Copin & Smirnov 2012)
**What's proved:**
- T=1 case: `strip_identity_genuine_T1'` (SAWStripT1Direct.lean) ✓
- Algebraic ingredients: `pair_cancellation`, `triplet_cancellation` ✓
- Vertex phase identity: `vertex_phase_identity` ✓
- Boundary coefficients, direction cosine positivity ✓
**What remains:** Walk partitioning into pairs/triplets, discrete Stokes summation

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** 1 = c_α · A_inf(T, xc) + xc · paper_bridge_partition(T, xc)
**Required for:** bridge_recurrence → paper_bridge_lower_bound → Z_xc_diverges
**Also implies:** strip_identity_genuine (sorry #1)
**Proof approach:** Parafermionic observable on infinite strip (no escape boundary)
**What's proved:**
- T=1 case (modulo A_inf_1_exact): `infinite_strip_identity_T1_clean` (SAWInfStripT1.lean)
- Cutting argument: `cutting_argument_proved` (SAWCuttingProof.lean) ✓
- Bridge recurrence from identity: `bridge_recurrence_proved` ✓

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**Statement:** ∑_{n≤N} c_n x^n ≤ 2·(∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²
**Required for:** hw_summable_corrected → Z(x) < ∞ for x < xc
**Proof approach:** Hammersley-Welsh bridge decomposition (1962)
**What remains:**
- Defining the canonical bridge decomposition (split SAW at first max-diagCoord vertex,
  recursively decompose half-plane walks into bridges of decreasing widths)
- Proving injectivity of the decomposition
- Weight accounting (walk length ≥ sum of bridge lengths, giving x^n ≤ ∏ x^{ℓ_i} for x ≤ 1)

### 4. `A_inf_1_exact` (SAWInfStripT1.lean) — minor
**Statement:** A_inf 1 xc = 2·xc³/(1-xc²)
**Required for:** infinite_strip_identity_T1_clean (T=1 special case only)
**Not on critical path** of the main theorem (only for the T=1 special case)

## Logical Structure

The three code-level sorry lemmas reduce to **two logically independent** mathematical results:
- **Parafermionic observable identity** (#1 and #2): Lemma 2 of Duminil-Copin & Smirnov 2012
- **Hammersley-Welsh bridge decomposition** (#3): Hammersley & Welsh, 1962

## Dependency Structure

```
infinite_strip_identity (#2)
  → strip_identity_genuine (#1) [logically, not in code due to import order]
  → B_paper_le_one → paper_bridge_partial_sum_le
  → paper_bridge_summable → paper_bridge_decay

infinite_strip_identity (#2)
  → bridge_recurrence → paper_bridge_lower_bound
  → Z_xc_diverges_corrected

paper_bridge_decomp_injection (#3) + paper_bridge_decay (from #1)
  → hw_summable_corrected → Z(x) < ∞ for x < xc

Z_xc_diverges + hw_summable → connective_constant_eq_corrected
```

## Proved Infrastructure (sorry-free)

### Core Definitions (SAW.lean)
- Hexagonal lattice, SAW definition, connective constant ✓
- Algebraic constants: xc, c_alpha, c_eps, j, λ ✓
- `pair_cancellation`, `triplet_cancellation` ✓
- `xc_inv` ✓

### Submultiplicativity (SAWSubmult.lean)
- `saw_count_submult'`, `saw_count_pos` ✓

### Fekete's Lemma (SAWMain.lean)
- `connective_constant_is_limit'`, `connective_constant_pos'` ✓

### Bridge Infrastructure (SAWBridge.lean, SAWBridgeFix.lean)
- Bridge definition, partition functions ✓
- `connective_constant_eq_from_bounds` ✓

### Strip Infrastructure (SAWStripIdentityCorrect.lean)
- PaperInfStrip, PaperFinStrip, PaperSAW_A/B/E definitions ✓
- Finiteness of PaperSAW_B ✓
- Non-negativity lemmas ✓

### Finite-to-Infinite Strip Connection
- B_paper ≤ xc · paper_bridge_partition: proved ✓ (SAWParafermionicProof.lean)
- B_paper monotone in L: proved ✓ (SAWWalkSplit.lean)

### Vertex Relation Algebra (SAWVertexIdentity.lean)
- `vertex_phase_identity` ✓
- Boundary coefficient lemmas ✓

### Boundary Sum Infrastructure (SAWBoundarySum.lean)
- `hex_dir_cos_pos`, `boundary_cos_pos` ✓

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved` ✓

### Bridge Recurrence (SAWRecurrenceProof.lean)
- `bridge_recurrence_proved` ✓ (depends on infinite_strip_identity)

### Quadratic Recurrence Lower Bound (SAWDecomp.lean)
- `quadratic_recurrence_lower_bound` ✓
- `harmonic_not_summable` ✓
- `not_summable_of_lower_bound` ✓

### T=1 Special Case
- `paper_bridge_partition_1_eq` (SAWStripT1Exact.lean) ✓
- `strip_identity_genuine_T1'` (SAWStripT1Direct.lean) ✓

### Lower Counting Bounds (SAWZigzagBuild.lean)
- `saw_count_even_lower_proved`, `saw_count_sq_ge_two_pow_proved` ✓

### Paper Chain (SAWPaperChain.lean)
- All proved modulo the three sorry lemmas ✓
- `connective_constant_eq_corrected` ✓ (modulo sorries)

## What Remains for the Full Proof

Two independent mathematical results need to be formalized:

1. **Parafermionic observable identity** (Lemma 2 of Duminil-Copin & Smirnov 2012):
   Requires formalizing:
   - Walk partitioning at each vertex into pairs and triplets
   - Proving the vertex relation (using pair_cancellation and triplet_cancellation)
   - Discrete Stokes summation (interior mid-edges cancel, boundary survives)
   - Boundary evaluation
   All algebraic ingredients are proved; the combinatorial walk infrastructure remains.

2. **Hammersley-Welsh bridge decomposition** (Hammersley & Welsh, 1962):
   Requires formalizing:
   - Splitting a SAW at the first vertex with maximum diagCoord
   - Half-plane walk decomposition into bridges of strictly decreasing widths
   - Injectivity of the decomposition (reconstruction argument)
   - Weight accounting
   This is purely combinatorial, independent of #1.
