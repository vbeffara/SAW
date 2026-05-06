# Proof Status: SAW Connective Constant

## Main Theorem
`connective_constant_eq_corrected` (SAWPaperChain.lean): μ = √(2+√2)

**Status: Depends on `sorryAx`** — three root sorry lemmas remain.

### Alternative proof path (SAWMainNew.lean)
`connective_constant_eq_direct` provides an alternative path to the same
theorem. This path avoids `B_paper_le_one_strip` and reduces the dependency
on bridge infrastructure, but still requires the same core mathematical
results. See details below.

## Critical Sorry Lemmas (Root Causes)

### 1. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean)
**Statement:** B_paper(T, L, xc) ≤ 1
**What it encapsulates:** The parafermionic observable identity (Lemma 2 of
Duminil-Copin & Smirnov 2012). This is the key consequence: the weighted
sum of SAWs from paperStart to the right boundary of the finite strip
S_{T,L} is at most 1.
**Required for:** strip_identity_genuine → B_paper_le_one → paper_bridge_partial_sum_le
→ paper_bridge_summable → paper_bridge_decay → hw_summable_corrected

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** 1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
**What it encapsulates:** The parafermionic observable identity for the infinite
strip (no escape boundary). Same argument as #1 but for the infinite strip.
**Required for:** bridge_recurrence → paper_bridge_lower_bound → Z_xc_diverges

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**Statement:** ∑_{n≤N} c_n x^n ≤ 2·(∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²
**What it encapsulates:** Hammersley-Welsh bridge decomposition (1962).
Each SAW can be decomposed into bridges of strictly decreasing widths.
**Required for:** hw_summable_corrected → Z(x) < ∞ for x < xc

## Alternative Proof Path (SAWMainNew.lean)

SAWMainNew.lean provides `connective_constant_eq_direct` via:
- `Z_xc_diverges_direct`: Z(xc) = ∞, using bridge recurrence from
  `infinite_strip_identity`. This version derives bridge summability from
  the Z(xc) < ∞ assumption (used for contradiction), avoiding
  `B_paper_le_one_strip`.
- `hw_summable_direct`: Z(x) < ∞ for x < xc. Currently sorry'd.

### New proved infrastructure (SAWMainNew.lean)
- `paper_bridge_partial_sum_le_Z_direct`: bridges inject into SAWs ✓
- `paper_bridge_summable_of_Z`: bridge summability from Z < ∞ ✓
- `paper_bridge_sigma_sum_le_Z`: sigma-type bridge injection ✓
- `paper_bridge_sum_le_Z_direct`: Σ B_T ≤ Z from Z < ∞ ✓
- `paper_bridge_partition_one_pos_direct`: B_1 > 0 from exact value ✓
- `Z_xc_diverges_direct`: Z(xc) = ∞ ✓ (modulo infinite_strip_identity)

### Remaining sorries in alternative path
1. `infinite_strip_identity` (shared with main path)
2. `hw_summable_direct` — Z(x) < ∞ for x < xc
   This cannot be proved from submultiplicativity alone (the argument is
   circular). It requires the HW bridge decomposition or equivalent.

## Logical Structure

The three root sorries correspond to TWO independent mathematical results:
- **Parafermionic observable identity** (#1 and #2): Lemma 2 of Duminil-Copin & Smirnov 2012
- **Hammersley-Welsh bridge decomposition** (#3): Hammersley & Welsh, 1962

## Proved Infrastructure (sorry-free or depends only on the 3 root sorries)

### Core Definitions (SAW.lean)
- Hexagonal lattice, SAW definition, connective constant ✓
- Algebraic constants: xc, c_alpha, c_eps, j, λ ✓
- `pair_cancellation`, `triplet_cancellation` ✓

### Submultiplicativity (SAWSubmult.lean)
- `saw_count_submult'`, `saw_count_pos` ✓

### Fekete's Lemma (SAWMain.lean)
- `connective_constant_is_limit'`, `connective_constant_pos'` ✓

### Bridge Infrastructure (SAWBridge.lean, SAWBridgeFix.lean)
- Bridge definition, partition functions ✓
- `connective_constant_eq_from_bounds` ✓

### Strip Identity (SAWStripIdentityCorrect.lean)
- PaperInfStrip, PaperFinStrip, PaperSAW_A/B/E definitions ✓
- Finiteness of PaperSAW_B ✓
- `strip_identity_genuine` ✓ (from B_paper_le_one_strip)

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved` ✓

### Bridge Recurrence (SAWRecurrenceProof.lean)
- `bridge_recurrence_proved` ✓ (from infinite_strip_identity + cutting)

### T=1 Special Cases
- `paper_bridge_partition_1_eq` ✓
- `strip_identity_genuine_T1'` ✓
- `A_inf_1_exact` ✓

### Lower Counting Bounds (SAWZigzagBuild.lean)
- `saw_count_even_lower_proved`, `saw_count_sq_ge_two_pow_proved` ✓

### Paper Chain (SAWPaperChain.lean)
- All proved modulo the three root sorries ✓
- `connective_constant_eq_corrected` ✓ (modulo root sorries)
