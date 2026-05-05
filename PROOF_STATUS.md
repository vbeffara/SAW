# Proof Status: SAW Connective Constant

## Main Theorem
`connective_constant_eq_corrected` (SAWPaperChain.lean): μ = √(2+√2)

**Status: Depends on `sorryAx`** — three root sorry lemmas remain.

## Critical Sorry Lemmas (Root Causes)

### 1. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean)
**Statement:** B_paper(T, L, xc) ≤ 1
**What it encapsulates:** The parafermionic observable identity (Lemma 2 of
Duminil-Copin & Smirnov 2012). This is the key consequence: the weighted
sum of SAWs from paperStart to the right boundary of the finite strip
S_{T,L} is at most 1.
**Proof approach:** Define F(z) at each mid-edge, vertex relation (pair/triplet
decomposition using pair_cancellation + triplet_cancellation), discrete
Stokes summation, boundary evaluation.
**What's proved:** All algebraic ingredients (pair_cancellation,
triplet_cancellation, boundary_cos_pos, direction vectors). T=1 special case
(strip_identity_genuine_T1').
**What remains:** Combinatorial walk pairing/tripling infrastructure,
discrete Stokes summation.
**Required for:** strip_identity_genuine → B_paper_le_one → paper_bridge_partial_sum_le
→ paper_bridge_summable → paper_bridge_decay → hw_summable_corrected

### 2. `infinite_strip_identity` (SAWRecurrenceProof.lean)
**Statement:** 1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
**What it encapsulates:** The parafermionic observable identity for the infinite
strip (no escape boundary). Same argument as #1 but simpler (no ε boundary).
**Required for:** bridge_recurrence → paper_bridge_lower_bound → Z_xc_diverges

### 3. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
**Statement:** ∑_{n≤N} c_n x^n ≤ 2·(∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}(x))²
**What it encapsulates:** Hammersley-Welsh bridge decomposition (1962).
Each SAW can be decomposed into bridges of strictly decreasing widths.
**Proof approach:** Cut SAW at first max-diagCoord vertex, recursively
decompose half-plane walks into bridges, prove injectivity.
**Required for:** hw_summable_corrected → Z(x) < ∞ for x < xc

## Logical Structure

The three root sorries correspond to TWO independent mathematical results:
- **Parafermionic observable identity** (#1 and #2): Lemma 2 of Duminil-Copin & Smirnov 2012
- **Hammersley-Welsh bridge decomposition** (#3): Hammersley & Welsh, 1962

## Recent Changes

- **Decomposed `strip_identity_genuine`**: Now proved from `B_paper_le_one_strip`.
  The existential statement (∃ A, E ≥ 0, 1 = c_α·A + B + c_ε·E) is derived
  from the simpler bound B_paper ≤ 1 by taking A = (1-B)/c_α, E = 0.
- **Proved `A_inf_1_exact`**: The exact value A_inf(1, xc) = 2xc³/(1-xc²)
  is now proved (was sorry'd in SAWInfStripT1.lean).

## Proved Infrastructure (sorry-free or depends only on the 3 root sorries)

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

### Strip Identity (SAWStripIdentityCorrect.lean)
- PaperInfStrip, PaperFinStrip, PaperSAW_A/B/E definitions ✓
- Finiteness of PaperSAW_B ✓
- Non-negativity lemmas ✓
- `strip_identity_genuine` ✓ (from B_paper_le_one_strip)
- `B_paper_le_one_direct` ✓ (from strip_identity_genuine)

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved` ✓ (depends on B_paper_le_one_strip through
  paper_bridge_partial_sum_le)

### Bridge Recurrence (SAWRecurrenceProof.lean)
- `bridge_recurrence_proved` ✓ (depends on infinite_strip_identity +
  cutting_argument_proved)

### Quadratic Recurrence Lower Bound (SAWDecomp.lean)
- `quadratic_recurrence_lower_bound` ✓
- `harmonic_not_summable` ✓

### T=1 Special Cases
- `paper_bridge_partition_1_eq` ✓
- `strip_identity_genuine_T1'` ✓
- `A_inf_1_exact` ✓

### Lower Counting Bounds (SAWZigzagBuild.lean)
- `saw_count_even_lower_proved`, `saw_count_sq_ge_two_pow_proved` ✓

### Paper Chain (SAWPaperChain.lean)
- All proved modulo the three root sorries ✓
- `connective_constant_eq_corrected` ✓ (modulo root sorries)

## Non-Critical Sorries (Dead Code / Superseded)

These sorries are in files that are NOT on the critical path for the main theorem,
or are superseded by proved versions:
- `cutting_argument` (SAWCutting.lean) — superseded by cutting_argument_proved
- `origin_bridge_lower_bound` (SAWHWInject, SAWHammersleyWelsh, SAWStripIdentity) —
  superseded by paper_bridge_lower_bound in SAWPaperChain
- `Z_xc_diverges` (SAWHWBridge.lean) — superseded by Z_xc_diverges_corrected
- `bridge_decomp_injection_from_algorithm` (SAWHWAlgorithm.lean) — different
  formulation using origin_bridge_partition, superseded by paper_bridge_decomp_injection
- `boundary_sum_identity` (SAWStripProofDirect.lean) — equivalent to B_paper_le_one_strip
- `vertex_relation_observable` (SAWStokesSkeleton.lean) — partial infrastructure
- `strip_identity_concrete` (SAWFiniteStrip.lean) — alternative formulation
- Various duplicate formulations in SAWBridgeDecomp, SAWBridgeDecompCore,
  SAWHWDecomp, SAWHWDecompNew
