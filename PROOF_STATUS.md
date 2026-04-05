# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main Theorem

**`connective_constant_eq_corrected`** (SAWPaperChain.lean): μ = √(2+√2)

**Status: INCOMPLETE** — depends on 3 sorry'd lemmas (see below).

## Critical Architectural Fix

The original `OriginBridge` and `origin_bridge_partition` in SAWBridgeFix.lean
use **x-coordinate strips**. The paper's strip identity B ≤ 1 uses **diagonal strips**
(aligned with Re(z) in the embedding).

**`origin_bridge_partition T xc ≤ 1` is FALSE** for x-coordinate bridges!
For T=1: xc + 4xc³ ≈ 1.18 > 1.

The corrected chain in **SAWPaperChain.lean** uses `PaperBridge` (diagonal bridges
matching the paper's convention). The corrected bridge partition satisfies
`paper_bridge_partition T xc ≤ 1/xc` (proved modulo B_paper_le_one_direct).

## Proof Architecture (Corrected)

The proof follows Duminil-Copin & Smirnov (2012):
1. **Lower bound** (Z(x_c) = ∞): Strip identity → paper bridge lower bound → harmonic series divergence
2. **Upper bound** (Z(x) < ∞ for x < x_c): Paper bridge decomposition → bridge decay → product convergence

### Critical Path Sorry's

#### 1. B_paper_le_one_direct (THE FUNDAMENTAL GAP)
**File:** SAWStripIdentityCorrect.lean
**Statement:** B_paper T L xc ≤ 1 for T ≥ 1, L ≥ 1
**Proof outline:** Sum vertex relation over strip vertices → discrete Stokes → boundary sum = 0 → B ≤ 1
**Infrastructure proved:**
- pair_cancellation ✅
- triplet_cancellation ✅
- boundary_cos_pos ✅
- interior_cancellation ✅
- B_paper_le_one_from_partial_bound ✅ (reduces to partial sum bounds)
- paperSAW_B_length_ge ✅ (walk length ≥ T)
- B_paper_fintype_sum ✅ (B_paper is a finite sum)
**Infrastructure still needed:**
- Parafermionic observable F(z) definition
- Vertex relation at each strip vertex (walk pair/triplet matching)
- Discrete Stokes theorem (boundary sum = 0)
- Boundary type evaluation

#### 2. paper_bridge_lower_bound
**File:** SAWPaperChain.lean
**Statement:** ∃ c > 0, ∀ T ≥ 1, c/T ≤ paper_bridge_partition T xc
**Depends on:** B_paper_le_one_direct (via strip identity and quadratic recurrence)

#### 3. paper_bridge_decomp_injection
**File:** SAWPaperChain.lean  
**Statement:** Σ c_n x^n ≤ 2·(Σ_S Π paper_bridge_partition(T+1, x))²
**Status:** Sorry. This is the Hammersley-Welsh (1962) decomposition.

### Fully Proved Components (no sorry in transitive closure)

| File | Result | Status |
|------|--------|--------|
| SAW.lean | pair_cancellation, triplet_cancellation | ✅ |
| SAW.lean | Fekete's lemma | ✅ |
| SAW.lean | hex lattice definitions | ✅ |
| SAWSubmult.lean | Submultiplicativity c_{n+m} ≤ c_n · c_m | ✅ |
| SAWMain.lean | Connective constant is a limit | ✅ |
| SAWMain.lean | Connective constant is positive | ✅ |
| SAWLowerCount.lean | μ ≥ √2 | ✅ |
| SAWQuadRecurrence.lean | Quadratic recurrence lower bound | ✅ |
| SAWStripIdentityCorrect.lean | boundary_cos_pos | ✅ |
| SAWVertexRelation.lean | paperSAW_B_length_ge, B_paper_fintype_sum | ✅ |
| SAWVertexRelation.lean | B_paper_le_one_from_partial_bound | ✅ |
| SAWDiagProof.lean | paperBridgeToSAWB_injective | ✅ |
| SAWDiagProof.lean | paper_bridge_partial_sum_shifted_le | ✅ (modulo B_paper_le_one_direct) |
| SAWDiagProof.lean | paper_bridge_partial_sum_le | ✅ (modulo B_paper_le_one_direct) |
| SAWDiagProof.lean | paper_bridge_upper_bound | ✅ (modulo B_paper_le_one_direct) |
| SAWPaperChain.lean | paperBridge_toSAW_sigma_injective | ✅ |
| SAWPaperChain.lean | paper_bridge_filter_card_le | ✅ |
| SAWPaperChain.lean | paper_bridge_decay_corrected | ✅ (modulo B_paper_le_one_direct) |
| SAWPaperChain.lean | Z_xc_diverges_corrected | ✅ (modulo paper_bridge_lower_bound) |
| SAWPaperChain.lean | connective_constant_eq_corrected | ✅ (modulo all sorry's) |

### Old Chain Sorry's (superseded by corrected chain)

The original `origin_bridge_upper_bound` is **FALSE** (see above).
The corrected chain in SAWPaperChain.lean supersedes:
- SAWBridgeFix.lean: origin_bridge_upper_bound, origin_bridge_lower_bound
- SAWHWDecomp.lean: bridge_decomposition_injection_proof
- SAWHammersleyWelsh.lean: hammersley_welsh_summable
- SAWStripIdentity.lean: Z_xc_diverges_from_lower_bound
- SAWFinal.lean: connective_constant_eq
