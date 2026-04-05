# Proof Status: The connective constant of the honeycomb lattice equals √(2+√2)

## Main Theorem

**`connective_constant_eq`** (SAWFinal.lean): μ = √(2+√2)

**Status: INCOMPLETE** — depends on 3 sorry'd lemmas (see below).

## Proof Architecture

The proof follows Duminil-Copin & Smirnov (2012):
1. **Lower bound** (Z(x_c) = ∞): Strip identity → bridge lower bound → harmonic series divergence
2. **Upper bound** (Z(x) < ∞ for x < x_c): Bridge decomposition → bridge decay → product convergence

### Critical Path Sorry's

#### 1. B_paper_le_one_direct (THE FUNDAMENTAL GAP)
**File:** SAWStripIdentityCorrect.lean:311
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

#### 2. origin_bridge_upper_bound and origin_bridge_lower_bound
**File:** SAWBridgeFix.lean:180, 186
**Depends on:** B_paper_le_one_direct (via strip identity)

#### 3. bridge_decomposition_injection_proof (INDEPENDENT)
**File:** SAWHWDecomp.lean:103
**Statement:** Hammersley-Welsh decomposition: Σ c_n x^n ≤ 2·(Σ_S Π B_{T+1}^x)²

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

### Proved Modulo B_paper_le_one_direct

| File | Result |
|------|--------|
| SAWHammersleyWelsh.lean | origin_bridge_decay, hw_upper_bound_abstract |
| SAWHammersleyWelsh.lean | hammersley_welsh_summable |
| SAWStripIdentity.lean | Z_xc_diverges_from_lower_bound |
| SAWFinal.lean | connective_constant_eq |

### Non-Critical Sorry's (superseded or not on critical path)

| File:Line | Declaration | Status |
|-----------|-------------|--------|
| SAWBridge.lean:353 | hammersley_welsh_bound | Superseded |
| SAWBridgeFix.lean:203 | Z_xc_diverges | Superseded |
| SAWBridgeFix.lean:224 | hammersley_welsh_injection | Superseded |
| SAWFiniteStrip.lean:286 | B_T_inf_eq_origin_bridge | Not on critical path |
| SAWFiniteStrip.lean:376 | origin_bridge_partial_sum_le_one | Not on critical path |
| SAWHWAlgorithm.lean:242 | bridge_decomp_injection_from_algorithm | Duplicate of HWDecomp |
