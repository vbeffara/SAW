# Proof Status: The Connective Constant of the Honeycomb Lattice

## Main Theorem

`connective_constant_eq` (SAWFinal.lean): μ = √(2+√2)

**Status: PROVED modulo 2 sorry's** (see below)

## Fully Proved Components

All of the following compile without sorry:

### Core Definitions (SAW.lean)
- `hexGraph`, `hexOrigin`, `paperStart` — hexagonal lattice
- `SAW` — self-avoiding walk type
- `saw_count` — number of n-step SAWs from origin
- `xc`, `lam`, `j`, `sigma` — critical constants
- `pair_cancellation`, `triplet_cancellation` — algebraic core identities
- `xc_pos`, `c_alpha_pos`, `c_eps_pos`

### Submultiplicativity (SAWSubmult.lean)
- `saw_count_submult'` — c_{n+m} ≤ c_n · c_m

### Connective Constant (SAWMain.lean)
- `fekete_submultiplicative` — Fekete's lemma
- `connective_constant_is_limit'` — c_n^{1/n} → μ
- `connective_constant_pos'` — μ > 0

### Bridge Infrastructure (SAWBridge.lean, SAWBridgeFix.lean)
- `Bridge`, `OriginBridge`, `PaperBridge` — bridge definitions
- `origin_bridge_partition`, `paper_bridge_partition` — partition functions
- `partition_converges_below_inv_cc` — Z(x) < ∞ for x < 1/μ
- `partition_diverges_above_inv_cc` — Z(x) = ∞ for x > 1/μ
- `cc_eq_inv_of_partition_radius` — μ = 1/x₀ from radius of convergence
- `connective_constant_eq_from_bounds` — main theorem reduction

### Strip Domain (SAWStripIdentityCorrect.lean)
- `PaperInfStrip`, `PaperFinStrip` — strip domains
- `PaperSAW_A_inf`, `PaperBridge` — walk types in strips

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved` — A_{T+1} - A_T ≤ xc · B_{T+1}²

### Bridge Recurrence (SAWRecurrenceProof.lean, modulo strip identity)
- `bridge_recurrence_proved` — B_T ≤ c_α B_{T+1}² + B_{T+1}
- `paper_bridge_recurrence_derived` — existential form

### Bridge Bounds (SAWPaperChain.lean, SAWDiagProof.lean)
- `paper_bridge_lower_bound` — ∃ c > 0, B_T ≥ c/T
- `paper_bridge_decay` — B_T(x) ≤ (x/xc)^T / xc for x < xc
- `paper_bridge_partial_sum_le` — partial sums of B bounded by 1/xc

### Divergence (SAWPaperChain.lean)
- `Z_xc_diverges_corrected` — Z(xc) = ∞ (modulo strip identity)

### Convergence (SAWPaperChain.lean)
- `hw_summable_corrected` — Z(x) < ∞ for x < xc (modulo HW decomp)

### Algebraic/Geometric Infrastructure
- `pair_cancellation_geometric`, `triplet_cancellation_geometric` (SAWPairTriplet.lean)
- `interior_edge_cancel`, direction sum lemmas (SAWVertexRelProof.lean)
- `correctHexEmbed`, boundary direction lemmas (SAWParafermionicCore.lean)

### HW Decomposition Infrastructure (SAWHWCore.lean) — NEW
- `diagCoordZ_adj_bound` — edge changes diagCoord by ≤ 1
- `walk_diagCoordZ_bound` — walk stays within length of start
- `walkMinDiagCoord_le` — minimum is a lower bound
- `walkMinDiagCoord_achieved` — minimum is achieved
- `hw_bridge_length_ge` — bridge length ≥ width
- `walk_split_at_vertex` — splitting preserves length
- `dropUntil_min_diagCoord` — suffix preserves min diagCoord
- `pow_le_prod_pow` — weight bound x^n ≤ ∏ x^{l_i}

### Elementary Bounds
- `saw_count_pos`, `saw_count_one`, `saw_count_two` — small values
- `saw_count_vertex_independent` — translation invariance
- Various zigzag/lower bound constructions

## Remaining Sorry's (2)

### 1. `infinite_strip_identity` (SAWRecurrenceProof.lean)
```
1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
```
**What it says**: The parafermionic observable identity for the infinite strip.

**What's needed**: The pair/triplet partition of walks at each vertex
of the strip, and the discrete Stokes summation that telescopes to
give the boundary identity.

**Algebraic prerequisites**: PROVED (pair_cancellation, triplet_cancellation)

**Impact**: Feeds into bridge recurrence → lower bound → Z(xc) = ∞ → μ ≥ 1/xc

### 2. `paper_bridge_decomp_injection` (SAWPaperChain.lean)
```
∑ n ∈ range(N+1), c_n * x^n ≤ 2 * (∑ S ∈ range(N).powerset, ∏ T ∈ S, B_{T+1}(x))²
```
**What it says**: The Hammersley-Welsh bridge decomposition counting inequality.

**What's needed**: The half-plane walk bridge decomposition algorithm,
its injectivity proof, and the weight bound.

**Infrastructure**: Key helper lemmas proved in SAWHWCore.lean.

**Impact**: Feeds into convergence → Z(x) < ∞ for x < xc → μ ≤ 1/xc
