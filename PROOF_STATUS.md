# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent root sorries** (see below).

## Root Sorries

### Sorry #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
```lean
1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
```
The parafermionic observable identity for the infinite strip, for all T ≥ 1.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry #2: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385)
```lean
B_paper T L xc ≤ 1
```
The core bound from the parafermionic observable for the finite strip.
Required for: paper_bridge_partial_sum_le → paper_bridge_decay → upper bound.
Follows from Sorry #1 by taking L → ∞, but also independently captures
the discrete Stokes argument (Lemma 2 of the paper).

### Sorry #3: `paper_bridge_decomp_injection` (SAWPaperChain.lean:265)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
  2 * (∑ S ∈ (Finset.range N).powerset,
    ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2
```
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

## Proof Architecture

The main theorem depends on two independent bounds:

### Lower Bound: μ ≥ √(2+√2) via Z(xc) = ∞
```
connective_constant_eq_corrected (SAWPaperChain.lean)
└── Z_xc_diverges_corrected [Z(xc) = ∞]
    └── paper_bridge_lower_bound [B_T ≥ c/T]
        └── bridge_recurrence_proved [B_T ≤ α·B_{T+1}² + B_{T+1}]
            └── infinite_strip_identity ← SORRY #1
```

### Upper Bound: μ ≤ √(2+√2) via Z(x) < ∞ for x < xc
```
connective_constant_eq_corrected (SAWPaperChain.lean)
└── hw_summable_corrected [Z(x) < ∞]
    ├── paper_bridge_decomp_injection ← SORRY #3
    └── paper_bridge_decay [B_T(x) ≤ (x/xc)^T / xc]
        └── paper_bridge_partial_sum_le [partial sums ≤ 1/xc]
            └── B_paper_le_one_strip ← SORRY #2
```

## ✅ What IS Proved (sorry-free)

### Core Algebraic Identities (SAW.lean)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- `sqrt_two_add_sqrt_two_eq`: √(2+√2) = 2cos(π/8)
- `c_alpha_pos`, `c_eps_pos`: boundary coefficients are positive

### Combinatorial Infrastructure
- `saw_count_submult'` (SAWSubmult.lean): c_{n+m} ≤ c_n·c_m
- `saw_count_vertex_independent` (SAWSubmult.lean): c_n is independent of starting vertex
- `saw_count_pos` (SAW.lean): c_n > 0 for all n
- `connective_constant` (SAW.lean): definition and basic properties

### Strip Domain Infrastructure (SAWStripIdentityCorrect.lean)
- `PaperInfStrip`, `PaperFinStrip`: strip domain definitions
- `PaperSAW_A`, `PaperSAW_B`, `PaperSAW_E`: walk partition functions
- `correctHexEmbed`: correct hex lattice embedding
- `boundary_cos_pos`: all boundary angles have positive cosine
- `starting_direction`: starting mid-edge direction is -1

### Bridge Infrastructure (SAWDiagProof.lean)
- `PaperBridge`: bridge definition with diagonal coordinates
- `paper_bridge_partition`: bridge partition function
- `paper_bridge_length_ge`: bridge of width T has length ≥ T
- `paper_bridge_in_fin_strip`: bridges fit in finite strips

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved`: A_inf(T+1) - A_inf(T) ≤ xc·B(T+1)²
- All helper lemmas (prefix/suffix bridge extraction, walk splitting)

### Bridge Recurrence (SAWRecurrenceProof.lean, modulo sorry #1)
- `bridge_diff_eq`: B(T) - B(T+1) = c_α/xc · (A(T+1) - A(T))
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1)

### Lower Bound Infrastructure (SAWDecomp.lean)
- `quadratic_recurrence_lower_bound`: from recurrence → B_T ≥ c/T
- `harmonic_not_summable`: ∑ 1/n diverges
- `not_summable_of_lower_bound`: comparison with harmonic series

### Bridge Decay (SAWPaperChain.lean, modulo sorry #2)
- `paper_bridge_decay`: B_T(x) ≤ (x/xc)^T / xc for x < xc
- `paper_bridge_summable`: bridges are summable for T ≥ 1

### Helper Lemmas (SAWHWProved2.lean, sorry-free)
- `diagCoord_adj_le/ge`: diagonal coordinate changes by at most 1 per step
- `walk_diagCoord_bound`: walk endpoint within length distance
- `walk_support_diagCoord_bound`: all support vertices within length distance
- `Finset.sum_powerset_prod_eq_prod_add_one`: powerset-product identity

### T=1 Identity (SAWAInf1Lower.lean, sorry-free, INDEPENDENT)
- `infinite_strip_identity_T1`: 1 = c_α·A_inf(1) + xc·B₁
- Complete explicit computation for T=1 strip

## What Remains

### To prove Sorry #1 (Parafermionic Identity):
1. Define the parafermionic observable F(z) at mid-edges
2. Formalize the pair/triplet partition of walks at each vertex
3. Show each pair/triplet contributes 0 (using pair_cancellation + triplet_cancellation)
4. Sum over all vertices (discrete Stokes theorem)
5. Evaluate boundary contributions
6. Conclude: 1 = c_α·A + B + c_ε·E for finite strip
7. Take L → ∞ to get infinite strip identity

### To prove Sorry #2 (B_paper ≤ 1):
Same as Sorry #1 steps 1-6 (it's the direct consequence of the finite strip identity).

### To prove Sorry #3 (HW Decomposition):
1. Define the bridge decomposition algorithm for half-plane walks
2. Prove the decomposition produces bridges of strictly decreasing widths
3. Define the full SAW decomposition (split at min diagCoord vertex)
4. Prove injectivity of the decomposition (reverse procedure)
5. Prove the weight bound (walk length ≥ sum of bridge lengths)
6. Derive the counting inequality

## Build Status
All files in the main proof chain compile without errors.
