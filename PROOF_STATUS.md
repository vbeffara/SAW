# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent root sorries** (see below).

## Root Sorries (2 independent)

### Sorry #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
```lean
1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
```
The parafermionic observable identity for the infinite strip, for all T ≥ 1.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

**Also implies** `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385):
```lean
B_paper T L xc ≤ 1
```
The core bound from the parafermionic observable for the finite strip.

### Sorry #2: `hw_injection_bound` (SAWHWFinalProof.lean:76)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
  2 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2
```
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

## Proof Architecture

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
    ├── hw_injection_bound ← SORRY #2
    └── paper_bridge_decay [B_T(x) ≤ (x/xc)^T / xc]
        └── paper_bridge_partial_sum_le [partial sums ≤ 1/xc]
            └── B_paper_le_one_strip ← (consequence of SORRY #1)
```

## Alternative Proof Path (SAWMainNew.lean)
`connective_constant_eq_direct`: Only requires `infinite_strip_identity` (sorry #1),
avoiding the HW decomposition entirely. Uses submultiplicativity for the upper bound.
Has its own sorries: `saw_count_exp_bound`, `hw_summable_direct`.

## File Summary (32 files, ~5900 lines)

### Core definitions (SAW.lean, SAWStrip.lean)
- HexVertex, hexGraph, SAW, saw_count, connective_constant
- xc, c_alpha, c_eps, pair_cancellation, triplet_cancellation
- Fekete's lemma, abstract bridge bounds

### Submultiplicativity chain
- SAWSubmult.lean → SAWMain.lean → SAWBridge.lean → SAWBridgeFix.lean

### Strip identity chain  
- SAWStripIdentityCorrect.lean → SAWStripIdentityProof.lean
- SAWDiagBridge.lean → SAWDiagConnection.lean → SAWDiagProof.lean

### Cutting argument chain
- SAWCutting.lean → SAWCuttingHelpers.lean → SAWCuttingProof.lean
- SAWParafermionic.lean, SAWWalkHelpers.lean

### Recurrence and lower bound
- SAWRecurrenceProof.lean, SAWDecomp.lean

### Strip T=1 computations
- SAWStripT1Walks.lean → SAWStripT1Exact.lean

### Hammersley-Welsh development
- SAWHWInject.lean → SAWHWAlgorithm.lean
- SAWHWStructural.lean, SAWHWBridgeExtractProof.lean
- SAWHWReCoord.lean, SAWHWBound.lean
- SAWHWDecompFresh.lean (structural lemmas for bridge extraction)
- SAWHWFinalProof.lean

### Assembly
- SAWPaperChain.lean (main theorem)
- SAWFinal.lean (convenience wrapper)
- SAWMainNew.lean (alternative proof path)
- SAWElementary.lean (misc helpers)
