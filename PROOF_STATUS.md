# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (SAWHWHalfPlane.lean)
Three sorry'd lemmas that together give the bridge decomposition inequality.
The old monolithic sorry `hw_injection_bound` has been ELIMINATED by reducing
it to these three more specific lemmas:

**2a. `hp_sum_zero_le`** (SAWHWHalfPlane.lean:57)
```lean
hp_sum 0 N x ≤ 1 + x
```
Base case: the width-0 half-plane walk sum is at most 1+x.
(At dc=0, only the trivial walk and paperStart→(0,0,false) are possible.)

**2b. `hp_sum_step`** (SAWHWHalfPlane.lean:69)
```lean
hp_sum (W + 1) N x ≤ (1 + paper_bridge_partition (W + 1) x) * hp_sum W N x
```
Inductive step: walks in dc ∈ [-(W+1), 0] bounded by (1+B_{W+1}) · walks in [-W, 0].
Uses bridge extraction: walks reaching dc -(W+1) decompose into a PaperBridge
plus a remaining walk of smaller width.

**2c. `saw_sum_le_hp_sq`** (SAWHWHalfPlane.lean:100)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤ 2 * (hp_sum N N x) ^ 2
```
SAW partition function bounded by square of half-plane walk partition function.
Uses splitting each SAW at the first vertex of minimum diagCoord.

## What was proved in the HW chain (this session)

1. **`hw_injection_bound_correct`** (SAWHWHalfPlane.lean): The combined HW inequality
   ∑ c_n x^n ≤ 8·(∏(1+B_T))² PROVED from 2a+2b+2c above.

2. **`hp_sum_le_prod`** (SAWHWHalfPlane.lean): The inductive bound
   hp_sum(W) ≤ (1+x)·∏(1+B_T) PROVED from 2a+2b by induction on W.

3. **`hw_injection_bound`** (SAWHWFinalProof.lean): Directly invokes hw_injection_bound_correct.
   PROVED (no sorry).

4. **`hw_bridge_decomp_proved`** (SAWHWFinalProof.lean): Powerset form. PROVED.

5. **`PaperInfStrip_width_mono`** (SAWHWHalfPlane.lean): PaperInfStrip monotonicity. PROVED.

6. **`hp_walk_count_zero`** (removed): Was proved but then the definition changed.

7. **`hp_sum_nonneg`** (SAWHWHalfPlane.lean): hp_sum nonnegativity. PROVED.

The constant changed from 2 to 8 (vertex vs mid-edge formulation). The downstream
proof `hw_summable_corrected` was updated to use 8 and still proves Z(x) < ∞.

## Proof Architecture

### Lower Bound: μ ≥ √(2+√2) via Z(xc) = ∞
```
connective_constant_eq_corrected
└── Z_xc_diverges_corrected
    └── paper_bridge_lower_bound
        └── bridge_recurrence_proved
            └── infinite_strip_identity ← SORRY #1
```

### Upper Bound: μ ≤ √(2+√2) via Z(x) < ∞ for x < xc
```
connective_constant_eq_corrected
└── hw_summable_corrected
    └── paper_bridge_decomp_injection ✓ PROVED
        └── hw_bridge_decomp_proved ✓ PROVED
            └── hw_injection_bound_correct ✓ PROVED
                ├── hp_sum_le_prod ✓ PROVED (from 2a + 2b)
                │   ├── hp_sum_zero_le ← SORRY #2a
                │   └── hp_sum_step ← SORRY #2b
                └── saw_sum_le_hp_sq ← SORRY #2c
    └── paper_bridge_decay ✓ PROVED
```

## File Summary

### Core definitions
- SAW.lean — HexVertex, hexGraph, SAW, saw_count, connective_constant, xc

### Hammersley-Welsh chain (modified this session)
- **SAWHWHalfPlane.lean** — hp_walk_count, hp_sum, inductive bound, combined inequality (NEW)
- **SAWHWFinalProof.lean** — hw_injection_bound calling hw_injection_bound_correct (MODIFIED)
- SAWHWStructural.lean — dc step structure, bipartiteness, PaperInfStrip compatibility
- SAWHWBridgeExtractProof.lean — Bridge extraction from walks
- SAWHWReCoord.lean — hexReScaled coordinate
- SAWHWBound.lean — Walk dc bounds, bridge translation

### Assembly (modified this session)
- **SAWPaperChain.lean** — Main theorem, uses constant 8 (MODIFIED)
- SAWFinal.lean — Convenience wrapper
