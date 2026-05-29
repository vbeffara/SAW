# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 1 independent sorry chain** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh — **COMPLETED**

All 3 root sorries in the Hammersley-Welsh chain have been proved:

1. **`extra_at_k_le_prod_lt`** (SAWHWConvBound.lean) — ✅ PROVED
   The fiber counting argument: extra walks with lastDCIndex = k inject into
   bridge_count_any(W+1, k) × narrow_suffix_count(W, n-k).
   Uses `fiber_bound` from SAWHWFiberCount.lean.

2. **`bridge_count_any_le_shifted`** (SAWHWGFBound.lean) — ✅ PROVED
   TRUE-endpoint bridges of length k truncate to FALSE-endpoint bridges of length k-1.
   Uses `bridge_count_any_le_shifted'` from SAWHWBridgeShift.lean.

3. **`bridge_count_any_gf_le`** (SAWHWGFBound.lean) — ✅ PROVED
   GF of bridge_count_any ≤ (1+x) · paper_bridge_partition.
   Follows from #2 via algebraic manipulation.

## Proof Architecture (HW chain) — COMPLETE

```
SAWHWConvBoundBase.lean (infrastructure: extra_at_k, suffix_fiber_injective, etc.)
  ↓
SAWHWFiberCount.lean (imports SAWHWConvBoundBase)
  fiber_bound [PROVED] — injection from fiber to relaxed suffix set
  dropToSuffix, dropToSuffix_injective, dropToSuffix_relaxed [ALL PROVED]
  ↓
SAWHWConvBound.lean (imports SAWHWConvBoundBase + SAWHWFiberCount)
  extra_at_k_le_prod_lt [PROVED] — uses fiber_bound + biUnion argument
  extra_at_k_le_prod [PROVED]
  extra_count_le_conv_nat [PROVED]
  extra_count_le_conv' [PROVED]
  ↓
SAWHWBridgeShift.lean (imports SAWHWStepHelpers)
  bridge_count_any_le_shifted' [PROVED] — TRUE bridge truncation injection
  truncateTrueBridge, truncateTrueBridge_is_bridge, truncateTrueBridge_injective [ALL PROVED]
  ↓
SAWHWGFBound.lean (imports SAWHWConvBound + SAWHWBridgeShift)
  bridge_count_any_le_shifted [PROVED]
  bridge_count_any_gf_le [PROVED]
  extra_sum_le [PROVED]
  hp_sum_step' [PROVED]
  hp_sum_le_prod' [PROVED]
  ↓
SAWHWSawBound.lean → SAWHWFinalProof.lean → SAWPaperChain.lean
  All downstream lemmas: [PROVED from HW chain]
```

## New files created for the HW proof

- `SAWHWConvBoundBase.lean` — Infrastructure extracted from SAWHWConvBound (definitions, suffix_fiber_injective, etc.)
- `SAWHWFiberCount.lean` — Fiber counting proof (fiber_bound and helpers)
- `SAWHWBridgeShift.lean` — Bridge count any ≤ bridge count + shifted bridge count
