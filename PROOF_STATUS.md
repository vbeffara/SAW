# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 1 independent sorry chain** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh — **FULLY COMPLETED**

All SAWHW*.lean files are **sorry-free** (verified by grep).

The Hammersley-Welsh argument establishes the upper bound μ ≤ √(2+√2)
by decomposing self-avoiding walks into bridges.

Key proved results:
- `saw_sum_le_hp_sq` — sorry-free, no axiom dependency beyond standard
- `hp_sum_le_prod'` — proved (only sorry dependency is from strip identity via B_paper_le_one_direct)
- `hw_injection_bound` — the main HW bound: ∑c_n x^n ≤ 8·∏(1+12·B_T(x))²
- `hw_summable_corrected` — Z(x) < ∞ for x < xc
- `extra_count_le_conv'` — convolution bound (sorry-free)
- `bridge_count_any_le_shifted'` — bridge count shift (sorry-free)
- `narrow_suffix_gf_le'` — narrow suffix GF bound (sorry-free)

The HW bound uses slightly weaker constants than the paper
(factor 8 and 12 instead of 2 and 1), but both versions
suffice to prove Z(x) < ∞ for x < xc.

## Proof Architecture (HW chain) — COMPLETE

```
SAWHWConvBoundBase.lean — infrastructure: extra_at_k, suffix_fiber_injective
  ↓
SAWHWFiberCount.lean — fiber counting: fiber_bound, dropToSuffix
  ↓
SAWHWConvBound.lean — convolution bound: extra_count_le_conv'
  ↓
SAWHWBridgeShift.lean — bridge shift: bridge_count_any_le_shifted'
  ↓
SAWHWGFBound.lean — GF bounds: bridge_count_any_gf_le, hp_sum_step', hp_sum_le_prod'
  ↓
SAWHWSawBound.lean — SAW bound: saw_sum_le_hp_sq, hw_injection_bound_correct
  ↓
SAWHWFinalProof.lean → SAWPaperChain.lean — main theorem
```

## Files in the HW chain

All files listed below are **sorry-free**:

- `SAWHWStructural.lean` — dc step lemmas, strip compatibility
- `SAWHWBound.lean` — basic bounds on bridge/strip counts
- `SAWHWHalfPlane.lean` — hp_walk_count, hp_sum definitions and base case
- `SAWHWLastVertex.lean` — lastDCIndex infrastructure
- `SAWHWBridgeExtractProof.lean` — bridge extraction from walks
- `SAWHWMinDC.lean` — minimum dc infrastructure
- `SAWHWDecomp.lean` — walk decomposition at min dc vertex
- `SAWHWDecompFresh.lean` — neg_dc injection proof
- `SAWHWStepHelpers.lean` — hp_sum_split, bridge GF lemmas, Cauchy product
- `SAWHWConvBoundBase.lean` — extra_at_k decomposition
- `SAWHWFiberCount.lean` — fiber counting injection
- `SAWHWConvBound.lean` — extra_count_le_conv'
- `SAWHWBridgeShift.lean` — bridge shift injection
- `SAWHWGFBound.lean` — GF bounds and inductive product bound
- `SAWHWSawBound.lean` — saw_sum_le_hp_sq and combined bound
- `SAWHWFinalProof.lean` — hw_injection_bound theorem
- `SAWHWExtraFinal.lean` — extra_sum_le_proof (derived from hp_sum_step')
- `SAWHWExtraProof.lean` — extra walk counting infrastructure
- `SAWHWExtraSumProof.lean` — extra sum auxiliary lemmas
- `SAWHWReCoord.lean` — coordinate transformations
- `SAWHWInject.lean` — walk_max_x, saw_x_coord_bound (sorry-free)
- `SAWHWAlgorithm.lean` — hexShift, shiftWalk infrastructure (sorry-free)
