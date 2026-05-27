# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (3 sorry's remaining, was 1)

The Hammersley-Welsh chain was significantly restructured in this session. The single
root sorry `extra_sum_le_placeholder` was decomposed into many proved lemmas and 3
remaining sorry's:

1. **`extra_walk_exists_getVert`** (SAWHWStepHelpers.lean)
   Convert support membership to getVert condition for lastDCIndex.
   Simple lemma, should be easy to prove.

2. **`extra_prefix_bridge`** (SAWHWStepHelpers.lean)  
   The prefix of an extra walk at lastDCIndex satisfies bridge conditions.
   Uses lastDCIndex_dc, lastDCIndex_is_false, walk_take_isPath.

3. **`extra_count_le_conv`** (SAWHWStepHelpers.lean)
   The counting bound: extra_count(W, n) ≤ Σ_k bridge_count(W+1, k) * narrow_suffix_count(W, n-k).
   Requires fiber counting: partition extra walks by lastDCIndex, for each k, bound by bridge_count * narrow_suffix.
   This is the hardest remaining lemma; requires constructing walk prefix as SAW and applying suffix_from_false_le.

## Proof Architecture

### Upper Bound: μ ≤ √(2+√2) via Z(x) < ∞ for x < xc
```
connective_constant_eq_corrected
└── hw_summable_corrected ✓
    └── paper_bridge_decomp_bound ✓
        └── hw_injection_bound ✓ (now uses hxc : x < xc)
            └── hw_injection_bound_correct ✓ (updated to hxc)
                ├── saw_sum_le_hp_sq ✓
                │   ├── saw_count_split ✓
                │   ├── saw_nonneg_le_hex_strip ✓
                │   ├── hex_origin_strip_sum_le ✓
                │   ├── hp_sum_ge_one_plus_x ✓
                │   ├── cauchy_product_le ✓
                │   └── saw_neg_le_hp_conv ✓
                └── hp_sum_le_prod ✓ (updated to hxc)
                    ├── hp_sum_zero_le ✓
                    └── hp_sum_step ✓ (updated to hxc)
                        └── extra_sum_le_placeholder ✓ (PROVED via decomposition)
                            ├── extra_count_le_conv ← SORRY (3 of 3)
                            │   ├── extra_walk_exists_getVert ← SORRY (1 of 3)
                            │   └── extra_prefix_bridge ← SORRY (2 of 3)
                            ├── cauchy_product_le' ✓ (NEW)
                            ├── bridge_gf_le_partition ✓ (NEW)
                            │   ├── bridge_inject_paper ✓ (NEW)
                            │   ├── bridge_summable ✓ (NEW)
                            │   └── saw_to_bridge_injective ✓ (NEW)
                            └── narrow_suffix_gf_le' ✓ (NEW)
                                ├── hex_origin_strip_sum_le' ✓ (NEW)
                                ├── narrow_suffix_count ✓ (NEW def)
                                └── suffix_from_false_le ✓ (NEW)
                                    ├── false_neighbors_in_strip ✓ (NEW)
                                    └── continuation_from_true_le' ✓

### Lower Bound: μ ≥ √(2+√2) via Z(xc) = ∞
connective_constant_eq_corrected
└── Z_xc_diverges_corrected
    └── paper_bridge_lower_bound
        └── bridge_recurrence_proved
            └── infinite_strip_identity ← SORRY #1
```

## Changes in this session

### Hypothesis change: x < 1 → x < xc
The intermediate lemmas `extra_sum_le_placeholder`, `hp_sum_step`, `hp_sum_le_prod`,
and `hw_injection_bound_correct` were changed from hypothesis `hx1 : x < 1` to
`hxc : x < xc`. This is needed because `paper_bridge_partition` (a tsum) is only
summable for `x ≤ xc`, not for all `x < 1`.

### New infrastructure proved in SAWHWStepHelpers.lean
1. **Bridge infrastructure**: `bridge_count`, `saw_to_bridge`, `saw_to_bridge_injective`,
   `bridge_summable`, `bridge_inject_paper`, `bridge_gf_le_partition`
2. **Suffix infrastructure**: `narrow_suffix_count`, `false_neighbors_in_strip`,
   `false_only_true_neighbor_at_dc_le'`, `suffix_from_false_le`,
   `contToHexOrigin'` + strip + injective, `continuation_from_true_le'`
3. **GF bounds**: `hex_origin_strip_sum_le'`, `narrow_suffix_gf_le'`, `cauchy_product_le'`
4. **Main bound**: `extra_sum_le_placeholder` proved modulo `extra_count_le_conv`

### Files modified
- `RequestProject/SAWHWStepHelpers.lean` — Major rewrite with bridge/suffix infrastructure
- `RequestProject/SAWHWSawBound.lean` — Updated `hw_injection_bound_correct` to use `hxc`
- `RequestProject/SAWHWFinalProof.lean` — Updated `hw_injection_bound` to pass `hxc` directly
