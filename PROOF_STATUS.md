# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (2 root sorries)

**2a. `extra_sum_le`** (SAWHWStepHelpers.lean:160)
The generating function bound for extra walks:
```lean
∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x
```
Requires constructing an injection from "extra walks" (visiting dc=-(W+1))
to (bridge prefix, suffix) pairs, and bounding the suffix GF by 6·hp_sum(W).
The injection splits at the last FALSE vertex at dc=-(W+1).

**2b. `saw_neg_le_hp_conv`** (SAWHWSawBound.lean:66)
SAWs visiting dc < 0 are bounded by the convolution of hp_walk_counts:
```lean
(saw_count_neg_dc n : ℝ) ≤
    ∑ k ∈ Finset.range (n + 1), (hp_walk_count N k : ℝ) * (hp_walk_count N (n - k) : ℝ)
```
Requires constructing an injection from SAWs visiting dc < 0 to pairs of
half-plane walks, using the decomposition at the first vertex of minimum dc.
The key is that each half stays in a strip of width ≤ k (resp. n-k) ≤ N,
which follows from the dc range lemma (walk_getVert_dc_diff).

## Proof Architecture

### Upper Bound: μ ≤ √(2+√2) via Z(x) < ∞ for x < xc
```
connective_constant_eq_corrected
└── hw_summable_corrected ✓
    └── paper_bridge_decomp_bound ✓
        └── hw_injection_bound ✓
            └── hw_injection_bound_correct ✓  (SAWHWSawBound.lean)
                ├── saw_sum_le_hp_sq ✓  (SAWHWSawBound.lean)
                │   ├── saw_count_split ✓
                │   ├── saw_nonneg_le_hex_strip ✓
                │   ├── hex_origin_strip_sum_le ✓
                │   ├── hp_sum_ge_one_plus_x ✓
                │   ├── cauchy_product_le ✓
                │   └── saw_neg_le_hp_conv ← SORRY #2b
                └── hp_sum_le_prod ✓  (SAWHWStepHelpers.lean)
                    ├── hp_sum_zero_le ✓
                    └── hp_sum_step ✓
                        └── extra_sum_le ← SORRY #2a
    └── paper_bridge_decay ✓

### Lower Bound: μ ≥ √(2+√2) via Z(xc) = ∞
connective_constant_eq_corrected
└── Z_xc_diverges_corrected
    └── paper_bridge_lower_bound
        └── bridge_recurrence_proved
            └── infinite_strip_identity ← SORRY #1
```

## Infrastructure proved in this session

### File restructuring
- Moved `hp_sum_step`, `hp_sum_le_prod` from SAWHWHalfPlane.lean to SAWHWStepHelpers.lean
  (eliminates circular dependency)
- Moved `saw_sum_le_hp_sq`, `hw_injection_bound_correct` from SAWHWHalfPlane.lean to SAWHWSawBound.lean
- Updated SAWHWFinalProof.lean imports accordingly
- SAWHWHalfPlane.lean now contains only definitions and base case proofs

### New proofs in SAWHWSawBound.lean
1. `cauchy_product_le` ✓ — Truncated convolution ≤ product of truncated sums
2. `hp_walk_count_one_ge` ✓ — hp_walk_count(W, 1) ≥ 1
3. `hp_sum_ge_one_plus_x` ✓ — hp_sum(N, N, x) ≥ 1 + x for N ≥ 1
4. `saw_sum_le_hp_sq` ✓ — ∑c_n x^n ≤ 2·hp_sum(N)² (the full SAW-to-halfplane reduction)
5. `hw_injection_bound_correct` ✓ — ∑c_n x^n ≤ 8·(∏(1+6B_T))²

### New proofs in SAWHWStructural.lean
1. `walk_getVert_dc_le` ✓ — dc(getVert i) ≤ dc(start) + i
2. `walk_getVert_dc_ge` ✓ — dc(getVert i) ≥ dc(start) - i
3. `walk_getVert_dc_diff` ✓ — dc(getVert j) - dc(getVert i) ≤ j - i
4. `walk_getVert_dc_diff'` ✓ — dc(getVert i) - dc(getVert j) ≤ j - i

## What remains to formalize

Both remaining sorries require constructing **explicit walk decomposition injections**
in Lean. The mathematical arguments are clear:

### For `extra_sum_le`:
Split each "extra walk" at the last FALSE vertex at dc=-(W+1). The prefix is a bridge
of width W+1. The suffix (from FALSE at dc=-(W+1)) has at most 3 first-step choices,
then enters dc ∈ [-W, 0]. After translate+flip, suffix maps to walks bounded by
hex_origin_strip_count(W, ·). The suffix GF ≤ (1+3x+2x²)·hp_sum(W) ≤ 6·hp_sum(W).

### For `saw_neg_le_hp_conv`:
Split the SAW at firstMinDCIdx. The prefix (reversed + translate + flip) gives
a walk from paperStart in strip [-k, 0] ⊆ [-N, 0]. The suffix (translate + flip)
gives a walk from paperStart in strip [-(n-k), 0] ⊆ [-N, 0]. The strip bounds
follow from prefix_dc_upper_bound/suffix_dc_upper_bound. The map is injective
because all transforms are bijective and the original walk = prefix.append(suffix).

### Technical challenge:
The difficulty is not mathematical but FORMAL: constructing Lean functions
`SAW → SAW × SAW` that compose walk operations (take, drop, reverse, translate, flip)
while carrying the necessary type-level proofs (IsPath, length, strip constraints).
The dc range infrastructure (walk_getVert_dc_diff) is fully proved, providing the
mathematical foundation for the strip constraint proofs.
