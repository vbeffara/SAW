# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (3 root sorries)

The HW chain proves Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).
Architecture has been fixed to use `bridge_count_any` directly (avoiding the
FALSE parity issue), with constant 12 instead of 6.

**Root sorries (3):**

1. **`extra_at_k_le_prod_lt`** (SAWHWConvBound.lean:145)
   The fiber counting argument: extra walks with lastDCIndex = k inject into
   bridge_count_any(W+1, k) × narrow_suffix_count(W, n-k).
   Requires: constructing the (take, drop) injection and bounding fibers.

2. **`bridge_count_any_le_shifted`** (SAWHWGFBound.lean:23)
   TRUE-endpoint bridges of length k truncate to FALSE-endpoint bridges of length k-1.
   Uses: the only in-strip FALSE neighbor of TRUE v at dc=-T is (v.1, v.2.1, false).

3. **`bridge_count_any_gf_le`** (SAWHWGFBound.lean:30)
   GF of bridge_count_any ≤ (1+x) · paper_bridge_partition.
   Follows from #2 via ∑_k bridge_count_any(T,k)*x^k ≤ (1+x)*∑_k bridge_count(T,k)*x^k.

## Proof Architecture (HW chain)

```
SAWHWConvBound.lean
  extra_at_k_le_prod_lt [SORRY] → extra_at_k_le_prod → extra_count_le_conv_nat → extra_count_le_conv'

SAWHWGFBound.lean (imports SAWHWConvBound)
  bridge_count_any_le_shifted [SORRY]
  bridge_count_any_gf_le [SORRY]
  extra_sum_le → hp_sum_step' → hp_sum_le_prod'

SAWHWSawBound.lean (imports SAWHWGFBound)
  saw_sum_le_hp_sq [PROVED]
  hw_injection_bound_correct [PROVED from hp_sum_le_prod']

SAWHWFinalProof.lean → SAWPaperChain.lean
  hw_injection_bound → paper_bridge_decomp_bound → hw_summable_corrected
  → connective_constant_eq_corrected [PROVED modulo sorries]
```

## Proved infrastructure for the HW chain

- `extra_count_eq_sum`: partition extra walks by lastDCIndex value
- `extra_at_k_le_prod_eq`: case k=n (trivial walk = bridge)
- `suffix_drop_narrow`: suffix after lastDCIndex stays in [-W, 0]
- `saw_eq_of_support`: SAWs are determined by their support
- `walk_support_take_drop`: support = take_support ++ drop_support.tail
- `suffix_fiber_injective`: walks with same take and drop supports are equal
- `extra_sum_le`: GF bound with constant 12 (proved from sorry'd inputs)
- `hp_sum_step'`: inductive step with constant 12
- `hp_sum_le_prod'`: product bound with constant 12
- `cauchy_product_le'`: Cauchy product inequality for GFs
- All the existing infrastructure from previous sessions
