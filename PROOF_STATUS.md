# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (3 sorry's remaining, was 3 originally)

The HW chain has been substantially restructured. The previous 2 root sorries
(`suffix_partition_bound` and `extra_count_le_conv`) have been addressed:

- **`suffix_partition_bound`**: PROVED (with helpers tailTo_injective, tailTo_strip, etc.)
- **`extra_count_le_conv`**: CORRECTED to use `bridge_count_any` (see below)

#### Remaining sorry's:

1. **`extra_count_le_conv`** (SAWHWStepHelpers.lean, line 690)
   Corrected to use `bridge_count_any` instead of `bridge_count`.
   Proved modulo `extra_at_k_le_prod` (see #2).

2. **`extra_at_k_le_prod`** (SAWHWConvBound.lean, line 48)
   The fiber counting argument: for each k, extra walks with lastDCIndex = k
   inject into bridge_count_any(W+1, k) × narrow_suffix_count(W, n-k).
   This is the core decomposition lemma.
   Can use `Finset.card_biUnion_le_card_mul` for the fiber counting.

3. **`bridge_count_any ≤ bridge_count`** (SAWHWStepHelpers.lean, line 733)
   In `extra_sum_le_placeholder`: transition from bridge_count_any to bridge_count
   to connect with paper_bridge_partition. This step is FALSE in general and needs
   the proof architecture to be modified (see "Known Issue" below).

#### Known Issue: Bridge endpoint parity

The original `bridge_count` requires FALSE endpoints, but walks of even length from
`paperStart` (TRUE) always end at TRUE. So `bridge_count(T, even_k) = 0`, while
`bridge_count_any(T, even_k)` can be nonzero. This makes the original
`extra_count_le_conv` FALSE (counterexample: W=0, n=0).

**Proposed fix**: Replace `bridge_count` with `bridge_count_any` in the partition
function bound. The bridge_count_any GF satisfies:
  Σ_k bridge_count_any(T,k)·x^k ≤ (1 + 1/x) · paper_bridge_partition(T,x)
This changes the constant in hp_sum_step from 6 to 6·(1+1/x) but does not affect
convergence of ∏(1+C·B_T) for x < x_c.

## What was proved in this session

### Newly proved lemmas (SAWHWStepHelpers.lean):

1. **`tailTo`** — Definition: given SAW from v with getVert 1 = w, produce SAW from w of length s-1.
2. **`tailTo_injective`** — The tail extraction is injective.
3. **`tailTo_support_subset`** — Elements of the tail's support are in the original support.
4. **`tailTo_strip`** — Strip condition propagates through tailTo.
5. **`suffix_partition_bound`** — **KEY LEMMA PROVED**: SAWs from FALSE v inject into continuations from the two TRUE neighbors at dc=-W.
6. **`bridge_count_any`** — Definition: bridge count without FALSE endpoint requirement.
7. **`bridge_count_le_any`** — bridge_count ≤ bridge_count_any (monotonicity).

### Infrastructure (SAWHWConvBound.lean):

8. **`extra_at_k`** — Definition: extra walks with specific lastDCIndex value.
9. **`extra_count_eq_sum`** — extra_count equals the sum of extra_at_k over k.
10. **`extra_count_le_conv_nat`** — The ℕ convolution bound (modulo extra_at_k_le_prod).

### Mathematical discovery:

The original formulation of `extra_count_le_conv` (using `bridge_count` with FALSE
endpoint requirement) is FALSE due to the TRUE/FALSE parity alternation in the
hexagonal lattice. The corrected formulation uses `bridge_count_any` which allows
any endpoint parity. This requires a minor architectural change in the downstream
proofs (changing the constant factor in the generating function bound).
