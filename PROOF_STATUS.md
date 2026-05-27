# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (1 root sorry remaining)

**`extra_sum_le_placeholder`** (SAWHWStepHelpers.lean, private)
The generating function bound for extra walks:
```lean
∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x
```

An equivalent public version `extra_sum_le_proof` is in SAWHWExtraFinal.lean.

#### Infrastructure proved toward extra_sum_le (in SAWHWExtraFinal.lean):

1. **`false_only_true_neighbor_at_dc_le`** ✓ — From FALSE(a,b), the only TRUE neighbor at dc ≤ a+b is (a,b,true). Key for bounding suffix first-step choices to 2.

2. **`contToHexOrigin`** ✓ — Injection from SAWs starting at TRUE w at dc=-W in [-W,0] to SAWs from hexOrigin in [-W,0], via hexTranslate + hexFlip.

3. **`contToHexOrigin_strip`** ✓ — The injection preserves the strip constraint [-W, 0].

4. **`contToHexOrigin_injective`** ✓ — The injection is injective.

5. **`continuation_from_true_le`** ✓ — From TRUE w at dc=-W, the number of strip-constrained SAWs of length s is ≤ hex_origin_strip_count(W, s).

6. **`narrow_suffix_count`** ✓ — Definition: 1 if s=0, 2*hex_origin_strip_count(W, s-1) if s≥1.

7. **`narrow_suffix_gf_le`** ✓ — The narrow suffix generating function is ≤ 6 * hp_sum(W, N, x).

#### Remaining work for extra_sum_le:

The mathematical argument is fully clear:
1. Each extra walk decomposes at lastDCIndex(-(W+1)) into bridge prefix + suffix.
2. Bridge prefix is a PaperBridge of width W+1 (by bridge_satisfies_paper_inf_strip).
3. Suffix starts from FALSE at dc=-(W+1), subsequent vertices stay in [-W, 0] (by suffix_after_last_narrow).
4. Suffix of length s has ≤ narrow_suffix_count(W, s) options (by false_only_true_neighbor_at_dc_le + continuation_from_true_le).
5. Narrow suffix GF ≤ 6 * hp_sum(W) (by narrow_suffix_gf_le, proved).
6. extra_count ≤ Σ bridge_count * suffix_count (by partition + fiber bound).
7. Bridge partial sum ≤ paper_bridge_partition (partial sum of nonneg tsum).
8. Combine via Cauchy product: extra_sum ≤ B * suffix_GF ≤ 6*B*hp_sum.

Steps 5 is fully proved. Steps 6-8 require:
- Constructing PaperBridge from SAW prefix (bridge extraction)
- Relating paper_bridge_length_count to paper_bridge_partition (injection + tsum)
- Cauchy product bound for finite × tsum product

These are primarily Lean formalization challenges (type coercions, Fintype instances, tsum machinery), not mathematical difficulties.

## Proof Architecture

### Upper Bound: μ ≤ √(2+√2) via Z(x) < ∞ for x < xc
```
connective_constant_eq_corrected
└── hw_summable_corrected ✓
    └── paper_bridge_decomp_bound ✓
        └── hw_injection_bound ✓
            └── hw_injection_bound_correct ✓
                ├── saw_sum_le_hp_sq ✓
                │   ├── saw_count_split ✓
                │   ├── saw_nonneg_le_hex_strip ✓
                │   ├── hex_origin_strip_sum_le ✓
                │   ├── hp_sum_ge_one_plus_x ✓
                │   ├── cauchy_product_le ✓
                │   └── saw_neg_le_hp_conv ✓
                └── hp_sum_le_prod ✓
                    ├── hp_sum_zero_le ✓
                    └── hp_sum_step ✓ (modulo extra_sum_le)
                        └── extra_sum_le_placeholder ← SORRY (remaining)
                            ├── narrow_suffix_gf_le ✓
                            ├── continuation_from_true_le ✓
                            ├── false_only_true_neighbor_at_dc_le ✓
                            └── [bridge extraction + Cauchy product] ← TODO

### Lower Bound: μ ≥ √(2+√2) via Z(xc) = ∞
connective_constant_eq_corrected
└── Z_xc_diverges_corrected
    └── paper_bridge_lower_bound
        └── bridge_recurrence_proved
            └── infinite_strip_identity ← SORRY #1
```
