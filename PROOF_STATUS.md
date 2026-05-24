# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh (SAWHWHalfPlane.lean + SAWHWStepHelpers.lean)

**2a. `extra_sum_le`** (SAWHWStepHelpers.lean)
```lean
∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x
```
The key generating function bound for the Hammersley-Welsh inductive step.
Requires the bridge-suffix decomposition:
- Each extra walk (visiting dc=-(W+1)) decomposes at the LAST vertex at dc=-(W+1)
  into a bridge prefix + suffix.
- After translate+flip, suffix maps to walk from hexOrigin in dc ∈ [-W, 0].
- Suffix GF ≤ (1+2x+2x²)·hp_sum(W) ≤ 6·hp_sum(W) (analytically proved from
  hex_origin_strip_le_hp, hex_origin_strip_zero, hp_sum_ge_one).
- Cauchy product gives: ∑ extra(n)·x^n ≤ B_{W+1}·6·hp_sum(W).

**Once `extra_sum_le` is proved, `hp_sum_step` follows automatically via
`hp_sum_step_from_helpers`.**

**2b. `saw_sum_le_hp_sq`** (SAWHWHalfPlane.lean:152)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤ 2 * (hp_sum N N x) ^ 2
```
SAW partition function bounded by square of half-plane walk partition function.
Uses splitting each SAW at the first vertex of minimum diagCoord.

## What was proved in the HW chain

### Infrastructure (SAWHWStepHelpers.lean)
1. **`hp_walk_count_split`**: hp_walk_count(W+1, n) = hp_walk_count(W, n) + extra_count(W, n). PROVED.
2. **`hp_sum_split`**: Generating function version of the split. PROVED.
3. **`hexOrigin_only_neighbor_in_strip`**: From hexOrigin in dc ∈ [-W, 0], only neighbor is paperStart. PROVED.
4. **`dropFirstHexSub`**: Injection from strip-constrained SAWs from hexOrigin(m+1) to SAWs from paperStart(m). PROVED.
5. **`dropFirstHexSub_injective`**: The injection is injective. PROVED.
6. **`hex_origin_strip_le_hp`**: hex_origin_strip_count(W, m) ≤ hp_walk_count(W, m-1). PROVED from injection.
7. **`hex_origin_strip_zero`**: hex_origin_strip_count(W, 0) = 1. PROVED.
8. **`hp_walk_count_zero`**: hp_walk_count(W, 0) = 1. PROVED.
9. **`hp_sum_ge_one`**: hp_sum(W, N, x) ≥ 1 for x ≥ 0. PROVED.
10. **`hp_sum_step_from_helpers`**: hp_sum_step derived from extra_sum_le. PROVED.

### Previously proved (SAWHWHalfPlane.lean)
1. **`hp_walk_count_zero_ge2`**: No SAW of length ≥ 2 stays at dc=0. PROVED.
2. **`hp_walk_count_zero_zero_le`**: At most 1 walk of length 0 at dc=0. PROVED.
3. **`hp_walk_count_zero_one_le`**: At most 1 walk of length 1 at dc=0. PROVED.
4. **`hp_sum_zero_le`**: hp_sum at width 0 ≤ 1+x. PROVED.
5. **`hp_sum_le_prod`**: hp_sum(W) ≤ 2·∏(1+6B_T). PROVED from hp_sum_step.
6. **`hw_injection_bound_correct`**: ∑c_n x^n ≤ 8·(∏(1+6B_T))². PROVED.

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
└── hw_summable_corrected ✓ PROVED
    └── paper_bridge_decomp_bound ✓ PROVED
        └── hw_injection_bound ✓ PROVED
            └── hw_injection_bound_correct ✓ PROVED
                ├── hp_sum_le_prod ✓ PROVED
                │   ├── hp_sum_zero_le ✓ PROVED
                │   └── hp_sum_step ← depends on extra_sum_le
                │       └── hp_sum_step_from_helpers ✓ PROVED
                │           └── extra_sum_le ← SORRY #2a
                │               ├── hex_origin_strip_le_hp ✓ PROVED
                │               ├── hex_origin_strip_zero ✓ PROVED
                │               ├── hp_sum_ge_one ✓ PROVED
                │               └── [bridge-suffix decomposition injection] ← needs formalization
                └── saw_sum_le_hp_sq ← SORRY #2b
    └── paper_bridge_decay ✓ PROVED
```
