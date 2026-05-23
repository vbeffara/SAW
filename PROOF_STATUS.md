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
Two sorry'd lemmas remain:

**2a. `hp_sum_step`** (SAWHWHalfPlane.lean:121)
```lean
hp_sum (W + 1) N x ≤ (1 + 6 * paper_bridge_partition (W + 1) x) * hp_sum W N x
```
Inductive step: walks in dc ∈ [-(W+1), 0] bounded by (1 + 6·B_{W+1}) · walks in [-W, 0].
Uses bridge decomposition: walks reaching dc -(W+1) decompose at the LAST such vertex
into a bridge prefix and suffix. The suffix (from bridge endpoint FALSE@dc=-(W+1))
has ≤ 3 immediate next vertices, plus walks through TRUE@dc=-W (2 choices) each
followed by walks from hexOrigin of width W. Combined with hp_sum ≥ 1,
the reaching walk contribution is ≤ 6B · hp_sum(W).

**2b. `saw_sum_le_hp_sq`** (SAWHWHalfPlane.lean:152)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤ 2 * (hp_sum N N x) ^ 2
```
SAW partition function bounded by square of half-plane walk partition function.
Uses splitting each SAW at the first vertex of minimum diagCoord.

## What was proved in the HW chain

### Newly proved (this session)
1. **`hp_walk_count_zero_ge2`**: No SAW of length ≥ 2 stays at dc=0. PROVED.
2. **`hp_walk_count_zero_zero_le`**: At most 1 walk of length 0 at dc=0. PROVED.
3. **`hp_walk_count_zero_one_le`**: At most 1 walk of length 1 at dc=0. PROVED.
4. **`hp_sum_zero_le`**: hp_sum at width 0 ≤ 1+x. PROVED from the above.
5. **`hp_sum_le_prod`**: hp_sum(W) ≤ 2·∏(1+6B_T). PROVED from hp_sum_step.
6. **`hw_injection_bound_correct`**: ∑c_n x^n ≤ 8·(∏(1+6B_T))². PROVED from hp_sum_le_prod + saw_sum_le_hp_sq.
7. **`hw_injection_bound`**: Wraps hw_injection_bound_correct. PROVED.
8. **`paper_bridge_decomp_bound`**: Calls hw_injection_bound. PROVED.
9. **`hw_summable_corrected`**: Z(x) < ∞ for x < xc. PROVED from paper_bridge_decomp_bound + paper_bridge_decay.

### Key design changes (this session)
- **Removed paper_bridge_partition_lt_one**: This was FALSE (B_1(xc) ≈ 1.53 > 1)!
  The vertex formulation gives B_T(xc) ≤ 1/xc ≈ 1.85, not ≤ 1.
- **Changed from 1/(1-B) to (1+6B) form**: The self-referential bound
  hp_sum(W+1) ≤ hp_sum(W) + B·hp_sum(W+1) can't be used as hp_sum ≤ hp_sum/(1-B)
  when B > 1. Instead, using hp_sum ≥ 1 to absorb the additive constant gives
  hp_sum(W+1) ≤ (1+6B)·hp_sum(W), which works for ALL B values.
- **Constant 6**: From 1+3x+2x² ≤ 6 for x ∈ [0,1], accounting for the vertex
  formulation's suffix structure (3 neighbors + 2 continuations to hexOrigin).
- **Removed hp_sum_step old form**: The old form with (1+B) was too tight for
  the vertex formulation.

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
                │   │   ├── hp_walk_count_zero_ge2 ✓ PROVED
                │   │   ├── hp_walk_count_zero_zero_le ✓ PROVED
                │   │   └── hp_walk_count_zero_one_le ✓ PROVED
                │   └── hp_sum_step ← SORRY #2a
                └── saw_sum_le_hp_sq ← SORRY #2b
    └── paper_bridge_decay ✓ PROVED
```
