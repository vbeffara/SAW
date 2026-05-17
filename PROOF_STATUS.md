# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent root sorries** (see below).

## Root Sorries

### Sorry #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
```lean
1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc
```
The parafermionic observable identity for the infinite strip, for all T ≥ 1.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

**T=1 case: PROVED INDEPENDENTLY** (see below).

### Sorry #2: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385)
Follows from Sorry #1.

### Sorry #3: `paper_bridge_decomp_injection` (SAWPaperChain.lean:265)
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

## ✅ New Results: T=1 Identity PROVED INDEPENDENTLY

### SAWAInf1Independent.lean — Endpoint injectivity (sorry-free)

- **`A_inf_1_same_endpoint`** ✓: Two PaperSAW_A_inf 1 walks with same first coordinate have the same endpoint.
- **`strip1_path_unique`** ✓: On the T=1 strip, two paths from paperStart to the same vertex are equal.
- **`A_inf_1_endpoint_injective`** ✓: The endpoint map s ↦ s.end_v.1 is injective on PaperSAW_A_inf 1.
- **`A_inf_1_upper`** ✓: A_inf 1 xc ≤ 2xc³/(1-xc²), using endpoint injectivity + geometric series.

### SAWAInf1Lower.lean — Independent lower bound (sorry-free)

All results in this file are **completely sorry-free** and do NOT depend on `infinite_strip_identity`.

- **`strip1_walk_to_pos`** ✓: Recursive construction of walks from paperStart to (m,-m,true) of length 2m.
- **`strip1_walk_to_neg`** ✓: Symmetric construction for negative direction.
- **`strip1_walk_to_pos_isPath`** ✓: Constructed walks are paths (no repeated vertices).
- **`strip1_walk_to_neg_isPath`** ✓: Same for negative direction.
- **`exists_A_inf_1_walk`** ✓: For each k ≠ 0, explicit PaperSAW_A_inf 1 walk to (k,-k,true).
- **`A_inf_1_equiv`** ✓: Bijection PaperSAW_A_inf 1 ≃ {k : ℤ // k ≠ 0} via endpoint map.
- **`nonzero_int_xc_sum_eq`** ✓: Geometric series computation ∑ xc^(2|k|+1) = 2xc³/(1-xc²).
- **`A_inf_1_lower_independent`** ✓: A_inf 1 xc ≥ 2xc³/(1-xc²).
- **`A_inf_1_exact_truly_independent`** ✓: A_inf 1 xc = 2xc³/(1-xc²).
- **`infinite_strip_identity_T1`** ✓: 1 = c_α · A_inf 1 xc + xc · B₁^xc, proved independently!

### Verification
All axioms are standard (propext, Classical.choice, Quot.sound). No `sorryAx`.
Verified via `#print axioms infinite_strip_identity_T1`.

## Proof Architecture

```
connective_constant_eq_corrected (SAWPaperChain.lean)
├── Z_xc_diverges_corrected [LOWER BOUND]
│   └── paper_bridge_lower_bound
│       └── bridge_recurrence_proved
│           └── infinite_strip_identity ← SORRY #1 (T=1 case PROVED)
└── hw_summable_corrected [UPPER BOUND]
    ├── paper_bridge_decomp_injection ← SORRY #3
    └── paper_bridge_decay
        └── paper_bridge_partial_sum_le
            └── B_paper_le_one_direct
                └── B_paper_le_one_strip ← SORRY #2 (= consequence of #1)
```

## Build Status
All files compile without errors. The new SAWAInf1Lower.lean is completely sorry-free.
