# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_corrected` in `SAWPaperChain.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo 2 independent sorry chains** (see below).

## Root Sorries

### Sorry Chain #1: `infinite_strip_identity` (SAWRecurrenceProof.lean:49)
The parafermionic observable identity for the infinite strip.
Required for: Z(xc) = ∞ (lower bound μ ≥ √(2+√2)).

### Sorry Chain #2: Hammersley-Welsh

The HW chain has **3 root sorries**, reduced from the original 2 by decomposition:

**2a. `extra_sum_le`** (SAWHWStepHelpers.lean:160)
The generating function bound for extra walks:
```lean
∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x
```
Requires constructing an injection from extra walks (visiting dc=-(W+1))
to (bridge, step-choice, hexOrigin-strip walk) triples. The bridge extraction
is done at the LAST vertex at dc=-(W+1) (using lastDCIndex infrastructure).
Once proved, `hp_sum_step` follows via `hp_sum_step_from_helpers`.

**2b. `saw_neg_le_hp_conv`** (SAWHWSawBound.lean:65)
SAWs visiting dc < 0 are bounded by the convolution of hp_walk_counts:
```lean
(saw_count_neg_dc n : ℝ) ≤
    ∑ k ∈ Finset.range (n + 1), (hp_walk_count N k : ℝ) * (hp_walk_count N (n - k) : ℝ)
```
Requires constructing an injection from SAWs visiting dc < 0 to pairs of
hp-walks, using the decomposition at the first vertex of minimum dc
(which is FALSE by firstMinDC_is_false). Once proved, `saw_sum_le_hp_sq`
follows via `saw_sum_le_hp_sq_proof`.

**2c. `saw_sum_le_hp_sq_proof`** (SAWHWSawBound.lean:73)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤ 2 * (hp_sum N N x) ^ 2
```
Follows from 2b + the algebraic argument:
saw_sum = nonneg_sum + neg_sum ≤ (1+x)·hp_sum + hp_sum² ≤ 2·hp_sum²

## What was proved in this session (Hammersley-Welsh)

### New file: `SAWHWLastVertex.lean` — 6 lemmas, all PROVED
Infrastructure for finding the last vertex at a given dc value.
1. `lastDCIndex` — definition using Finset.max'
2. `lastDCIndex_le_length` ✓
3. `lastDCIndex_dc` ✓
4. `lastDCIndex_is_max` ✓
5. `after_lastDCIndex_no_dc` ✓
6. `lastDCIndex_is_false` ✓ — last vertex at dc=-(W+1) is FALSE
7. `suffix_after_last_narrow` ✓ — suffix stays in [-W, 0]

### New file: `SAWHWMinDC.lean` — 7 lemmas, all PROVED
Infrastructure for the minimum dc decomposition.
1. `minDCVal` — definition: minimum dc value along a walk
2. `minDCVal_le` ✓ — min is ≤ every dc value
3. `minDCVal_achieved` ✓ — minimum is achieved
4. `firstMinDCIdx` — definition: first index achieving minimum
5. `firstMinDCIdx_le_length` ✓
6. `firstMinDCIdx_dc` ✓
7. `minDCVal_paperStart_le` ✓ — minDCVal ≤ 0 from paperStart
8. `neg_minDCVal_le_length` ✓ — width ≤ walk length
9. `firstMinDC_is_false` ✓ — first min-dc vertex is FALSE (when minDCVal < 0)

### New file: `SAWHWExtraProof.lean` — 2 lemmas, all PROVED
1. `hp_walk_count_mono` ✓ — wider strip has more walks
2. `hex_origin_strip_sum_le` ✓ — hex strip GF ≤ (1+x)·hp_sum

### New file: `SAWHWSawBound.lean` — 3 proved, 2 sorry
1. `saw_count_nonneg_dc` / `saw_count_neg_dc` — definitions
2. `saw_count_split` ✓ — saw_count = nonneg + neg
3. `saw_nonneg_le_hex_strip` ✓ — nonneg walks ≤ hex strip (via hexFlip injection)
4. `saw_neg_le_hp_conv` — SORRY (injection construction)
5. `saw_sum_le_hp_sq_proof` — SORRY (depends on 4)

### Import restructuring
- Removed unnecessary imports from SAWHWLastVertex.lean to break circular dependencies
- Added SAWHWLastVertex import to SAWHWStepHelpers.lean and SAWHWHalfPlane.lean

## What remains to formalize

Both remaining sorries require constructing **explicit walk decomposition injections**
in Lean. The mathematical arguments are completely clear:

1. **`extra_sum_le`**: Split extra walk at lastDCIndex, extract bridge prefix,
   translate+flip suffix → hexOrigin strip walk. Injection is injective.

2. **`saw_neg_le_hp_conv`**: Split SAW at firstMinDCIdx, reverse prefix,
   translate+flip both halves → pair of hp-walks. Injection is injective.

The technical challenge is composing Walk.take, Walk.drop, Walk.reverse,
hexTranslate_walk, hexFlip_walk while verifying IsPath preservation and
strip constraints at each step. Each individual operation has Lean API support,
but the composition is very involved.

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
└── hw_summable_corrected ✓
    └── paper_bridge_decomp_bound ✓
        └── hw_injection_bound ✓
            └── hw_injection_bound_correct ✓
                ├── hp_sum_le_prod ✓
                │   ├── hp_sum_zero_le ✓
                │   └── hp_sum_step
                │       └── hp_sum_step_core ← depends on extra_sum_le
                │           └── extra_sum_le ← SORRY #2a
                │               ├── lastDCIndex infrastructure ✓ (6 lemmas)
                │               ├── hex_origin_strip_sum_le ✓
                │               ├── hp_sum_ge_one ✓
                │               └── [injection construction needed]
                └── saw_sum_le_hp_sq
                    └── saw_sum_le_hp_sq_proof ← depends on saw_neg_le_hp_conv
                        ├── saw_count_split ✓
                        ├── saw_nonneg_le_hex_strip ✓
                        ├── hex_origin_strip_sum_le ✓
                        └── saw_neg_le_hp_conv ← SORRY #2b
                            ├── firstMinDC_is_false ✓
                            ├── minDCVal infrastructure ✓ (7 lemmas)
                            ├── hp_walk_count_mono ✓
                            └── [injection construction needed]
    └── paper_bridge_decay ✓
```
