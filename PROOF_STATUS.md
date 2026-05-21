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

### Sorry #2: `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385)
```lean
B_paper T L xc ≤ 1
```
The core bound from the parafermionic observable for the finite strip.
Required for: paper_bridge_partial_sum_le → paper_bridge_decay → upper bound.
**Note**: Sorry #2 is a consequence of Sorry #1 (by taking L → ∞).

### Sorry #3: `hw_injection_bound` (SAWHWFinalProof.lean:76)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
  2 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2
```
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

**There are only 2 independent root sorries: #1/#2 (parafermionic) and #3 (HW).**

## New Progress (Hammersley-Welsh)

### New sorry-free files:

- `SAWHWBound.lean`: Helper infrastructure for the bridge decomposition:
  - `saw_vertex_dc_bound`: vertices in n-step SAWs have dc in [-n, n]
  - `hexFlip_dc`: hexFlip negates diagCoord
  - `hexFlip_involution`, `hexFlip_paperStart`, `hexFlip_hexOrigin`: hexFlip properties
  - `prod_one_add_eq`: the powerset product identity ∏(1+a_T) = Σ_{S} ∏_{T∈S} a_T
  - `paper_bridge_partition_nonneg'`: B_T(x) ≥ 0 for x > 0

- `SAWHWDecompFresh.lean`: New structural lemmas for the bridge decomposition:
  - `last_at_min_dc_is_false` (PROVED): In a walk from a TRUE vertex at dc=0
    staying in [-M, 0], any non-endpoint vertex at dc=-M is FALSE. Uses
    `no_true_at_min_dc_in_strip`.
  - `min_dc_vertex_is_false_in_hp` (PROVED): In a downward half-plane walk from
    paperStart, any non-endpoint vertex at minimum dc is FALSE.
  - `hp_prefix_is_bridge` (PROVED): The prefix of a half-plane walk to a FALSE
    vertex at dc=-M is a valid PaperBridge of width M.
  - `next_after_min_dc_false` (PROVED): After a FALSE vertex at dc=-M, the next
    vertex has dc = -(M-1) and is TRUE. This is the key lemma showing that the
    "remainder" after bridge extraction has strictly smaller width.

### What remains for Sorry #3

The remaining gap is the **full iterative bridge extraction and counting argument**:

1. **Half-plane walk decomposition**: Given a downward half-plane walk from
   paperStart (all dc ∈ [-M, 0]), iteratively extract PaperBridges of
   widths M > M₁ > M₂ > ... using the structural lemmas above. Each step:
   - Find the LAST vertex at dc=-M (FALSE, by `min_dc_vertex_is_false_in_hp`)
   - Extract PaperBridge of width M (by `hp_prefix_is_bridge`)
   - The next vertex has dc=-(M-1) (by `next_after_min_dc_false`)
   - Translate the remainder to start from paperStart (by `hexTranslate`)
   - Recurse with width M-1

2. **General SAW splitting**: Split a SAW at the first vertex of maximum
   diagCoord (which is TRUE, by `max_dc_is_true'`). After translation,
   both the reversed prefix and suffix become downward half-plane walks.

3. **Injectivity**: The bridge sequence uniquely determines the walk
   (given the starting vertex choice). This is the "reverse procedure"
   from the paper.

4. **Counting**: Sum over all bridge sequences to get:
   ∑ c_n x^n ≤ 2 * (∏(1+B_T))²

### Key difficulty

The main challenge is that the full decomposition requires:
- Well-founded recursion on hexReScaled width (or diagCoord width)
- Walk splitting, translation, and concatenation operations
- Careful handling of the hexagonal lattice's bipartite structure
- A formal injectivity argument

Each of these is individually tractable but together they require ~500+ lines
of Lean code. The structural lemmas in `SAWHWDecompFresh.lean` resolve the
hardest STRUCTURAL obstacles (the bipartite issue), but the COMBINATORIAL
machinery (walk splitting, iterative extraction, counting) remains.

## Proof Architecture

### Lower Bound: μ ≥ √(2+√2) via Z(xc) = ∞
```
connective_constant_eq_corrected (SAWPaperChain.lean)
└── Z_xc_diverges_corrected [Z(xc) = ∞]
    └── paper_bridge_lower_bound [B_T ≥ c/T]
        └── bridge_recurrence_proved [B_T ≤ α·B_{T+1}² + B_{T+1}]
            └── infinite_strip_identity ← SORRY #1
```

### Upper Bound: μ ≤ √(2+√2) via Z(x) < ∞ for x < xc
```
connective_constant_eq_corrected (SAWPaperChain.lean)
└── hw_summable_corrected [Z(x) < ∞]
    ├── paper_bridge_decomp_injection ← SORRY #3
    └── paper_bridge_decay [B_T(x) ≤ (x/xc)^T / xc]
        └── paper_bridge_partial_sum_le [partial sums ≤ 1/xc]
            └── B_paper_le_one_strip ← SORRY #2
```
