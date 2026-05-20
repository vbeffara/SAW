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

### Sorry #3: `paper_bridge_decomp_injection` (SAWPaperChain.lean:265)
```lean
∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
  2 * (∑ S ∈ (Finset.range N).powerset,
    ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2
```
The Hammersley-Welsh bridge decomposition counting inequality.
Required for: Z(x) < ∞ for x < xc (upper bound μ ≤ √(2+√2)).

**Key progress** (SAWHWStructural.lean, SAWHWReCoord.lean, SAWHWDecompInject.lean — all sorry-free, no longer depend on SAWPaperChain.lean):

**IMPORTANT**: These three files have been refactored to import SAWDiagProof instead
of SAWPaperChain, breaking the circular dependency. This means hw_bridge_decomp_core
(in SAWHWBridgeDecomp.lean) can be proved without circular references.
Once proved, it can be imported into SAWPaperChain.lean to close sorry #3.

The equivalent theorem statement is in SAWHWBridgeDecomp.lean:hw_bridge_decomp_core.

Previously proved structural lemmas (now in dependency-free files):

The following critical structural lemmas have been proved, establishing that
the bridge decomposition automatically produces valid PaperBridges:

- `dc_step_from_true`: From TRUE vertices, diagCoord can only decrease or stay
- `dc_step_from_false`: From FALSE vertices, diagCoord can only increase or stay
- `true_only_false_neighbor_at_dc`: TRUE vertex's only neighbor at same dc is FALSE(same cell)
- `path_interior_has_neighbors`: Non-endpoint path vertices have distinct predecessor and successor
- `no_true_at_min_dc_in_strip`: TRUE vertices at dc = -T cannot be intermediate vertices in bridges (they would force revisiting FALSE at same dc, violating self-avoidance)
- `no_false_at_zero_dc`: FALSE vertices at dc = 0 cannot be intermediate vertices in bridges from paperStart
- `bridge_satisfies_paper_inf_strip`: **KEY RESULT**: Any SAW from paperStart to a FALSE vertex at dc = -T, staying in dc ∈ [-T, 0], automatically satisfies PaperInfStrip T for ALL vertices. This means the bridge decomposition produces valid PaperBridges without needing to verify PaperInfStrip constraints explicitly.

These lemmas resolve the fundamental bipartite-structure obstacle: on the hex lattice,
TRUE and FALSE vertices have different PaperInfStrip constraints, but self-avoidance
automatically enforces the tighter constraints.

**Detailed analysis of the remaining approach**:

Two complementary coordinate systems are available:

1. **hexReScaled** (SAWHWReCoord.lean): STRICTLY changes at every walk step,
   resolving the "flat walk" issue with diagCoord. Key lemmas:
   - `hexReScaled_adj_ne`: strictly changes at every step
   - `hexReScaled_adj_bound`: changes are in {-2, -1, +1, +2}
   - `hexReScaled_mod3`: values ≡ 0 or 2 (mod 3)
   - `hexReScaled_in_strip`: PaperInfStrip T → hexReScaled ∈ [0, 3T]

2. **diagCoord** (v.1 + v.2.1) with the structural lemma (SAWHWDecompInject.lean):
   - `false_has_true_ge_dc'`: In any non-trivial hex walk, every FALSE vertex
     has a TRUE vertex at diagCoord ≥ its own in the walk support
   - `max_dc_is_true'`: Max diagCoord is ALWAYS achieved by a TRUE vertex
   This is the key structural lemma: it ensures the split vertex in the
   Hammersley-Welsh decomposition is always TRUE, making extracted bridges
   compatible with PaperBridge (which starts at paperStart = TRUE vertex).

To complete the proof, one needs to formalize:
1. Walk splitting at the first max-diagCoord vertex (always TRUE by max_dc_is_true')
2. Half-space walk decomposition into PaperBridges by induction on width
3. Bridge extraction and translation to PaperBridges
4. Injectivity of the decomposition (each walk uniquely determines its bridge sequence)
5. Weight bound (walk length ≥ sum of bridge lengths, hence x^n ≤ ∏ x^{bridge_len})

**There are only 2 independent root sorries: #1/#2 (parafermionic) and #3 (HW).**

## Proof Architecture

The main theorem depends on two independent bounds:

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

## ✅ What IS Proved (sorry-free)

### Core Algebraic Identities (SAW.lean)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
- `sqrt_two_add_sqrt_two_eq`: √(2+√2) = 2cos(π/8)
- `c_alpha_pos`, `c_eps_pos`: boundary coefficients are positive

### Vertex Relation Infrastructure (SAWStripProofNew.lean)
- `false_vertex_triplet_zero`: triplet cancellation at FALSE vertices
- `true_vertex_triplet_zero`: triplet cancellation at TRUE vertices

### Combinatorial Infrastructure
- `saw_count_submult'` (SAWSubmult.lean): c_{n+m} ≤ c_n·c_m
- `saw_count_vertex_independent` (SAWSubmult.lean): c_n is independent of starting vertex
- `saw_count_pos` (SAW.lean): c_n > 0 for all n
- `connective_constant` (SAW.lean): definition and basic properties

### HexReScaled Coordinate (SAWHWReCoord.lean)
- `hexReScaled_adj_ne`: strict change at every step (key for bridge decomposition)
- `hexReScaled_mod3`: mod-3 structure of hexReScaled values
- `hexReScaled_in_strip`: strip constraints in hexReScaled coordinates
- `hexReScaled_bridge_endpoint`: bridge endpoints in hexReScaled coordinates

### Bridge Infrastructure (SAWDiagProof.lean)
- `PaperBridge`: bridge definition with diagonal coordinates
- `paper_bridge_partition`: bridge partition function
- `paper_bridge_length_ge`: bridge of width T has length ≥ T
- `paper_bridge_in_fin_strip`: bridges fit in finite strips

### Cutting Argument (SAWCuttingProof.lean)
- `cutting_argument_proved`: A_inf(T+1) - A_inf(T) ≤ xc·B(T+1)²

### Bridge Recurrence (SAWRecurrenceProof.lean, modulo sorry #1)
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1)

### Lower Bound Infrastructure (SAWDecomp.lean)
- `quadratic_recurrence_lower_bound`: from recurrence → B_T ≥ c/T
- `harmonic_not_summable`: ∑ 1/n diverges

### Bridge Decay (SAWPaperChain.lean, modulo sorry #2)
- `paper_bridge_decay`: B_T(x) ≤ (x/xc)^T / xc for x < xc
- `paper_bridge_summable`: bridges are summable for T ≥ 1

### Helper Lemmas (SAWHWProved2.lean, sorry-free)
- `diagCoord_adj_le/ge`: diagonal coordinate changes by at most 1 per step
- `walk_diagCoord_bound`: walk endpoint within length distance
- `Finset.sum_powerset_prod_eq_prod_add_one`: powerset-product identity

## What Remains

### To prove Sorry #1/#2 (Parafermionic Identity):
The algebraic ingredients are fully proved. What remains is the combinatorial
discrete Stokes argument:
1. ✅ Define the winding phase and prove triplet cancellation at vertices
2. Define the observable at each mid-edge of the strip
3. Show the vertex relation holds at each interior vertex
4. Sum vertex relations: interior mid-edges cancel (discrete Stokes)
5. Evaluate boundary contributions
6. Conclude: 1 = c_α·A + B + c_ε·E, hence B ≤ 1

### To prove Sorry #3 (HW Decomposition):
The hexReScaled coordinate infrastructure is in place (`hexReScaled_adj_ne` etc.).
The remaining formalization steps are:
1. Define half-plane walks using hexReScaled coordinate
2. Formalize walk splitting at minimum hexReScaled vertex
3. Formalize bridge extraction by induction on hexReScaled height
4. Show extracted bridges are valid PaperBridges after translation
5. Prove injectivity of the decomposition
6. Derive the counting inequality

## Build Status
All files in the main proof chain compile without errors.
