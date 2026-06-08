# Proof Status: μ = √(2+√2)

## Main Theorem

```
theorem connective_constant_eq : connective_constant = Real.sqrt (2 + Real.sqrt 2)
```

**Location:** `RequestProject/SAWFinal.lean`

## Critical Path — Single Fundamental Sorry

All sorry's on the critical path reduce to a single fundamental mathematical fact:

### `hex_closed_trail_turning_number` (SAWTurningNumber.lean:92)
**The discrete Gauss-Bonnet theorem for simple closed hex trails.**
For a simple closed trail L on the hex lattice:
  hexWalkWinding L + closure = ±2π

This is the discrete analogue of the turning tangent theorem / Umlaufsatz:
a simple closed polygon has total exterior angle ±2π.

**Proved helper:** `hex_edge_norm_one` — each hex edge direction has norm 1.

**Why it's hard:** Requires showing that a simple (non-self-intersecting)
closed polygon in the plane has turning number exactly ±1. This is a
fundamental result in discrete geometry equivalent to the Jordan curve
theorem for polygonal paths. No existing Mathlib infrastructure covers this.

### Dependency Chain

All remaining sorry's flow from `hex_closed_trail_turning_number`:

```
hex_closed_trail_turning_number
  → pair_winding_relation (SAWPairCancellation.lean)
    → pair_exp_cancellation (PROVED from pair_winding_relation)
      → pair_contrib_cancels (PROVED)
        → freshVertexSum_pair_part_zero_proved (PROVED)
          → fresh_vertex_relation (PROVED = Lemma 1)
            → finite_strip_identity_from_vr (SAWStripIdentityFromVR.lean)
              → B_paper_le_one_strip (SAWStripIdentityCorrect.lean)
              → infinite_strip_identity (SAWRecurrenceProof.lean)
```

Note: `B_paper_le_one_strip` and `infinite_strip_identity` are
currently formulated as standalone sorry's (not directly connected to
the vertex relation chain) due to circular import constraints.
The file `SAWStripIdentityFromVR.lean` provides the bridge between
the vertex relation and the strip identity, but is blocked by the
same fundamental sorry.

## All Sorry Locations (12 total)

### Critical path (5 sorry's):
1. `hex_closed_trail_turning_number` (SAWTurningNumber.lean:92) — **ROOT CAUSE**
2. `pair_winding_relation` (SAWPairCancellation.lean:173) — needs #1
3. `B_paper_le_one_strip` (SAWStripIdentityCorrect.lean:385) — needs vertex relation
4. `infinite_strip_identity` (SAWRecurrenceProof.lean:56) — needs vertex relation
5. `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean:80) — needs #2 + discrete Stokes

### Preparation for future use (2 sorry's):
6. `prefix_penultimate_is_neighbor` (SAWPairWindingProof.lean:43) — helper for #2
7. `pair_inner_loop_trail_rev` (SAWWindingDecomp.lean:91) — helper for winding decomposition

### Dead branches (5 sorry's, NOT on critical path):
8. `trail_vertex_relation` (SAWCancellationIdentity.lean:305) — superseded by fresh version
9. `strip_observable_summable` (SAWStripObservable.lean:173) — not needed
10. `triplet_part_zero` (SAWTrailVertexRelation.lean:274) — superseded
11. `pair_part_zero` (SAWTrailVertexRelation.lean:282) — superseded
12. `hex_simple_closed_trail_winding` (SAWWindingDiff.lean:72) — general turning number (dead branch)

## Fully Proved Components

### Hammersley-Welsh Decomposition (FULLY PROVED ✓)
All SAWHW*.lean files are sorry-free:
- `hw_injection_bound` — SAW count ≤ 8 · (∏(1+12·B_T))²
- Bridge decomposition algorithm and injection
- Extra walk bounds and fiber counting

### Algebraic Identities (FULLY PROVED ✓)
- `pair_cancellation`: j·conj(λ)⁴ + conj(j)·λ⁴ = 0 ✓
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0 ✓
- `xc_inv`: xc⁻¹ = √(2+√2) ✓
- `fin3_other_pair_cancel` ✓ — pair algebraic cancellation for all j_idx
- `exp_shift_minus'`, `exp_shift_plus'` ✓ — exponential shift formulas

### Vertex Relation / Lemma 1 (PROVED modulo pair_winding_relation)
- `fresh_vertex_relation` (SAWPairInvolutionProof.lean) ✓ (modulo pair_winding_relation)
- Triplet cancellation: `freshVertexSum_triplet_part_zero` ✓
- Pair cancellation: `freshVertexSum_pair_part_zero_proved` ✓ (modulo pair_winding_relation)
- Pair involution: `pairSigmaInvol_injective` ✓
- Extension maps: `freshExtensionMap_injective`, `fresh_outgoing_surj` ✓

### Winding Infrastructure (MOSTLY PROVED ✓)
- `hexWalkWinding_split` ✓ — winding additivity for list splitting
- `hex_turn_value` ✓ — all hex turns are ±π/3
- `hex_edge_norm_one` ✓ — all hex edge directions have unit norm
- `hexWalkWinding_reverse_list'` ✓ — winding reversal for hex trails
- `pair_suffix_hex_trail` ✓ — suffix is a hex trail list
- `pair_suffix_hex_trail_rev` ✓ — reversed suffix is a hex trail list
- `pair_suffix_reverse` ✓ — reversed suffix = reverse of suffix
- `pair_suffix_winding_neg` ✓ — reversed suffix winding is negated
- `pair_inner_loop_trail` ✓ — full walk support is hex trail

### Bridge Recurrence (PROVED modulo infinite_strip_identity)
- `bridge_recurrence_proved`: B(T) ≤ c_α·B(T+1)² + B(T+1) ✓ (modulo infinite_strip_identity)
- `cutting_argument_proved`: A(T+1) - A(T) ≤ xc·B(T+1)² ✓

### Connective Constant Infrastructure (FULLY PROVED ✓)
- `saw_count_submult'`: c_{n+m} ≤ c_n · c_m ✓
- `connective_constant_is_limit'`: μ = lim c_n^{1/n} ✓
- `connective_constant_eq_from_bounds`: Z diverges + Z converges → μ = √(2+√2) ✓

## File Organization

All files that contribute to the proof are imported transitively from `SAWFinal.lean`.

### Key file groups:
- **Core:** SAW.lean, SAWSubmult.lean, SAWMain.lean
- **Bridges:** SAWBridge.lean, SAWBridgeFix.lean, SAWDiagBridge.lean, SAWDiagConnection.lean, SAWDiagProof.lean
- **Strip identity:** SAWStripIdentityCorrect.lean, SAWStripIdentityProof.lean, SAWStripIdentityFromVR.lean
- **Parafermionic observable:** SAWObservable.lean, SAWObservableDef.lean, SAWObservableFormal.lean
- **Vertex relation:** SAWPathVertexRelation.lean, SAWVertexRelationProof.lean, SAWCancellationProved.lean
- **Pair involution:** SAWPairInvolution.lean, SAWPairInvolutionHelpers.lean, SAWPairInvolutionProof.lean
- **Pair cancellation:** SAWPairCancellation.lean, SAWPairWinding.lean, SAWPairWindingProof.lean
- **Winding:** SAWWindingGeneral.lean, SAWWindingLemma.lean, SAWWindingReverse.lean, SAWWindingDecomp.lean, SAWWindingDiff.lean
- **Turning number:** SAWTurningNumber.lean
- **Discrete Stokes:** SAWDiscreteStokes.lean, SAWStokesAbstract.lean, SAWStripAlgebra.lean
- **HW decomposition:** SAWHW*.lean (15+ files, all sorry-free)
- **Recurrence:** SAWRecurrenceProof.lean, SAWCuttingProof.lean, SAWCutting.lean
- **Final assembly:** SAWPaperChain.lean, SAWFinal.lean

### Preparation files (linked but not on critical path):
- `SAWWindingDecomp.lean` — pair_inner_loop_trail_rev (preparation for pair_winding_relation)
- `SAWPairWindingProof.lean` — prefix_penultimate_is_neighbor (preparation for pair_winding_relation)
- `SAWPairWindingRelation.lean` — alternative pair cancellation via winding
- `SAWObservableSum.lean` — observable as formal sum over trails
- `SAWStripAlgebra.lean` — algebraic identities for strip boundary evaluation
