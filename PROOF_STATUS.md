# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_direct` in `SAWMainNew.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo two critical sorries** (`infinite_strip_identity` and
`B_paper_le_one_strip`), both of which are consequences of the strip identity
(Lemma 2 of Duminil-Copin & Smirnov 2012).

## Main Theorem Chain

```
  finite_strip_identity_from_vr (NEW SORRY — Lemma 2, discrete Stokes + boundary eval)
       ↓                              ↓
  B_paper_le_one_strip         infinite_strip_identity
  (SORRY — via strip identity)  (SORRY — via strip identity)
       ↓                              ↓
  paper_bridge_partial_sum_le   paper_bridge_recurrence_derived (PROVED)
       ↓                              ↓
  paper_bridge_decay (PROVED)   Z_xc_diverges_direct (PROVED)
       ↓                              ↓
  hw_summable_corrected         connective_constant_eq_direct (PROVED)
  (PROVED — Z(x)<∞ for x<xc)       ↓
       ↓                       = main theorem
  connective_constant_eq_direct
```

## Cancellation Identity (Lemma 1) — Status

The cancellation identity (Lemma 1, the vertex relation) is **PROVED**
modulo `pair_winding_relation`, which requires the discrete turning
number theorem for simple closed trails on the hex lattice.

### Proof Chain (cancellation identity)

```
hex_simple_closed_trail_winding (SORRY — turning number theorem)
    ↓
pair_winding_relation (SORRY — winding decomposition)
    ↓
pair_exp_cancellation (PROVED ✓)
    ↓
pair_contrib_cancels (PROVED ✓)
    ↓
pairSigmaInvol_injective (PROVED ✓)
    ↓
freshVertexSum_pair_part_zero_proved (PROVED ✓ — S = -S argument)
    ↓
fresh_vertex_relation (PROVED ✓ — triplet + pair = 0)
    ↓
vertex_relation_at_interior (PROVED ✓ — in SAWStripIdentityFromVR.lean)
    ↓
finite_strip_identity_from_vr (SORRY — discrete Stokes + boundary eval)
```

## Connection: Vertex Relation → Strip Identity (NEW)

`SAWStripIdentityFromVR.lean` establishes the bridge:
- `vertex_relation_at_interior` (PROVED) — wraps `fresh_vertex_relation`
- `finite_strip_identity_from_vr` (SORRY) — the discrete Stokes + boundary evaluation
- `B_paper_le_one_from_vr` (PROVED from strip identity)
- `bridge_partition_bound_from_vr` (PROVED)

The single sorry `finite_strip_identity_from_vr` is equivalent to
both `B_paper_le_one_strip` and `infinite_strip_identity`.

## Remaining Sorries (total: 9)

### Critical path (main theorem):
1. **`infinite_strip_identity`** (SAWRecurrenceProof.lean): The parafermionic
   observable identity for the infinite strip. One of two sorries affecting
   the main theorem.

2. **`B_paper_le_one_strip`** (SAWStripIdentityCorrect.lean): B_paper ≤ 1
   from the strip identity. The other sorry affecting the main theorem
   (via paper_bridge_partial_sum_le → bridge decay → HW bound).

### Critical path (cancellation identity):
3. **`pair_winding_relation`** (SAWPairCancellation.lean): The winding
   decomposition for pair-involution walks. The ONLY sorry affecting
   the cancellation identity `fresh_vertex_relation`.
   **Requires**: the discrete turning number theorem for simple closed
   trails on the hexagonal lattice.

### Consolidation (NEW):
4. **`finite_strip_identity_from_vr`** (SAWStripIdentityFromVR.lean):
   The finite strip identity derived from the vertex relation.
   **Equivalent to** sorries #1 + #2 combined.
   Requires: discrete Stokes argument + boundary evaluation.

### Preparation for future use:
5. **`hex_simple_closed_trail_winding`** (SAWWindingDiff.lean): The discrete
   turning number theorem. Foundation for `pair_winding_relation`.

### Dead branches (may be false, not on critical path):
6. **`trail_vertex_relation`** (SAWCancellationIdentity.lean): Uses StripTrail
   observable which includes non-fresh trails. The vertex relation may NOT
   hold for this observable — use `fresh_vertex_relation` instead.

7. **`triplet_part_zero`** (SAWTrailVertexRelation.lean): Wrong decomposition
   for StripTrails. The FreshTrail decomposition (in SAWVertexRelationProof.lean)
   is the correct one.

8. **`pair_part_zero`** (SAWTrailVertexRelation.lean): Same issue as #7.

9. **`vertex_relation_strip`** (SAWStripObservable.lean): Path-based observable
   with freshness condition has incomplete triplets when extension neighbors
   are already visited. Use trail-based `fresh_vertex_relation` instead.

## Summary

The main theorem `μ = √(2+√2)` depends on **two critical sorries**:
`infinite_strip_identity` and `B_paper_le_one_strip`. Both are consequences
of the strip identity (Lemma 2), which follows from the vertex relation
(Lemma 1) + discrete Stokes summation + boundary evaluation.

The vertex relation `fresh_vertex_relation` (Lemma 1) is **PROVED** modulo
`pair_winding_relation`, which requires the discrete turning number theorem.

The Hammersley-Welsh bound uses `B_paper_le_one_strip` through the chain
`paper_bridge_partial_sum_le → paper_bridge_decay → hw_summable_corrected`.

**NEW**: `SAWStripIdentityFromVR.lean` shows how the vertex relation connects
to the strip identity, consolidating the two critical sorries into a single
sorry (`finite_strip_identity_from_vr`) that represents the discrete Stokes
argument + boundary evaluation.

## File Organization

All files are imported (directly or transitively) by `SAWFinal.lean`.
Dead branches (#6-9) contain useful infrastructure (definitions, lemmas)
that is reused by other files in the proof chain.
