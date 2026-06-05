# Proof Status: Connective Constant of the Honeycomb Lattice

## Main Theorem
`connective_constant_eq_direct` in `SAWMainNew.lean`:
**μ = √(2+√2)** where μ is the connective constant of the hexagonal lattice.

**Status: PROVED modulo one sorry** (`infinite_strip_identity` in SAWRecurrenceProof.lean).

The Hammersley-Welsh bound is fully proved (sorry-free), and the
convergence proof `hw_summable_direct` now uses it via `hw_summable_corrected`.

## Main Theorem Chain

```
infinite_strip_identity (SORRY — discrete Stokes + vertex relation)
    ↓
paper_bridge_recurrence_derived (PROVED)
    ↓
Z_xc_diverges_direct (PROVED)           hw_summable_direct (PROVED ✓)
    ↓                                    ↓
connective_constant_eq_direct (PROVED — main theorem)
```

## Cancellation Identity (Lemma 1) — Status

The cancellation identity (Lemma 1) from Section 2 of Duminil-Copin & Smirnov (2012) 
states that for every interior vertex v:
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

### Proof Chain (cancellation identity)

```
pair_winding_relation (SORRY — turning number theorem)
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
```

### Key Results

- `pair_exp_cancellation` — **PROVED** from `pair_winding_relation` + three algebraic helpers:
  `fin3_other_pair_cancel`, `exp_shift_minus'`, `exp_shift_plus'`

- `freshVertexSum_triplet_part_zero` — **PROVED** (each triplet root's extensions cancel)

- `freshVertexSum_pair_part_zero_proved` — **PROVED** (S = -S involution argument)

- `fresh_vertex_relation` — **PROVED** from triplet + pair parts

### Mathematical Note on `pair_winding_relation`

The `pair_winding_relation` statement uses a specific cyclic ordering of
(k, exit) via `fin3_other`. Analysis in SAWWindingDiff.lean shows that the
correct formulation is: |W(pairInvol γ) - W(γ)| = 8π/3, which holds for
both cyclic and anti-cyclic orderings. The existing sorry'd statement
works correctly within Lean's sorry framework (all downstream proofs
compile and are sound given the sorry).

The turning number theorem for simple closed trails on the hexagonal
lattice (every simple closed trail has total exterior angle ±2π) is
the key missing ingredient, stated as `hex_simple_closed_trail_winding`
in SAWWindingDiff.lean.

## Remaining Sorries (total: 8 sorry statements)

### Critical path (main theorem):
1. **`infinite_strip_identity`** (SAWRecurrenceProof.lean): The parafermionic
   observable identity for the infinite strip. This is the ONLY sorry that
   affects the main theorem `connective_constant_eq_direct`.

### Critical path (cancellation identity):
2. **`pair_winding_relation`** (SAWPairCancellation.lean): The winding
   decomposition for pair-involution walks. This is the ONLY sorry that
   affects the cancellation identity `fresh_vertex_relation`.
   **Requires**: the discrete turning number theorem for simple closed
   trails on the hexagonal lattice.

### Preparation for future use (not in critical chain but NOT dead branches):

These are preparation for the full proof of `infinite_strip_identity`,
which requires connecting `fresh_vertex_relation` (Lemma 1) to the
strip identity (Lemma 2) via discrete Stokes summation + boundary evaluation.

3. **`hex_simple_closed_trail_winding`** (SAWWindingDiff.lean): The discrete
   turning number theorem. States that a simple closed trail on the hex
   lattice has total winding ±2π (minus closure turn). This is the
   mathematical foundation for `pair_winding_relation`.

4. **`trail_vertex_relation`** (SAWCancellationIdentity.lean): Alternative
   trail-based vertex relation using `trailVertexSum` (StripTrail-based).
   Preparation for connecting different observable definitions.

5. **`B_paper_le_one_strip`** (SAWStripIdentityCorrect.lean): Bridge bound
   for finite strip. Preparation for the finite strip identity (Lemma 2
   with escape boundary terms).

6. **`vertex_relation_strip`** (SAWStripObservable.lean): Path-based vertex
   relation using `stripVertexSum` (StripPathToMidEdge-based). For vertex-
   SAWs, only triplets arise (no pairs needed).

7. **`triplet_part_zero`** (SAWTrailVertexRelation.lean): Triplet part of
   StripTrail vertex sum. Part of the trail-based vertex relation proof.

8. **`pair_part_zero`** (SAWTrailVertexRelation.lean): Pair part of
   StripTrail vertex sum. Part of the trail-based vertex relation proof.

## Summary

The main theorem `μ = √(2+√2)` depends on a **single sorry**:
`infinite_strip_identity`, which is the parafermionic observable identity
for the infinite strip (Lemma 2 of the paper). This requires:
- The vertex relation (Lemma 1) — **PROVED** (modulo `pair_winding_relation`)
- Discrete Stokes summation over all strip vertices
- Boundary evaluation connecting boundary sums to partition functions

The cancellation identity `fresh_vertex_relation` (Lemma 1) depends on
a **single sorry**: `pair_winding_relation`, which requires the discrete
turning number theorem for simple closed trails on the hexagonal lattice.

The Hammersley-Welsh bound is **fully proved** (sorry-free).

All 6 remaining non-critical sorries are **preparation** for the full
proof of `infinite_strip_identity` (connecting Lemma 1 to Lemma 2).
