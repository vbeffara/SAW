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
fin3_other_pair_cancel (PROVED — algebraic, from pair_cancellation)
  + exp_shift_minus' / exp_shift_plus' (PROVED — exponential identities)
    ↓
pair_exp_cancellation (PROVED ✓ — from pair_winding_relation + algebra)
    ↓
pair_contrib_cancels (PROVED — factors out xc^ℓ)
    ↓
pairSigmaInvol_injective (PROVED ✓)
    ↓
freshVertexSum_pair_part_zero_proved (PROVED — S = -S argument)
    ↓
fresh_vertex_relation (PROVED — triplet + pair = 0)
```

### Key Improvement: pair_exp_cancellation now PROVED

`pair_exp_cancellation` was previously sorry'd. It is now **proved** from
`pair_winding_relation` + three algebraic helper lemmas:

1. `fin3_other_pair_cancel` — for each j_idx, the midEdgeDir-weighted
   conj(λ)⁴ and λ⁴ terms cancel. Proved by fin_cases from `pair_cancellation`.

2. `exp_shift_minus'` — exp(-iσ(W - 4π/3)) = exp(-iσW) · conj(λ)⁴.
   Proved from σ = 5/8 and the exponential identities.

3. `exp_shift_plus'` — exp(-iσ(W + 4π/3)) = exp(-iσW) · λ⁴.
   Proved similarly.

The proof factors out exp(-iσW_common) and uses `linear_combination`.

## Remaining Sorries (total: 8 sorry statements)

### Critical path (main theorem):
1. **`infinite_strip_identity`** (SAWRecurrenceProof.lean): The parafermionic
   observable identity for the infinite strip. This is the ONLY sorry that
   affects the main theorem `connective_constant_eq_direct`.

### Critical path (cancellation identity):
2. **`pair_winding_relation`** (SAWPairCancellation.lean): The winding
   decomposition for pair-involution walks. States that the windings of γ
   and pairInvol(γ) are W_common ± 4π/3. This is the ONLY sorry that
   affects the cancellation identity `fresh_vertex_relation`.
   **Requires**: the discrete turning number theorem for simple closed
   trails on the hexagonal lattice.

### Alternative formulations (not in critical chain):
3. **`freshVertexSum_pair_part_zero_proof`** (SAWPairCancellation.lean):
   Redundant with `freshVertexSum_pair_part_zero_proved` in
   SAWPairInvolutionProof.lean. Not used by any other lemma.
4. **`trail_vertex_relation`** (SAWCancellationIdentity.lean): Alternative
   trail-based vertex relation.
5. **`B_paper_le_one_strip`** (SAWStripIdentityCorrect.lean): Bridge bound
   for finite strip (alternative proof path).
6. **`vertex_relation_strip`** (SAWStripObservable.lean): Strip vertex
   relation using `stripVertexSum` definition.
7. **`triplet_part_zero`** (SAWTrailVertexRelation.lean): Triplet part of
   StripTrail vertex sum.
8. **`pair_part_zero`** (SAWTrailVertexRelation.lean): Pair part of
   StripTrail vertex sum.

## Summary

The main theorem `μ = √(2+√2)` depends on a **single sorry**:
`infinite_strip_identity`, which is the parafermionic observable identity
for the infinite strip (Lemma 2 of the paper). This requires the full
discrete Stokes argument connecting the vertex relation to the strip
partition functions.

The cancellation identity `fresh_vertex_relation` (Lemma 1) depends on
a **single sorry**: `pair_winding_relation`, which requires the discrete
turning number theorem for simple closed trails on the hexagonal lattice.
The algebraic step connecting `pair_winding_relation` to `pair_exp_cancellation`
is now fully proved.

The Hammersley-Welsh bound is **fully proved** (sorry-free).
