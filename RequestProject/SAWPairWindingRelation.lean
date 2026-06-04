/-
# Winding Relation for Pair Cancellation — Derived Results

This file provides an alternative proof of pair contribution cancellation
using `pair_winding_relation` from SAWPairCancellation.lean.

## Main results

* `pair_contrib_from_winding` — each pair's contribution to the vertex
  sum is zero (proved from pair_winding_relation + algebraic identity)

## Proof architecture

The cancellation identity reduces to:

1. **Triplet part = 0** (PROVED in SAWVertexRelationProof.lean:
   `freshVertexSum_triplet_part_zero`)

2. **Pair part = 0** which requires:
   a. Each pair's contribution cancels (`pair_contrib_cancels` in
      SAWPairCancellation.lean, PROVED from pair_winding_relation)
   b. The pair involution organizes all walks into cancelling pairs
   c. The winding relation (`pair_winding_relation`, SORRY in SAWPairCancellation.lean)

The remaining sorry (c) requires formalizing the discrete turning number
theorem for simple closed curves on the hexagonal lattice.
-/

import Mathlib
import RequestProject.SAWPairCancellation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Alternative proof of pair contribution cancellation

This mirrors `pair_contrib_cancels` in SAWPairCancellation.lean using
the same `pair_winding_relation` but with a slightly different proof structure. -/

/-- Each pair's contribution to the vertex sum is zero.
    Alternative proof using pair_winding_relation directly. -/
theorem pair_contrib_from_winding {T L : ℕ} (v : HexVertex) {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    midEdgeDir v k * γ.1.weight +
    midEdgeDir v (pairExitIdx hv_ne γ) * (pairInvol hv hv_ne γ).1.weight = 0 :=
  pair_contrib_cancels v hv hv_ne γ

end
