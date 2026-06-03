/-
# Winding Relation for Pair Cancellation

Establishes the key winding relation for the pair involution and
derives the pair cancellation from it. This file reduces the
cancellation identity (Lemma 1) to a single geometric fact.

## Main results

* `pair_winding_relation` — the suffix winding is ±4π/3 (sorry:
  requires the turning number theorem for simple curves on the hex
  lattice in a simply-connected domain)
* `pair_contrib_from_winding` — each pair's contribution to the vertex
  sum is zero (proved from pair_winding_relation + algebraic identity)

## Proof architecture

The cancellation identity reduces to:

1. **Triplet part = 0** (PROVED in SAWVertexRelationProof.lean:
   `freshVertexSum_triplet_part_zero`)

2. **Pair part = 0** which requires:
   a. Each pair's contribution cancels (`pair_contrib_from_winding`, PROVED here)
   b. The pair involution organizes all walks into cancelling pairs
   c. The winding relation (`pair_winding_relation`, SORRY)

The remaining gap (c) is a consequence of:
- The turning number theorem for simple closed curves (winding = ±2π)
- The hex lattice geometry (exterior angles are ±π/3)
- The simply-connected domain constraining the loop orientation
-/

import Mathlib
import RequestProject.SAWPairCancellation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Pair winding relation

**Key geometric fact** (from the paper, using simply-connected topology):

For a FreshIncomingPair γ at k with exit through exit_idx, the walk
decomposes as prefix (start → v) + suffix (v → n_exit → inner → n_k).

The suffix traverses a near-complete loop at v. In a simply-connected
domain, the loop's turning number is exactly 1 (counterclockwise) or
-1 (clockwise), giving total turning ±2π. Combined with the hex lattice
geometry (exterior angle at v = ±π/3), the suffix winding is exactly
-4π/3 for the original walk and +4π/3 for the paired walk (or vice versa).

This is Equation (2) in the proof of Lemma 1 in:
  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

The proof uses: "the fact that a is on the boundary and Ω is simply connected." -/

/-- The winding relation for pairs: there exists W_common and j such that
    the windings match the pair algebraic identity structure.

    This encapsulates the turning number theorem on the hex lattice. -/
lemma pair_winding_relation {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∃ (W_common : ℝ) (j : Fin 3),
      k = (fin3_other j).1 ∧ pairExitIdx hv_ne γ = (fin3_other j).2 ∧
      γ.1.winding = W_common - 4 * Real.pi / 3 ∧
      (pairInvol hv hv_ne γ).1.winding = W_common + 4 * Real.pi / 3 ∧
      (pairInvol hv hv_ne γ).1.len = γ.1.len := by
  sorry

/-! ## Pair contribution cancels (from winding relation)

Using the winding relation and the algebraic pair identity
  j · conj(λ)⁴ + conj(j) · λ⁴ = 0
the contribution of each pair to the vertex sum is zero. -/

/-- Each pair's contribution to the vertex sum is zero.

    **Proof**: From pair_winding_relation, the windings satisfy
    W(γ) = W ∓ 4π/3, W(pair) = W ± 4π/3 with matching indices.
    Substituting into the vertex contribution and applying
    `pair_contrib_zero_at_vertex` gives zero. -/
theorem pair_contrib_from_winding {T L : ℕ} (v : HexVertex) {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    midEdgeDir v k * γ.1.weight +
    midEdgeDir v (pairExitIdx hv_ne γ) * (pairInvol hv hv_ne γ).1.weight = 0 := by
  obtain ⟨W, j, hk, hexit, hw_γ, hw_pair, h_len⟩ := pair_winding_relation hv hv_ne γ
  unfold FreshTrail.weight
  rw [hw_γ, hw_pair, h_len]
  have h := pair_contrib_zero_at_vertex v j W γ.1.len
  simp only [fin3_other, trailVertexContrib] at h
  fin_cases j <;> simp only [fin3_other] at hk hexit h <;> {
    subst hk; rw [hexit]; exact h
  }

end
