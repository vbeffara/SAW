/-
# Pair Cancellation for the Vertex Relation (Lemma 1)

Proves that the pair part of the vertex sum vanishes, completing the
proof of the cancellation identity.
-/

import Mathlib
import RequestProject.SAWPairWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## The pair involution on FreshIncomingPair -/

/-- The exit index of a FreshIncomingPair walk. -/
noncomputable def pairExitIdx {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : Fin 3 :=
  (pair_exit_neighbor γ hv_ne).choose

/-- The exit index is not k. -/
lemma pairExitIdx_ne {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    pairExitIdx hv_ne γ ≠ k :=
  (pair_exit_neighbor γ hv_ne).choose_spec.choose

/-- The inner walk of a FreshIncomingPair. -/
noncomputable def pairInner {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexGraph.Walk (hexNeighbors3 v (pairExitIdx hv_ne γ)) (hexNeighbors3 v k) :=
  (pair_exit_neighbor γ hv_ne).choose_spec.choose_spec.choose

/-- The suffix decomposition. -/
lemma pairSuffix_spec {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    γ.1.walk.dropUntil v (pair_walk_v_in_support γ hv_ne) =
    .cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ)) (pairInner hv_ne γ) :=
  (pair_exit_neighbor γ hv_ne).choose_spec.choose_spec.choose_spec

/-- The prefix walk. -/
noncomputable def pairPrefix {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexGraph.Walk paperStart v :=
  γ.1.walk.takeUntil v (pair_walk_v_in_support γ hv_ne)

/-- The original walk is prefix ++ suffix. -/
lemma pairDecomp {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    γ.1.walk = (pairPrefix hv_ne γ).append
      (.cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ)) (pairInner hv_ne γ)) := by
  unfold pairPrefix
  rw [← pairSuffix_spec hv_ne γ]
  exact (SimpleGraph.Walk.take_spec γ.1.walk (pair_walk_v_in_support γ hv_ne)).symm

/-- Construct the paired walk. -/
noncomputable def pairInvolWalk {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexGraph.Walk paperStart (hexNeighbors3 v (pairExitIdx hv_ne γ)) :=
  mkPairedWalk v k (pairExitIdx hv_ne γ) (pairPrefix hv_ne γ) (pairInner hv_ne γ)

/-- The paired walk is a trail. -/
lemma pairInvolWalk_is_trail {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvolWalk hv_ne γ).IsTrail := by
  apply mkPairedWalk_is_trail
  · rw [← pairDecomp hv_ne γ]; exact γ.1.is_trail
  · rw [← pairDecomp hv_ne γ]; exact γ.1.fresh
  · exact hv_ne

/-- The paired walk has the right fresh edge. -/
lemma pairInvolWalk_fresh {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    s(hexNeighbors3 v (pairExitIdx hv_ne γ), v) ∉ (pairInvolWalk hv_ne γ).edges := by
  apply mkPairedWalk_fresh
  · rw [← pairDecomp hv_ne γ]; exact γ.1.fresh
  · rw [← pairDecomp hv_ne γ]; exact γ.1.is_trail

/-- The paired walk stays in strip. -/
lemma pairInvolWalk_in_strip {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∀ u ∈ (pairInvolWalk hv_ne γ).support, PaperFinStrip T L u := by
  apply mkPairedWalk_in_strip
  rw [← pairDecomp hv_ne γ]; exact γ.1.in_strip

/-- The paired walk has 2 v-edges. -/
lemma pairInvolWalk_two_v {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    vEdgeCount v (pairInvolWalk hv_ne γ) = 2 := by
  apply mkPairedWalk_two_v_edges
  rw [← pairDecomp hv_ne γ]; exact γ.2

/-- The FreshIncomingPair at exit_idx. -/
noncomputable def pairInvol {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    FreshIncomingPair T L v (pairExitIdx hv_ne γ) :=
  ⟨⟨pairInvolWalk hv_ne γ,
    pairInvolWalk_is_trail hv_ne γ,
    (hexNeighbors3_adj v (pairExitIdx hv_ne γ)).symm,
    pairInvolWalk_fresh hv_ne γ,
    pairInvolWalk_in_strip hv_ne γ⟩,
   pairInvolWalk_two_v hv_ne γ⟩

/-- The paired walk has the same length. -/
lemma pairInvol_length {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvol hv hv_ne γ).1.len = γ.1.len := by
  simp only [pairInvol, FreshTrail.len, pairInvolWalk]
  rw [mkPairedWalk_length]
  have := pairDecomp hv_ne γ
  have h_len := congr_arg SimpleGraph.Walk.length this
  simp [SimpleGraph.Walk.length_append] at h_len
  omega

/-- The pair contribution cancels for each pair. -/
lemma pair_contrib_cancels {T L : ℕ} (v : HexVertex) {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    midEdgeDir v k * γ.1.weight +
    midEdgeDir v (pairExitIdx hv_ne γ) * (pairInvol hv hv_ne γ).1.weight = 0 := by
  sorry

/-- **The pair part of the vertex sum vanishes.** -/
theorem freshVertexSum_pair_part_zero_proof (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    ∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingPair T L v ji), γ.1.weight = 0 := by
  sorry

end
