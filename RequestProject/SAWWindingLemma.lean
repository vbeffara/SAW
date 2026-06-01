/-
# Winding Append Lemma

Proves that appending a vertex to a walk changes the winding by
the turning angle at the junction. This is the key geometric ingredient
for the cancellation identity.

## Main results

* `hexWalkWinding_snoc` — winding of L ++ [w] in terms of winding of L
* `extension_winding_general` — winding of triplet extension for general j
-/

import Mathlib
import RequestProject.SAWCancellationProved

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Winding append lemma

hexWalkWinding is defined recursively on triples of consecutive vertices.
Appending a new vertex w to a list L adds one turning angle. -/

/-
Appending a vertex to a list M ++ [x, a] adds the turning angle at a.
-/
lemma hexWalkWinding_snoc (x a b : HexVertex) (M : List HexVertex) :
    hexWalkWinding (M ++ [x, a, b]) =
    hexWalkWinding (M ++ [x, a]) +
    Complex.arg ((correctHexEmbed b - correctHexEmbed a) /
                 (correctHexEmbed a - correctHexEmbed x)) := by
  induction' M with v₀ M ih;
  · exact add_comm _ _;
  · rcases M with ( _ | ⟨ v₁, _ | ⟨ v₂, M ⟩ ⟩ ) <;> simp_all +decide [ hexWalkWinding ]; all_goals ring

/-- Walk support append lemma for extensions. -/
lemma walk_support_append_singleton {s u v : HexVertex}
    (w : hexGraph.Walk s u) (hadj : hexGraph.Adj u v) :
    (w.append (.cons hadj .nil)).support = w.support ++ [v] := by
  simp [SimpleGraph.Walk.support_append]

/-
The last vertex of a walk's support is its endpoint.
-/
lemma walk_support_getLast {s t : HexVertex} (w : hexGraph.Walk s t)
    (h : 0 < w.length) : w.support.getLast! = t := by
  induction w <;> simp_all +decide [ SimpleGraph.Walk.support, List.getLast! ]

/-- For a strip trail's walk support, the last element is the endpoint. -/
lemma stripTrail_walk_support_last {T L : ℕ} {prev next : HexVertex}
    (γ : StripTrail T L prev next)
    (h : 0 < γ.walk.length) :
    γ.walk.support.getLast! = prev := by
  exact walk_support_getLast γ.walk h

/-! ## Extension winding for general j

The critical result: extending a 0-v-edge incoming trail at n_j
by adding edge {n_j, v} changes the winding.

For the extension at n_k = (fin3_other j).1:
  winding changes by -π/3 (clockwise turn)

For the extension at n_l = (fin3_other j).2:
  winding changes by +π/3 (counterclockwise turn)
-/

/-
The winding of the extension at the clockwise neighbor.
-/
lemma extension_winding_cw {T L : ℕ} (v : HexVertex) (idx : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v idx) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv_strip : PaperFinStrip T L v)
    (hlen : 1 ≤ γ.walk.length) :
    (tripletExtendStrip v idx (fin3_other idx).1 γ h_no_v hv_strip).winding =
    γ.winding - Real.pi / 3 := by
  unfold StripTrail.winding StripTrail.fullSupport tripletExtendStrip;
  convert hexWalkWinding_snoc ( hexNeighbors3 v idx ) v ( hexNeighbors3 v ( fin3_other idx |>.1 ) ) ( γ.walk.support.dropLast ) using 1;
  · simp +decide [ walk_support_append_singleton, List.dropLast ];
    rw [ ← List.dropLast_append_getLast ( by aesop_cat : γ.walk.support ≠ [ ] ) ] ; simp +decide [ List.dropLast ] ;
  · rw [ show γ.walk.support = γ.walk.support.dropLast ++ [ hexNeighbors3 v idx ] from ?_ ];
    · grind +suggestions;
    · rw [ List.dropLast_append_getLast? ];
      rw [ List.getLast?_eq_getElem? ];
      rw [ List.getElem?_eq_getElem ] <;> norm_num [ hlen ]

/-
The winding of the extension at the counterclockwise neighbor.
-/
lemma extension_winding_ccw {T L : ℕ} (v : HexVertex) (idx : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v idx) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv_strip : PaperFinStrip T L v)
    (hlen : 1 ≤ γ.walk.length) :
    (tripletExtendStrip v idx (fin3_other idx).2 γ h_no_v hv_strip).winding =
    γ.winding + Real.pi / 3 := by
  -- Apply the lemma hexWalkWinding_snoc to the extended trail's full support.
  have h_winding : hexWalkWinding (γ.walk.support ++ [v, hexNeighbors3 v (fin3_other idx).2]) = hexWalkWinding (γ.walk.support ++ [v]) + Real.pi / 3 := by
    rw [ ← turning_angle_counterclockwise v idx ];
    convert hexWalkWinding_snoc ( hexNeighbors3 v idx ) v ( hexNeighbors3 v ( fin3_other idx ).2 ) ( γ.walk.support.dropLast ) using 1;
    · rw [ ← List.dropLast_append_getLast ( by aesop_cat : γ.walk.support ≠ [ ] ) ];
      simp +decide [ List.dropLast ];
    · rw [ ← List.dropLast_append_getLast ( by aesop_cat : γ.walk.support ≠ [ ] ) ];
      simp +decide [ List.dropLast ];
  convert h_winding using 1;
  unfold StripTrail.winding StripTrail.fullSupport tripletExtendStrip; simp +decide [ walk_support_append_singleton ] ;

/-! ## Triplet sum for strip trails

Using the winding and length relations, each triplet's contribution
to the vertex relation sum is zero. -/

/-- Each triplet from a 0-v-edge root sums to zero. -/
theorem strip_trail_triplet_vanishes {T L : ℕ} (v : HexVertex) (idx : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v idx) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv_strip : PaperFinStrip T L v)
    (hlen : 1 ≤ γ.walk.length) :
    midEdgeDir v idx * γ.weight +
    midEdgeDir v (fin3_other idx).1 *
      (tripletExtendStrip v idx (fin3_other idx).1 γ h_no_v hv_strip).weight +
    midEdgeDir v (fin3_other idx).2 *
      (tripletExtendStrip v idx (fin3_other idx).2 γ h_no_v hv_strip).weight = 0 := by
  -- Use winding and length relations
  have h_len_k := tripletExtendStrip_len v idx (fin3_other idx).1 γ h_no_v hv_strip
  have h_len_l := tripletExtendStrip_len v idx (fin3_other idx).2 γ h_no_v hv_strip
  have h_wind_k := extension_winding_cw v idx γ h_no_v hv_strip hlen
  have h_wind_l := extension_winding_ccw v idx γ h_no_v hv_strip hlen
  -- Now ext_k has winding = γ.winding - π/3 and len = γ.len + 1
  -- And ext_l has winding = γ.winding + π/3 and len = γ.len + 1
  unfold StripTrail.weight at *
  rw [h_wind_k, h_wind_l, h_len_k, h_len_l]
  exact triplet_algebraic_zero v idx γ.winding γ.len

end