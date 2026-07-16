import Mathlib

/-!
# Connected escape certificates for the polygonal Umlaufsatz

This file isolates a general topological interface for the one remaining
unbounded-component step in the polygonal Umlaufsatz.  It is not a dead branch:
`RequestProject.SAWUmlaufPolygon` imports it, and its live theorem
`vertex_escape_component_unbounded` explicitly reduces to the certificate below.

The useful point is that a straight ray is not required.  For every radius it
is enough to exhibit *some connected subset* of the forbidden-segment
complement which contains the source and reaches past that radius.  Thus a
family of bent polygonal escape routes can discharge the same component goal.
-/

open Real Complex Topology

noncomputable section

namespace HexArea

/-
A connected component is unbounded if, for every radius, a connected subset
of the ambient set contains the source and reaches a point beyond that radius.
This is the component-level interface intended for finite polygonal escape
constructions in the Umlaufsatz proof.
-/
lemma connectedComponentIn_unbounded_of_connected_reaches
    (U : Set ℂ) (x : ℂ)
    (hreach : ∀ R : ℝ, ∃ C : Set ℂ,
      IsConnected C ∧ x ∈ C ∧ C ⊆ U ∧ ∃ y ∈ C, R < ‖y‖) :
    ¬ Bornology.IsBounded (connectedComponentIn U x) := by
  -- Assume the connected component is bounded.
  by_contra h_bounded
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y ∈ connectedComponentIn U x, ‖y‖ ≤ R := by
    exact h_bounded.exists_norm_le.imp fun R hR y hy => hR y hy;
  obtain ⟨ C, hC₁, hC₂, hC₃, y, hy₁, hy₂ ⟩ := hreach R; exact not_le_of_gt hy₂ ( hR y <| hC₁.isPreconnected.subset_connectedComponentIn hC₂ hC₃ hy₁ ) ;

/-
Paths to arbitrarily distant points supply connected-reaching
certificates.  This is the path-level interface used by the bent-route branch
of the polygonal Umlaufsatz: the image of each path is the required connected
set.  It sits strictly between the geometric routing problem and the abstract
connected-component conversion above.

A list of cardinality at most one is either empty or a singleton.
This elementary split is consumed by the live polygonal escape leaf to separate
the exterior-boundary problem from the one-valid-diagonal problem.
-/
lemma eq_nil_or_eq_singleton_of_length_le_one {α : Type*} (L : List α)
    (hL : L.length ≤ 1) : L = [] ∨ ∃ a, L = [a] := by
  cases L <;> aesop

lemma connected_reaches_of_joinedIn (U : Set ℂ) (x : ℂ)
    (hpath : ∀ R : ℝ, ∃ y : ℂ, R < ‖y‖ ∧ JoinedIn U x y) :
    ∀ R : ℝ, ∃ C : Set ℂ,
      IsConnected C ∧ x ∈ C ∧ C ⊆ U ∧ ∃ y ∈ C, R < ‖y‖ := by
  intro R;
  cases' hpath R with y hy;
  obtain ⟨ γ, hγ ⟩ := hy.2;
  refine' ⟨ Set.range γ, _, _, _, _ ⟩;
  · exact isConnected_range γ.continuous;
  · exact ⟨ 0, γ.source ⟩;
  · exact Set.range_subset_iff.mpr hγ;
  · exact ⟨ y, ⟨ 1, by simp +decide ⟩, hy.1 ⟩

/-
A nonconstant avoiding ray also supplies paths to arbitrarily distant
points.  This is the direct bridge from a future finite-geometry ray
construction to `connected_reaches_of_joinedIn`; unlike
`connected_reaches_of_ray`, it preserves the path witness needed by downstream
polygonal routing.
-/
lemma joinedIn_arbitrarily_far_of_ray (U : Set ℂ) (x d : ℂ) (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → x + (t : ℂ) * d ∈ U) :
    ∀ R : ℝ, ∃ y : ℂ, R < ‖y‖ ∧ JoinedIn U x y := by
  intro R
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ R < ‖x + t * d‖ := by
    -- By the properties of the norm, we can find such a $t$.
    have ht_exists : ∃ t : ℝ, 0 ≤ t ∧ ‖t • d‖ > R + ‖x‖ := by
      norm_num [ norm_smul ];
      exact ⟨ ⌊ ( R + ‖x‖ ) / ‖d‖⌋₊ + 1, by positivity, by rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.lt_floor_add_one ( ( R + ‖x‖ ) / ‖d‖ ), norm_pos_iff.mpr hd, mul_div_cancel₀ ( R + ‖x‖ ) ( norm_ne_zero_iff.mpr hd ) ] ⟩;
    obtain ⟨ t, ht₀, ht ⟩ := ht_exists; exact ⟨ t, ht₀, by have := norm_sub_le ( x + t * d ) x; norm_num at *; linarith ⟩ ;
  refine' ⟨ x + t * d, ht.2, _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  refine' ⟨ fun s => x + s.val * t * d, _ ⟩;
  exacts [ by continuity, by norm_num, by norm_num, fun s => by simpa [ mul_assoc ] using hray ( s * t ) ( mul_nonneg s.2.1 ht.1 ) ]

/-- A nonconstant forward ray supplies connected-reaching certificates.
This now explicitly factors through the path-level interface above, linking the
straight-ray preparation to the live bent-route branch. -/
lemma connected_reaches_of_ray (U : Set ℂ) (x d : ℂ) (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → x + (t : ℂ) * d ∈ U) :
    ∀ R : ℝ, ∃ C : Set ℂ,
      IsConnected C ∧ x ∈ C ∧ C ⊆ U ∧ ∃ y ∈ C, R < ‖y‖ := by
  exact connected_reaches_of_joinedIn U x
    (joinedIn_arbitrarily_far_of_ray U x d hd hray)

end HexArea