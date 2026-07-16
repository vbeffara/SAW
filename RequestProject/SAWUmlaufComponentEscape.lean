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
A nonconstant forward ray supplies the connected-reaching certificates.
This links the earlier straight-ray route to the more general bent-route
interface without making straightness a requirement of the Umlaufsatz core.
-/
lemma connected_reaches_of_ray (U : Set ℂ) (x d : ℂ) (hd : d ≠ 0)
    (hray : ∀ t : ℝ, 0 ≤ t → x + (t : ℂ) * d ∈ U) :
    ∀ R : ℝ, ∃ C : Set ℂ,
      IsConnected C ∧ x ∈ C ∧ C ⊆ U ∧ ∃ y ∈ C, R < ‖y‖ := by
  intro R
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 ≤ t ∧ R < ‖x + t * d‖ := by
    -- By the properties of the norm, we can find such a $t$.
    have ht_exists : ∃ t : ℝ, 0 ≤ t ∧ ‖t * d‖ > R + ‖x‖ := by
      norm_num +zetaDelta at *;
      exact ⟨ ⌊ ( R + ‖x‖ ) / ‖d‖⌋₊ + 1, by positivity, by rw [ abs_of_nonneg ( by positivity ) ] ; nlinarith [ Nat.lt_floor_add_one ( ( R + ‖x‖ ) / ‖d‖ ), norm_pos_iff.mpr hd, mul_div_cancel₀ ( R + ‖x‖ ) ( norm_ne_zero_iff.mpr hd ) ] ⟩;
    obtain ⟨ t, ht₁, ht₂ ⟩ := ht_exists; exact ⟨ t, ht₁, by have := norm_sub_le ( x + t * d ) x; norm_num at *; linarith ⟩ ;
  refine' ⟨ Set.image ( fun t : ℝ => x + t * d ) ( Set.Ici 0 ), _, _, _, _ ⟩;
  · exact ⟨ Set.Nonempty.image _ ⟨ 0, by norm_num ⟩, isPreconnected_Ici.image _ <| Continuous.continuousOn <| by continuity ⟩;
  · exact ⟨ 0, by norm_num ⟩;
  · exact Set.image_subset_iff.mpr hray;
  · exact ⟨ _, ⟨ t, ht.1, rfl ⟩, ht.2 ⟩

end HexArea