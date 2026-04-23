/-
# Additional walk infrastructure for bridge decomposition

Proves properties of walk splitting, diagCoord bounds, and
bridge extraction that are needed for the HW decomposition.
-/

import Mathlib
import RequestProject.SAWHWDecompProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk width -/

/-- Width of a walk: max diagCoord - min diagCoord. -/
def walkWidth {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  walkMaxDiagCoord p - walkMinDiagCoord p

/-- Walk width is non-negative. -/
lemma walkWidth_nonneg {v w : HexVertex} (p : hexGraph.Walk v w) :
    0 ≤ walkWidth p := by
  unfold walkWidth
  obtain ⟨u, hu, _⟩ := walkMinDiagCoord_achieved p
  have h2 := walkMaxDiagCoord_ge p u hu
  linarith [walkMinDiagCoord_le p u hu]

/-
Walk width ≤ walk length.
-/
lemma walkWidth_le_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkWidth p ≤ p.length := by
      obtain ⟨ u₁, hu₁ ⟩ := walkMinDiagCoord_achieved p;
      obtain ⟨ u₂, hu₂ ⟩ := walkMaxDiagCoord_achieved p;
      -- By walk_split_at_vertex, we can split the walk into two parts: from u₁ to u₂ and from u₂ to u₁.
      obtain ⟨p₁, p₂, hp⟩ : ∃ p₁ : hexGraph.Walk v u₁, ∃ p₂ : hexGraph.Walk u₁ w, p = p₁.append p₂ := by
        exact ⟨ p.takeUntil u₁ hu₁.1, p.dropUntil u₁ hu₁.1, by simp +decide ⟩;
      by_cases hu₂₁ : u₂ ∈ p₁.support;
      · obtain ⟨p₁', p₂', hp'⟩ : ∃ p₁' : hexGraph.Walk v u₂, ∃ p₂' : hexGraph.Walk u₂ u₁, p₁ = p₁'.append p₂' := by
          exact ⟨ p₁.takeUntil u₂ hu₂₁, p₁.dropUntil u₂ hu₂₁, by simp +decide ⟩;
        have := walk_diagCoordZ_bound p₂' u₁; simp_all +decide ;
        unfold walkWidth; linarith;
      · obtain ⟨p₃, p₄, hp₃⟩ : ∃ p₃ : hexGraph.Walk u₁ u₂, ∃ p₄ : hexGraph.Walk u₂ w, p₂ = p₃.append p₄ := by
          use p₂.takeUntil u₂ (by
          aesop), p₂.dropUntil u₂ (by
          aesop)
          generalize_proofs at *;
          exact?;
        have h_walkWidth_le_length : diagCoordZ u₂ - diagCoordZ u₁ ≤ p₃.length := by
          have := walk_diagCoordZ_bound p₃ u₂; aesop;
        simp_all +decide [ walkWidth ];
        linarith

/-- The min diagCoord vertex exists in every walk. -/
lemma walk_has_min_vertex {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, ∀ z ∈ p.support, diagCoordZ u ≤ diagCoordZ z := by
  obtain ⟨u, hu, hmin⟩ := walkMinDiagCoord_achieved p
  exact ⟨u, hu, fun z hz => hmin ▸ walkMinDiagCoord_le p z hz⟩

/-- The max diagCoord vertex exists in every walk. -/
lemma walk_has_max_vertex {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, ∀ z ∈ p.support, diagCoordZ z ≤ diagCoordZ u := by
  obtain ⟨u, hu, hmax⟩ := walkMaxDiagCoord_achieved p
  exact ⟨u, hu, fun z hz => hmax ▸ walkMaxDiagCoord_ge p z hz⟩

/-! ## Prefix and suffix diagCoord bounds -/

/-- Vertices in the takeUntil prefix have diagCoord ≥ the min. -/
lemma takeUntil_min_le {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support)
    (hmin : ∀ z ∈ p.support, diagCoordZ u ≤ diagCoordZ z)
    (z : HexVertex) (hz : z ∈ (p.takeUntil u hu).support) :
    diagCoordZ u ≤ diagCoordZ z :=
  hmin z (SimpleGraph.Walk.support_takeUntil_subset p hu hz)

/-- Vertices in the dropUntil suffix have diagCoord ≥ the min. -/
lemma dropUntil_min_le' {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support)
    (hmin : ∀ z ∈ p.support, diagCoordZ u ≤ diagCoordZ z)
    (z : HexVertex) (hz : z ∈ (p.dropUntil u hu).support) :
    diagCoordZ u ≤ diagCoordZ z :=
  hmin z (SimpleGraph.Walk.support_dropUntil_subset p hu hz)

/-! ## Walk splitting preserves total length -/

/-- Splitting a walk preserves total length. -/
lemma walk_split_total_length {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    (p.takeUntil u hu).length + (p.dropUntil u hu).length = p.length := by
  conv_rhs => rw [← SimpleGraph.Walk.take_spec p hu]
  exact (SimpleGraph.Walk.length_append _ _).symm

end