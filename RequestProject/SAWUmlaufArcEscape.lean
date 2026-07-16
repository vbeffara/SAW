import Mathlib
import RequestProject.SAWUmlaufArcInduction

/-!
# Escape from a simple polygonal arc

This file packages the planar arc non-separation theorem into the quantitative
escape statement used by the live Umlaufsatz branch.  Deleting the two edges
incident to a vertex of a simple closed polygon leaves a simple polygonal arc;
its complement is path connected, hence the deleted vertex can be joined to
points of arbitrarily large norm without crossing any remaining edge.

`SAWUmlaufArcBasics` contains the finite-chain definitions,
`SAWUmlaufArcInduction` records the induction and local detour leaf, and this
file is imported by `SAWUmlaufPolygon`, where
`polygon_nonincident_edges_form_simpleArc` and
`vertex_escape_joinedIn_arbitrarily_far_no_diag` consume the result.  All three
files are therefore explicitly linked to the main theorem.
-/

open Real Complex

noncomputable section

namespace HexArea

/-- Compatibility statement in the original union-of-segments presentation.
The proof is an immediate bridge to the induction theorem over `chainCarrier`.
-/
lemma simpleArc_complement_isPathConnected (L : List ℂ)
    (hsimple : PlaneArcSimple L) :
    IsPathConnected ((⋃ e ∈ chainEdges L, segment ℝ e.1 e.2)ᶜ) := by
  simpa [chainCarrier] using simpleArc_complement_isPathConnected_inductive L hsimple

/-- A point in the complement of a simple polygonal arc can be joined, within
that complement, to points of arbitrarily large norm.  This is the exact output
consumed by the boundary-vertex escape theorem in `SAWUmlaufPolygon`. -/
lemma simpleArc_joinedIn_arbitrarily_far (L : List ℂ)
    (hsimple : PlaneArcSimple L) (x : ℂ)
    (hx : x ∈ ((⋃ e ∈ chainEdges L, segment ℝ e.1 e.2)ᶜ)) :
    ∀ R : ℝ, ∃ y : ℂ, R < ‖y‖ ∧
      JoinedIn ((⋃ e ∈ chainEdges L, segment ℝ e.1 e.2)ᶜ) x y := by
  intro R
  obtain ⟨B, hBpos, hB⟩ := HexArea.exists_norm_bound_segments (chainEdges L)
  obtain ⟨y, hyHull, hyNorm⟩ :=
    HexArea.exists_not_mem_convexHull_list_norm_gt L (max R B)
  have hyB : B < ‖y‖ := lt_of_le_of_lt (le_max_right R B) hyNorm
  have hyR : R < ‖y‖ := lt_of_le_of_lt (le_max_left R B) hyNorm
  have hy : y ∈ ((⋃ e ∈ chainEdges L, segment ℝ e.1 e.2)ᶜ) :=
    HexArea.mem_compl_iUnion_segments_of_norm_gt (chainEdges L) B y hB hyB
  exact ⟨y, hyR, (simpleArc_complement_isPathConnected L hsimple).joinedIn x hx y hy⟩

end HexArea
