import Mathlib
import RequestProject.SAWUmlaufHullExterior

/-!
# Escape from a simple polygonal arc

This file isolates the topological theorem needed by the live Umlaufsatz
escape branch.  Deleting the two edges incident to a vertex of a simple closed
polygon leaves a simple polygonal **arc**.  The complement of such an arc in the
plane is path connected, hence the deleted vertex can be joined to points of
arbitrarily large norm without crossing any remaining edge.

The file is imported by `SAWUmlaufPolygon`, where
`closedEdges_filter_eq_chainEdges_rotate` identifies the forbidden edges with
the edges of the arc and `vertex_escape_joinedIn_arbitrarily_far_no_diag`
consumes `simpleArc_joinedIn_arbitrarily_far`.  Thus this is preparation for the
main Umlaufsatz theorem, not a dead branch.
-/

open Real Complex

noncomputable section

namespace HexArea

/-- Consecutive directed edges of an open vertex chain. -/
def chainEdges (L : List ℂ) : List (ℂ × ℂ) := L.zip L.tail

/-- A polygonal arc has distinct vertices and nonincident edges are disjoint.
Adjacent edges are allowed to meet at their shared endpoint. -/
def PlaneArcSimple (L : List ℂ) : Prop :=
  L.Nodup ∧
  ∀ e₁ ∈ chainEdges L, ∀ e₂ ∈ chainEdges L,
    e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
      Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2)

/-- The finite union of segments carried by an open chain is closed. -/
lemma isClosed_iUnion_chainEdges (L : List ℂ) :
    IsClosed (⋃ e ∈ chainEdges L, segment ℝ e.1 e.2) := by
  simpa using (HexArea.isOpen_compl_iUnion_segments (chainEdges L)).isClosed_compl

/-- **Polygonal-arc complement theorem.**  A simple embedded polygonal arc does
not separate the plane.  This is the precise planar-topology residue of the
no-diagonal Umlaufsatz escape branch.  It is intentionally retained as an
honest `sorry` while the surrounding reductions are formalized. -/
lemma simpleArc_complement_isPathConnected (L : List ℂ)
    (hsimple : PlaneArcSimple L) :
    IsPathConnected ((⋃ e ∈ chainEdges L, segment ℝ e.1 e.2)ᶜ) := by
  sorry

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
