import Mathlib
import RequestProject.SAWUmlaufArcBasics
import RequestProject.SAWUmlaufArcCrossings
import RequestProject.SAWUmlaufSemicircle
import RequestProject.SAWUmlaufSpliceMany
import RequestProject.SAWUmlaufOrderedDetours
import RequestProject.SAWUmlaufCrossingBounds

/-!
# Geometric construction of the finite Umlaufsatz detour plan

This file isolates the remaining constructive leaf on the live route to the
Umlaufsatz.  It is imported by `SAWUmlaufArcDetour`, which uses the theorem
below to prove `joinedIn_compl_cons_segment_of_tail`; the chain then continues
through `SAWUmlaufArcInduction → SAWUmlaufArcEscape → SAWUmlaufPolygon`.
Consequently this partial file is explicitly connected to the main theorem and
is not a dead branch.

Given a path avoiding the old polygonal tail, the crossing package supplies a
compact set of times at which it meets the newly adjoined segment and uniform
clearance from the tail.  One refines a finite crossing cover into ordered
components, retains the old path between those components, and inserts local
semicircular detours.  The geometric output is now an
`OrderedDetourSchedule`: retained pieces need only be checked against the new
edge, while replacements are checked against both the new edge and old tail.
`OrderedDetourSchedule.erase_mapsTo_compl_union` turns this into the lower-level
`DetourPlan.MapsTo` invariant, and `DetourPlan.realizeFromSource` performs all
dependent endpoint concatenations without changing the original labels.

`SAWUmlaufCrossingBounds` is directly imported here and supplies the endpoint
separation and zero-crossing cases needed by the ordered construction.  It is
therefore linked preparation for this theorem, not a detached branch.

There is one geometric complication which this statement intentionally keeps:
`PlaneArcSimple` permits overlap between adjacent collinear edges.  Components
lying in a portion of the first segment already covered by the tail need no new
detour; only genuinely new portions are replaced.  Thus no false
"first edge meets the tail only at its endpoint" premise is introduced.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- **Remaining finite geometric construction, ordered form.**  A path in the
complement of the old tail, whose endpoints avoid the enlarged carrier, admits
an ordered schedule.  The schedule records only the genuinely geometric local
obligations: retained path pieces avoid the new segment, while inserted pieces
avoid both the new segment and the old tail.

The intended construction uses `path_uniform_clearance_from_tail` and
`exists_finite_crossing_ball_cover`, chooses finitely many ordered crossing
intervals, and uses `semicirclePath_local_detour` (or its lifted variant on a
closed local piece) for the replacements.  The theorem is kept as an honest
`sorry` because selecting and ordering those intervals is the remaining planar
geometry.  All conversion and dependent concatenation after this output are
proved. -/
lemma exists_avoiding_orderedDetourSchedule
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    Nonempty (OrderedDetourSchedule γ (segment ℝ a b)
      (chainCarrier (b :: L)) 0) := by
  sorry

/-- Compatibility output consumed by the existing arc-detour theorem.  This is
now a proved conversion from the sharper ordered geometric interface above. -/
lemma exists_avoiding_detourPlan
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    ∃ P : DetourPlan γ 0,
      DetourPlan.MapsTo (chainCarrier (a :: b :: L))ᶜ P := by
  obtain ⟨S⟩ :=
    exists_avoiding_orderedDetourSchedule a b L hsimple γ hγtail hx hy
  refine ⟨S.erase, ?_⟩
  rw [chainCarrier_cons_cons]
  exact OrderedDetourSchedule.erase_mapsTo_compl_union hγtail S

end HexArea
