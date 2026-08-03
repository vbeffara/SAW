import Mathlib
import RequestProject.SAWUmlaufArcBasics
import RequestProject.SAWUmlaufArcCrossings
import RequestProject.SAWUmlaufSemicircle
import RequestProject.SAWUmlaufSpliceMany
import RequestProject.SAWUmlaufOrderedDetours
import RequestProject.SAWUmlaufCrossingBounds
import RequestProject.SAWUmlaufCrossingIntervals
import RequestProject.SAWUmlaufLocalDetour
import RequestProject.SAWUmlaufHalfPlaneDetour
import RequestProject.SAWUmlaufSideCrossings
import RequestProject.SAWUmlaufAttachmentData

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
separation and zero-crossing cases needed by the ordered construction.
`SAWUmlaufCrossingIntervals` converts those strict inner bounds into the exact
safe-prefix and safe-suffix certificates used by an ordered schedule, and
packages the final one-block assembly once a local replacement has been built.
Both files are therefore linked preparation for this theorem, not detached
branches.  `SAWUmlaufLocalDetour` packages the translated-semicircle primitive
into simultaneous avoidance of the new closed segment and of an old tail with
a clearance ball. `SAWUmlaufHalfPlaneDetour` proves the convex half-plane
attachment layer and packages a complete connected local replacement from two
same-side values in one clearance ball. `SAWUmlaufSideCrossings` develops the
continuous side-coordinate and parameter-neighborhood interface needed to
select attachment intervals and records both positive- and negative-side local
replacement outputs. `SAWUmlaufAttachmentData` records the exact finite
same-side blocks, their ordering, and their crossing-cover condition, so this
preparation is explicitly consumed rather than left detached. The remaining
construction must produce those finitely many blocks and fold their local
replacements into the existing ordered schedule.

There is one geometric complication which this statement intentionally keeps:
`PlaneArcSimple` permits overlap between adjacent collinear edges.  Components
lying in a portion of the first segment already covered by the tail need no new
detour; only genuinely new portions are replaced.  Thus no false
"first edge meets the tail only at its endpoint" premise is introduced.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- **Remaining local geometric replacement.**  All crossings may be enclosed
between two interior parameters; the unresolved planar construction is a path
between those boundary values which avoids both the new edge and the old tail.
The retained prefix and suffix are handled separately, and already proved, in
`SAWUmlaufCrossingIntervals`.

The intended proof refines `exists_finite_crossing_ball_cover` into ordered
local intervals and realizes the finitely many lifted semicircle detours.  It is
kept as an honest partial theorem so that the exact geometric output survives
future rounds and remains connected to the main Umlaufsatz. -/
lemma exists_inner_avoiding_replacement
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    ∃ left right : unitInterval,
      (0 : unitInterval) < left ∧ left ≤ right ∧ right < (1 : unitInterval) ∧
      (∀ t ∈ pathHitTimes γ (segment ℝ a b), left < t ∧ t < right) ∧
      ∃ replacement : Path (γ left) (γ right),
        (∀ q, replacement q ∉ segment ℝ a b) ∧
        (∀ q, replacement q ∉ chainCarrier (b :: L)) := by
  sorry

/-- **Finite geometric construction, ordered form.**  A path in the complement
of the old tail, whose endpoints avoid the enlarged carrier, admits an ordered
schedule.  The bookkeeping and retained-piece obligations are now discharged:
this theorem is a proved assembly from `exists_inner_avoiding_replacement`. -/
lemma exists_avoiding_orderedDetourSchedule
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    Nonempty (OrderedDetourSchedule γ (segment ℝ a b)
      (chainCarrier (b :: L)) 0) := by
  obtain ⟨left, right, hleft, hlr, hright, hinner,
      replacement, hreplNew, hreplTail⟩ :=
    exists_inner_avoiding_replacement a b L hsimple γ hγtail hx hy
  exact orderedDetourSchedule_of_inner_replacement γ
    (segment ℝ a b) (chainCarrier (b :: L)) left right
    hleft.le hlr hright.le hinner replacement hreplNew hreplTail

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
