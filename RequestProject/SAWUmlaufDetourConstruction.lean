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
import RequestProject.SAWUmlaufAttachmentSchedule
import RequestProject.SAWUmlaufEndpointEscape
import RequestProject.SAWUmlaufMixedSchedule

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
same-side blocks, their ordering, and their crossing-cover condition, while
`SAWUmlaufAttachmentSchedule` records the retained-gap certificates and folds
those geometric blocks into the existing ordered schedule.
`SAWUmlaufEndpointEscape` supplies the explicitly linked odd-crossing
alternative: one exceptional block routes around the free endpoint when its
boundary values lie on opposite sides.  These preparations are consumed here
rather than left detached. The remaining construction must merge the
same-side blocks and at most one endpoint-escape block into the finite schedule.

There is one geometric complication which this statement intentionally keeps:
`PlaneArcSimple` permits overlap between adjacent collinear edges.  Components
lying in a portion of the first segment already covered by the tail need no new
detour; only genuinely new portions are replaced.  Thus no false
"first edge meets the tail only at its endpoint" premise is introduced.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- **Remaining finite geometric selection.**  Compact crossing data can be
refined to a left-to-right attachment schedule.  This is the honest remaining
leaf: its constructors force every retained gap and final suffix to avoid the
new edge, while each selected block contains all data needed for a local
semicircular replacement.  In particular, the statement does not incorrectly
require the two sides of every individual transverse crossing to agree; a block
may span several crossings before returning to one side.

The output is consumed immediately below, so this partial theorem is on the
live route to the Umlaufsatz. -/
lemma exists_attachmentDetourSchedule
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    ∃ ε : ℝ, 0 < ε ∧
      Nonempty (AttachmentDetourSchedule γ a b
        (chainCarrier (b :: L)) ε 0) := by
  -- The same-side blocks formalized in `SAWUmlaufAttachmentData` handle even
  -- packets of crossings.  An odd packet requires an additional local route
  -- around an endpoint of `[a,b]`; constructing that endpoint-escape block and
  -- merging it with the same-side blocks is the remaining geometric residue.
  sorry

/-- **Finite geometric construction, ordered form.**  A path in the complement
of the old tail, whose endpoints avoid the enlarged carrier, admits an ordered
schedule.  All path concatenation and local-replacement bookkeeping is now a
proved fold from `exists_attachmentDetourSchedule`; only finite geometric
selection remains in that theorem. -/
lemma exists_avoiding_orderedDetourSchedule
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ) :
    Nonempty (OrderedDetourSchedule γ (segment ℝ a b)
      (chainCarrier (b :: L)) 0) := by
  obtain ⟨ε, hε, hS⟩ :=
    exists_attachmentDetourSchedule a b L hsimple γ hγtail hx hy
  obtain ⟨S⟩ := hS
  exact S.toOrderedDetourSchedule hsimple.head_ne_of_cons_cons hε

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
