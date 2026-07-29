import Mathlib
import RequestProject.SAWUmlaufArcBasics
import RequestProject.SAWUmlaufSpliceMany

/-!
# Ordered detour schedules for the Umlaufsatz

This file is an explicitly linked part of the live polygonal-arc route to the
Umlaufsatz.  It is imported by `SAWUmlaufDetourConstruction`, whose output is
used by `SAWUmlaufArcDetour → SAWUmlaufArcInduction → SAWUmlaufArcEscape →
SAWUmlaufPolygon`.

The old path already avoids the tail carrier.  Consequently the geometric
construction should not repeatedly prove that retained subpaths avoid the
tail: it only has to prove that they avoid the newly adjoined segment.  An
inserted replacement, on the other hand, must avoid both sets.  The inductive
`OrderedDetourSchedule` records exactly these local obligations, together with
the parameter order which was deliberately absent from the lower-level
`DetourPlan` endpoint-bookkeeping type.

Erasing a schedule gives a `DetourPlan`.  The main theorem of this file proves
that, provided the original path avoids the old tail, the erased plan maps to
the complement of the union of the new segment and old tail.  Thus the sole
remaining geometric task can be stated as construction of an ordered schedule,
without any dependent path-concatenation bookkeeping.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- An ordered finite sequence of crossing replacements along `γ`.

`newEdge` is the newly forbidden set and `oldTail` is the set already avoided
by the original path.  A retained piece only carries a `newEdge` avoidance
proof; avoidance of `oldTail` is inherited from `γ`.  Inserted paths carry both
proofs. -/
inductive OrderedDetourSchedule {x y : ℂ} (γ : Path x y)
    (newEdge oldTail : Set ℂ) : unitInterval → Type
  | done (start : unitInterval)
      (suffixNew : ∀ q, γ.subpath start 1 q ∉ newEdge) :
      OrderedDetourSchedule γ newEdge oldTail start
  | step (start left right : unitInterval)
      (hstart : start ≤ left) (hinterval : left ≤ right)
      (replacement : Path (γ left) (γ right))
      (keptNew : ∀ q, γ.subpath start left q ∉ newEdge)
      (insertedNew : ∀ q, replacement q ∉ newEdge)
      (insertedTail : ∀ q, replacement q ∉ oldTail)
      (rest : OrderedDetourSchedule γ newEdge oldTail right) :
      OrderedDetourSchedule γ newEdge oldTail start

namespace OrderedDetourSchedule

/-- Forget the order and separated-avoidance certificates, retaining the
endpoint-correct finite splice plan. -/
def erase {x y : ℂ} {γ : Path x y} {newEdge oldTail : Set ℂ}
    {start : unitInterval} :
    OrderedDetourSchedule γ newEdge oldTail start → DetourPlan γ start
  | .done start _ => .done start
  | .step start left right _ _ replacement _ _ _ rest =>
      .step start left right replacement rest.erase

/-- Every retained old subpath inherits avoidance of the old tail from the
original path. -/
lemma subpath_avoids_of_path_avoids {x y : ℂ} (γ : Path x y)
    (oldTail : Set ℂ) (hγTail : ∀ q, γ q ∉ oldTail)
    (s t q : unitInterval) : γ.subpath s t q ∉ oldTail := by
  simp only [Path.subpath]
  exact hγTail _

/-- If the remaining suffix of the original path already avoids the new edge,
there is an empty schedule.  This is the terminal case of the future crossing
interval recursion. -/
lemma done_of_suffix_avoids {x y : ℂ} {γ : Path x y}
    {newEdge oldTail : Set ℂ} (start : unitInterval)
    (hnew : ∀ q, γ.subpath start 1 q ∉ newEdge) :
    Nonempty (OrderedDetourSchedule γ newEdge oldTail start) := by
  exact ⟨.done start hnew⟩

/-- In particular, a path which globally avoids the new edge has an empty
schedule beginning at its source. -/
lemma done_zero_of_path_avoids {x y : ℂ} {γ : Path x y}
    {newEdge oldTail : Set ℂ} (hnew : ∀ q, γ q ∉ newEdge) :
    Nonempty (OrderedDetourSchedule γ newEdge oldTail 0) := by
  apply done_of_suffix_avoids 0
  intro q
  simpa only [Path.subpath_zero_one] using hnew q

/-- The fully-overlapped branch needs no geometric detour: if the newly named
edge is already contained in the old tail, old-tail avoidance supplies the
empty schedule.  This explicitly handles the adjacent-collinear overlap allowed
by `PlaneArcSimple` rather than imposing a false endpoint-only intersection
condition. -/
lemma done_zero_of_newEdge_subset_oldTail {x y : ℂ} {γ : Path x y}
    {newEdge oldTail : Set ℂ} (hsub : newEdge ⊆ oldTail)
    (hγTail : ∀ q, γ q ∉ oldTail) :
    Nonempty (OrderedDetourSchedule γ newEdge oldTail 0) := by
  apply done_zero_of_path_avoids
  intro q hq
  exact hγTail q (hsub hq)

/-- Erasing an ordered schedule yields precisely the `MapsTo` invariant needed
by finite path realization. -/
lemma erase_mapsTo_compl_union {x y : ℂ} {γ : Path x y}
    {newEdge oldTail : Set ℂ} (hγTail : ∀ q, γ q ∉ oldTail)
    {start : unitInterval}
    (S : OrderedDetourSchedule γ newEdge oldTail start) :
    DetourPlan.MapsTo (newEdge ∪ oldTail)ᶜ S.erase := by
  induction S with
  | done start suffixNew =>
      apply DetourPlan.MapsTo.done
      intro q hq
      exact hq.elim (suffixNew q) (subpath_avoids_of_path_avoids γ oldTail hγTail start 1 q)
  | step start left right hstart hinterval replacement keptNew insertedNew insertedTail rest ih =>
      apply DetourPlan.MapsTo.step
      · intro q hq
        exact hq.elim (keptNew q)
          (subpath_avoids_of_path_avoids γ oldTail hγTail start left q)
      · intro q hq
        exact hq.elim (insertedNew q) (insertedTail q)
      · exact ih

/-- Source-level assembly: an ordered schedule beginning at zero gives a path
with the same endpoints as `γ` which avoids both forbidden sets. -/
lemma joinedIn_compl_union {x y : ℂ} {γ : Path x y}
    {newEdge oldTail : Set ℂ} (hγTail : ∀ q, γ q ∉ oldTail)
    (S : OrderedDetourSchedule γ newEdge oldTail 0) :
    JoinedIn (newEdge ∪ oldTail)ᶜ x y := by
  exact DetourPlan.joinedIn_of_detourPlan S.erase
    (erase_mapsTo_compl_union hγTail S)

end OrderedDetourSchedule

end HexArea
