import Mathlib
import RequestProject.SAWUmlaufSplice

/-!
# Finite path splicing for the Umlaufsatz detour

This file is preparation on the live proof path for
`joinedIn_compl_cons_segment_of_tail`.  It is imported by
`SAWUmlaufArcDetour`, hence transitively by `SAWUmlaufPolygon` and the main
Umlaufsatz.  It is not a detached branch.

A finite crossing construction must retain the pieces of the original path
between successive crossing intervals and insert one local replacement on each
interval.  Repeatedly applying `splicePath` obscures the original parameter
values because each concatenation reparametrizes the path.  `DetourPlan` avoids
that problem: it records a dependent list of replacements, with the end
parameter of one retained piece becoming the start parameter of the next.
`DetourPlan.realize` then concatenates all retained pieces and replacements in
one pass.

The ordering and geometric coverage obligations are deliberately kept outside
this datatype.  They belong to the remaining construction which refines the
finite crossing cover.  The datatype and its realization settle the finite,
dependent endpoint bookkeeping needed once those intervals have been chosen.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- A finite sequence of detours along an original path `γ`, beginning at
parameter `start`.  A step keeps the old subpath from `start` to `left`, inserts
`replacement` from `γ left` to `γ right`, and continues at `right`.

The eventual geometric constructor will additionally prove
`start ≤ left ≤ right` and ordering of successive steps.  These inequalities
are not needed for the endpoint-correct concatenation itself. -/
inductive DetourPlan {x y : ℂ} (γ : Path x y) : unitInterval → Type
  | done (start : unitInterval) : DetourPlan γ start
  | step (start left right : unitInterval)
      (replacement : Path (γ left) (γ right))
      (rest : DetourPlan γ right) : DetourPlan γ start

namespace DetourPlan

/-- Realize a plan beginning at `start` as a path from `γ start` to the target
of the original path. -/
def realize {x y : ℂ} {γ : Path x y} {start : unitInterval} :
    DetourPlan γ start → Path (γ start) y
  | .done _ => (γ.subpath start 1).cast rfl (by simpa using γ.target)
  | .step _ left _ replacement rest =>
      (γ.subpath start left).trans (replacement.trans rest.realize)

/-- Package a plan beginning at parameter `0` as a path with exactly the same
endpoints as the original path. -/
def realizeFromSource {x y : ℂ} {γ : Path x y} (P : DetourPlan γ 0) : Path x y :=
  P.realize.cast (by simpa using γ.source) rfl

/-- Every retained old subpath and every inserted replacement in the plan maps
into `U`.  This is the precise finite-splicing invariant used by the detour
construction: unlike `splicePath_mapsTo`, it does not require the discarded
crossing intervals of the original path to lie in `U`. -/
inductive MapsTo {x y : ℂ} {γ : Path x y} (U : Set ℂ) :
    {start : unitInterval} → DetourPlan γ start → Prop
  | done (start : unitInterval)
      (suffix : ∀ q, γ.subpath start 1 q ∈ U) : MapsTo U (.done start)
  | step (start left right : unitInterval)
      (replacement : Path (γ left) (γ right))
      (rest : DetourPlan γ right)
      (kept : ∀ q, γ.subpath start left q ∈ U)
      (inserted : ∀ q, replacement q ∈ U)
      (tail : MapsTo U rest) : MapsTo U (.step start left right replacement rest)

/-- Realizing a valid finite detour plan produces a path entirely in the desired
ambient set.  This closes the finite dependent concatenation bookkeeping; the
remaining Umlaufsatz gap is the geometric construction of a `DetourPlan` whose
retained pieces avoid the new segment and whose replacements are the local
semicircular detours. -/
lemma realize_mapsTo {x y : ℂ} {γ : Path x y} {U : Set ℂ}
    {start : unitInterval} {P : DetourPlan γ start} (hP : MapsTo U P) :
    ∀ q, P.realize q ∈ U := by
  intro q
  induction hP generalizing q with
  | done start suffix =>
      simp [DetourPlan.realize]
      exact suffix q
  | step start left right replacement rest kept inserted tail ih =>
      simp [DetourPlan.realize, Path.trans_apply]
      split_ifs with h h2
      · exact kept _
      · exact inserted _
      · exact ih _

/-- Source-level form consumed by `JoinedIn`: a valid plan starting at zero is
a replacement path from the original source to target which stays in `U`. -/
lemma realizeFromSource_mapsTo {x y : ℂ} {γ : Path x y} {U : Set ℂ}
    {P : DetourPlan γ 0} (hP : MapsTo U P) :
    ∀ q, P.realizeFromSource q ∈ U := by
  intro q
  exact realize_mapsTo hP q

/-- A source-level detour plan immediately gives the corresponding joinedness
statement.  This is the final abstract assembly used after constructing the
ordered finite crossing plan. -/
lemma joinedIn_of_detourPlan {x y : ℂ} {γ : Path x y} {U : Set ℂ}
    (P : DetourPlan γ 0) (hP : MapsTo U P) : JoinedIn U x y := by
  have realize_mapsTo_gen : ∀ (start : unitInterval) (P : DetourPlan γ start) (q : unitInterval),
      ∀ (hP : MapsTo U P), P.realize q ∈ U := by
    clear hP P
    intro start P q hP
    induction hP generalizing q with
    | done start suffix =>
      simp [DetourPlan.realize]
      exact suffix q
    | step start left right replacement rest kept inserted tail ih =>
      simp [DetourPlan.realize, Path.trans_apply]
      split_ifs with h h2
      · exact kept _
      · exact inserted _
      · exact ih _
  have realizeFromSource_mapsTo : ∀ q, P.realizeFromSource q ∈ U := by
    intro q
    simp only [DetourPlan.realizeFromSource]
    exact realize_mapsTo_gen 0 P q hP
  exact ⟨P.realizeFromSource, realizeFromSource_mapsTo⟩

end DetourPlan

end HexArea
