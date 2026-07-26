import Mathlib
import RequestProject.SAWUmlaufSemicircle
import RequestProject.SAWUmlaufArcCrossings

/-!
# Path splicing for the finite Umlaufsatz detour

This file is an explicitly linked part of the live proof of
`joinedIn_compl_cons_segment_of_tail`: it is imported by
`SAWUmlaufArcDetour`, and hence by the full Umlaufsatz chain. The geometric
replacement paths are supplied by `SAWUmlaufSemicircle`; this file isolates the
parameter-space operation which removes one closed time interval from an old
path and inserts a replacement with the same endpoints. Iterating this
operation over a finite ordered family is the remaining bookkeeping step.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Replace the portion of `γ` between `s` and `t` by a path `δ` with matching
endpoints. No order hypothesis is needed to define the operation; applications
to detours use `s ≤ t`. -/
def splicePath {x y : ℂ} (γ : Path x y) (s t : unitInterval)
    (δ : Path (γ s) (γ t)) : Path x y :=
  ((γ.subpath 0 s).cast (by simpa using γ.source.symm) rfl).trans
    (δ.trans ((γ.subpath t 1).cast rfl (by simpa using γ.target)))

/-
A single splice preserves membership in any set which contains both the old
path and the replacement. This is the induction invariant needed when
successively inserting the finitely many local detours.
-/
lemma splicePath_mapsTo {x y : ℂ} (γ : Path x y)
    (s t : unitInterval) (δ : Path (γ s) (γ t)) (U : Set ℂ)
    (hγ : ∀ q, γ q ∈ U) (hδ : ∀ q, δ q ∈ U) :
    ∀ q, splicePath γ s t δ q ∈ U := by
  intro q
  unfold splicePath;
  simp +decide [ Path.trans_apply, Path.subpath ];
  grind

/-- A finite ordered family of parameter intervals which may be replaced
without overlap. The ordering condition is explicit so a finite-cover
refinement cannot silently splice intersecting intervals. -/
structure OrderedDetourIntervals where
  count : ℕ
  left : Fin count → unitInterval
  right : Fin count → unitInterval
  le_each : ∀ i, left i ≤ right i
  separated : ∀ i j, i < j → right i ≤ left j

/-- Data for a finite family of replacement paths along one candidate path.
This is the formal target type for refining the compact crossing cover into
ordered, pairwise nonoverlapping local detours. -/
structure PathDetourFamily {x y : ℂ} (γ : Path x y) : Type
    extends OrderedDetourIntervals where
  replacement : ∀ i, Path (γ (left i)) (γ (right i))

/-
The carrier of one splice is contained in the old carrier together with the
replacement carrier. This local statement will be iterated once the finite
crossing cover has been refined to `PathDetourFamily`.
-/
lemma splicePath_mem_old_or_replacement {x y : ℂ} (γ : Path x y)
    (s t : unitInterval) (δ : Path (γ s) (γ t)) :
    ∀ q, splicePath γ s t δ q ∈ pathCarrier γ ∪ pathCarrier δ := by
  convert HexArea.splicePath_mapsTo γ s t δ _ _ _ using 1;
  · exact fun q => Or.inl <| Set.mem_range_self q;
  · exact fun q => Or.inr <| Set.mem_range_self q

end HexArea