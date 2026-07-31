import Mathlib
import RequestProject.SAWUmlaufCrossingBounds

/-!
# Safe parameter intervals for the Umlaufsatz detour

This file is on the live finite-detour route to the Umlaufsatz.  It is imported
by `SAWUmlaufDetourConstruction`, whose output is consumed through
`SAWUmlaufArcDetour → SAWUmlaufArcInduction → SAWUmlaufArcEscape →
SAWUmlaufPolygon`.

The compactness argument in `SAWUmlaufCrossingBounds` puts every crossing time
strictly between two interior parameters.  Here that parameter statement is
converted into the exact path-avoidance certificates required by
`OrderedDetourSchedule`: the prefix before the left bound and the suffix after
the right bound avoid the newly adjoined segment.  Thus this file is linked
preparation for the remaining local replacement, not a dead branch.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- If the old path avoids `oldTail`, then every hit on the newly forbidden
set occurs in its genuinely new part, outside `oldTail`.  This is the precise
set-theoretic reduction needed for adjacent collinear overlap. -/
lemma pathHitTimes_eq_diff_of_avoids
    {x y : ℂ} (γ : Path x y) (newEdge oldTail : Set ℂ)
    (hγtail : ∀ q, γ q ∉ oldTail) :
    pathHitTimes γ newEdge = pathHitTimes γ (newEdge \ oldTail) := by
  ext q
  simp only [pathHitTimes, Set.mem_preimage, Set.mem_diff]
  constructor
  · intro hq
    exact ⟨hq, hγtail q⟩
  · exact fun hq => hq.1

/-- In particular, the old path has no parameter at which it simultaneously
meets the new edge and old tail. -/
lemma pathHitTimes_inter_eq_empty_of_avoids
    {x y : ℂ} (γ : Path x y) (newEdge oldTail : Set ℂ)
    (hγtail : ∀ q, γ q ∉ oldTail) :
    pathHitTimes γ (newEdge ∩ oldTail) = ∅ := by
  ext q
  simp [pathHitTimes, hγtail q]

/-- Crossing-time containment can therefore be proved using only the genuinely
new portion of an edge; no detour is required over an overlapping old-tail
portion. -/
lemma pathHitTimes_subset_diff_of_avoids
    {x y : ℂ} (γ : Path x y) (newEdge oldTail : Set ℂ)
    (hγtail : ∀ q, γ q ∉ oldTail) :
    pathHitTimes γ newEdge ⊆ γ ⁻¹' (newEdge \ oldTail) := by
  rw [pathHitTimes_eq_diff_of_avoids γ newEdge oldTail hγtail]
  exact Set.Subset.rfl

/-- The affine parameter used by `Path.subpath s t` lies between `s` and `t`
when the endpoints are ordered. -/
lemma subpathAux_mem_Icc (s t q : unitInterval) (hst : s ≤ t) :
    Path.subpathAux s t q ∈ Set.Icc s t := by
  simp [Path.subpathAux, Set.mem_Icc]
  refine ⟨Subtype.mk_le_mk.mpr ?_, Subtype.mk_le_mk.mpr ?_⟩
  · have hq0 : (0 : ℝ) ≤ q := q.2.1
    have hq1 : (q : ℝ) ≤ 1 := q.2.2
    have hst' : (s : ℝ) ≤ t := hst
    nlinarith
  · have hq0 : (0 : ℝ) ≤ q := q.2.1
    have hq1 : (q : ℝ) ≤ 1 := q.2.2
    have hst' : (s : ℝ) ≤ t := hst
    nlinarith

/-- If an ordered closed parameter interval contains no hit time, the
corresponding subpath avoids the set. -/
lemma subpath_avoids_of_Icc_disjoint_hitTimes
    {x y : ℂ} (γ : Path x y) (S : Set ℂ)
    (s t : unitInterval) (hst : s ≤ t)
    (hdisj : Disjoint (Set.Icc s t) (pathHitTimes γ S)) :
    ∀ q, γ.subpath s t q ∉ S := by
  intro q hq
  have hmem : Path.subpathAux s t q ∈ Set.Icc s t := by
    simp [Path.subpathAux]
    have hs : (s : ℝ) ≤ t := hst
    have hq0 : (0 : ℝ) ≤ q := q.2.1
    have hq1 : (q : ℝ) ≤ 1 := q.2.2
    constructor
    · exact_mod_cast (by nlinarith: (s : ℝ) ≤ (1 - q) * s + q * t)
    · exact_mod_cast (by nlinarith: (1 - q) * s + q * t ≤ (t : ℝ))
  have : Path.subpathAux s t q ∈ pathHitTimes γ S := by
    rw [pathHitTimes]
    exact hq
  exact Set.disjoint_left.mp hdisj hmem this

/-- Strict inner bounds for all hit times provide both safe retained pieces
needed by a one-block ordered detour schedule. -/
lemma prefix_suffix_avoid_of_hitTimes_inner_bounds
    {x y : ℂ} (γ : Path x y) (S : Set ℂ)
    (left right : unitInterval)
    (hleft : (0 : unitInterval) ≤ left) (hright : right ≤ (1 : unitInterval))
    (hinner : ∀ t ∈ pathHitTimes γ S, left < t ∧ t < right) :
    (∀ q, γ.subpath 0 left q ∉ S) ∧
      (∀ q, γ.subpath right 1 q ∉ S) := by
  apply And.intro
  · apply subpath_avoids_of_Icc_disjoint_hitTimes γ S 0 left hleft
    rw [Set.disjoint_left]
    intro t ht ht'
    have := hinner t ht'
    exact not_le.mpr this.1 ht.2
  · apply subpath_avoids_of_Icc_disjoint_hitTimes γ S right 1 hright
    rw [Set.disjoint_left]
    intro t ht ht'
    have := hinner t ht'
    exact not_le.mpr this.2 ht.1

/-- Once all crossings have been enclosed between `left` and `right`, a single
replacement joining the two boundary values and avoiding both forbidden sets
completes the ordered schedule. -/
lemma orderedDetourSchedule_of_inner_replacement
    {x y : ℂ} (γ : Path x y) (newEdge oldTail : Set ℂ)
    (left right : unitInterval)
    (hleft : (0 : unitInterval) ≤ left) (hlr : left ≤ right)
    (hright : right ≤ (1 : unitInterval))
    (hinner : ∀ t ∈ pathHitTimes γ newEdge, left < t ∧ t < right)
    (replacement : Path (γ left) (γ right))
    (hreplNew : ∀ q, replacement q ∉ newEdge)
    (hreplTail : ∀ q, replacement q ∉ oldTail) :
    Nonempty (OrderedDetourSchedule γ newEdge oldTail 0) := by
  obtain ⟨hprefix, hsuffix⟩ :=
    prefix_suffix_avoid_of_hitTimes_inner_bounds γ newEdge left right
      hleft hright hinner
  exact orderedDetourSchedule_single_block left right hleft hlr replacement
    hprefix hreplNew hreplTail hsuffix

end HexArea
