import Mathlib
import RequestProject.SAWUmlaufArcCrossings
import RequestProject.SAWUmlaufOrderedDetours

/-!
# Parameter bounds for the Umlaufsatz crossing detour

This file is part of the live construction of
`exists_avoiding_orderedDetourSchedule`.  It is imported by
`SAWUmlaufDetourConstruction`, hence by `SAWUmlaufArcDetour →
SAWUmlaufArcInduction → SAWUmlaufArcEscape → SAWUmlaufPolygon` and the main
Umlaufsatz.

The endpoints of the original path avoid the new closed segment.  Continuity
therefore gives an initial and a terminal parameter interval free of crossings.
Equivalently, all crossing times lie in one compact subinterval strictly inside
`[0,1]`.  This is the first ordering fact needed before the compact crossing
cover can be refined into a finite detour schedule.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- If both endpoints avoid a set, neither endpoint parameter belongs to its
hit-time set. -/
lemma pathHitTimes_endpoints_not_mem
    {x y : ℂ} (γ : Path x y) (S : Set ℂ)
    (hx : x ∉ S) (hy : y ∉ S) :
    (0 : unitInterval) ∉ pathHitTimes γ S ∧
      (1 : unitInterval) ∉ pathHitTimes γ S := by
  simp [pathHitTimes]
  exact ⟨hx, hy⟩

/-- The crossing times of a closed segment are uniformly separated from both
endpoint parameters when the path endpoints avoid that segment.  The bounds
are deliberately stated in the order needed by an ordered detour schedule. -/
lemma exists_pathHitTimes_segment_inner_bounds
    {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (hx : x ∉ segment ℝ a b) (hy : y ∉ segment ℝ a b) :
    ∃ left right : unitInterval,
      (0 : unitInterval) < left ∧ left ≤ right ∧ right < (1 : unitInterval) ∧
      ∀ t ∈ pathHitTimes γ (segment ℝ a b), left < t ∧ t < right := by
  -- The crossing time set is compact
  have hcompact := isCompact_pathHitTimes_segment γ a b
  -- Endpoints are not in the crossing set
  have h0 : (0 : unitInterval) ∉ pathHitTimes γ (segment ℝ a b) := by
    simp [pathHitTimes]
    convert hx using 1
  have h1 : (1 : unitInterval) ∉ pathHitTimes γ (segment ℝ a b) := by
    simp [pathHitTimes]
    convert hy using 1
  -- Either empty or nonempty
  by_cases hempty : pathHitTimes γ (segment ℝ a b) = ∅
  · -- Empty case: pick middle point
    let m : unitInterval := ⟨1/2, by norm_num⟩
    refine ⟨m, m, ?_, le_rfl, ?_, ?_⟩
    · show (0 : unitInterval) < m; exact Subtype.mk_lt_mk.mpr (by norm_num : (0 : ℝ) < 1/2)
    · show m < (1 : unitInterval); exact Subtype.mk_lt_mk.mpr (by norm_num : (1 : ℝ)/2 < 1)
    · simp [hempty]
  · -- Nonempty case: use min and max of the compact set
    have hne : (pathHitTimes γ (segment ℝ a b)).Nonempty := by rwa [Set.nonempty_iff_ne_empty]
    -- Get the inf and sup
    let K := pathHitTimes γ (segment ℝ a b)
    let infVal := sInf K
    let supVal := sSup K
    have hinf_mem : infVal ∈ K := hcompact.sInf_mem hne
    have hsup_mem : supVal ∈ K := hcompact.sSup_mem hne
    -- infVal > 0 because 0 ∉ K
    have hinf_pos : (0 : ℝ) < infVal := by
      have h : (0 : unitInterval) < infVal := by
        by_contra h'
        push_neg at h'
        have : (0 : unitInterval) = infVal := le_antisymm infVal.property.1 h'
        exact h0 (this ▸ hinf_mem)
      exact_mod_cast h
    -- supVal < 1 because 1 ∉ K
    have hsup_lt_one : (supVal : ℝ) < 1 := by
      have h : (supVal : unitInterval) < 1 := by
        by_contra h'
        push_neg at h'
        have : (1 : unitInterval) = supVal := le_antisymm h' supVal.property.2
        exact h1 (this ▸ hsup_mem)
      exact_mod_cast h
    -- Pick midpoints between 0 and inf, and sup and 1
    let left : unitInterval := ⟨(infVal : ℝ) / 2, by
      have hinf_nonneg : (0 : ℝ) ≤ infVal := infVal.property.1
      have hinf_le_one : (infVal : ℝ) ≤ 1 := infVal.property.2
      constructor <;> linarith⟩
    let right : unitInterval := ⟨(supVal + 1) / 2, by
      have hsup_nonneg : (0 : ℝ) ≤ supVal := supVal.property.1
      have hsup_le_one : (supVal : ℝ) ≤ 1 := supVal.property.2
      constructor <;> linarith⟩
    have hleft_lt_inf : (left : ℝ) < infVal := by
      simp only [left]
      linarith [hinf_pos]
    have hsup_lt_right : (supVal : ℝ) < right := by
      simp only [right]
      linarith [hsup_lt_one]
    refine ⟨left, right, ?_, ?_, ?_, ?_⟩
    · -- 0 < left
      exact Subtype.mk_lt_mk.mpr (by linarith [hinf_pos] : (0 : ℝ) < infVal / 2)
    · -- left ≤ right
      show left ≤ right
      simp only [left, right, Subtype.mk_le_mk]
      have hne' : (pathHitTimes γ (segment ℝ a b)).Nonempty := ‹_›
      have hinf_le_sup : (infVal : ℝ) ≤ supVal := by
        have : infVal ≤ supVal := by
          apply csInf_le_csSup hcompact.bddBelow hcompact.bddAbove hne'
        exact_mod_cast this
      linarith [hinf_le_sup]
    · -- right < 1
      exact Subtype.mk_lt_mk.mpr (by linarith [hsup_lt_one] : ((supVal + 1) / 2 : ℝ) < 1)
    · -- ∀ t ∈ pathHitTimes γ ..., left < t ∧ t < right
      intro t ht
      constructor
      · -- left < t
        have ht_ge_inf : infVal ≤ t := csInf_le hcompact.bddBelow ht
        exact lt_of_lt_of_le hleft_lt_inf (le_trans (by linarith [hinf_pos] : (infVal : ℝ) ≤ infVal) (by exact_mod_cast ht_ge_inf))
      · -- t < right
        have ht_le_sup : t ≤ supVal := le_csSup hcompact.bddAbove ht
        exact lt_of_le_of_lt ht_le_sup (by exact_mod_cast hsup_lt_right)

/-- If there are no crossing times, the original path itself supplies the
terminal empty schedule.  This closes the zero-crossing branch of the live
finite-cover construction. -/
lemma orderedDetourSchedule_of_no_segment_hits
    {x y : ℂ} (γ : Path x y) (a b : ℂ) (oldTail : Set ℂ)
    (hno : pathHitTimes γ (segment ℝ a b) = ∅) :
    Nonempty (OrderedDetourSchedule γ (segment ℝ a b) oldTail 0) := by
  apply OrderedDetourSchedule.done_zero_of_path_avoids
  intro q hq
  have : q ∈ pathHitTimes γ (segment ℝ a b) := hq
  exact hno.subset this

/-- One replacement interval, together with a safe suffix, is already a full
ordered schedule.  This constructor is the terminal assembly step after all
crossings have been enclosed in a single replaceable parameter block. -/
lemma orderedDetourSchedule_single_block
    {x y : ℂ} {γ : Path x y} {newEdge oldTail : Set ℂ}
    (left right : unitInterval) (hleft : (0 : unitInterval) ≤ left)
    (hlr : left ≤ right) (replacement : Path (γ left) (γ right))
    (hprefix : ∀ q, γ.subpath 0 left q ∉ newEdge)
    (hreplNew : ∀ q, replacement q ∉ newEdge)
    (hreplTail : ∀ q, replacement q ∉ oldTail)
    (hsuffix : ∀ q, γ.subpath right 1 q ∉ newEdge) :
    Nonempty (OrderedDetourSchedule γ newEdge oldTail 0) := by
  exact ⟨.step 0 left right hleft hlr replacement hprefix hreplNew hreplTail
    (.done right hsuffix)⟩

end HexArea
