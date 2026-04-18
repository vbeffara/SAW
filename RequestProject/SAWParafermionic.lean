/-
# Walk reconstruction and cutting map infrastructure
-/

import Mathlib
import RequestProject.SAWCutting
import RequestProject.SAWCuttingHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk reconstruction from parts -/

lemma walk_take_drop_spec {v w : HexVertex}
    (p : hexGraph.Walk v w) (u : HexVertex) (hu : u ∈ p.support) :
    p = (p.takeUntil u hu).append (p.dropUntil u hu) :=
  (SimpleGraph.Walk.take_spec p hu).symm

lemma path_determined_by_parts {v w : HexVertex}
    (p₁ p₂ : hexGraph.Path v w)
    (u : HexVertex) (hu₁ : u ∈ p₁.1.support) (hu₂ : u ∈ p₂.1.support)
    (h_take : p₁.1.takeUntil u hu₁ = p₂.1.takeUntil u hu₂)
    (h_drop : p₁.1.dropUntil u hu₁ = p₂.1.dropUntil u hu₂) :
    p₁ = p₂ := by
  have h_eq : p₁.val = (p₁.val.takeUntil u hu₁).append (p₁.val.dropUntil u hu₁) ∧
    p₂.val = (p₂.val.takeUntil u hu₂).append (p₂.val.dropUntil u hu₂) := by
    exact ⟨walk_take_drop_spec _ _ _, walk_take_drop_spec _ _ _⟩
  grind +extAll

lemma walk_reverse_injective {v w : HexVertex}
    (p₁ p₂ : hexGraph.Walk v w) (h : p₁.reverse = p₂.reverse) :
    p₁ = p₂ := by
  have := h ▸ SimpleGraph.Walk.reverse_reverse p₂; aesop

lemma shiftWalk_injective_walks (dx dy : ℤ) {v w : HexVertex}
    (p₁ p₂ : hexGraph.Walk v w) (h : shiftWalk dx dy p₁ = shiftWalk dx dy p₂) :
    p₁ = p₂ := by
  have h_structure : p₁.support = p₂.support := by
    have h_support : List.map (hexShift dx dy) p₁.support =
        List.map (hexShift dx dy) p₂.support := by
      rw [← shiftWalk_support, ← shiftWalk_support, h]
    exact List.map_injective_iff.mpr (hexShift_injective dx dy) h_support
  grind +suggestions

/-! ## Cutting map infrastructure -/

noncomputable def extraWalkCutData {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    {v : HexVertex // v ∈ s.walk.1.support ∧
      v.1 + v.2.1 = -(T + 1 : ℤ) ∧ v.2.2 = false} :=
  let h := A_inf_diff_reaches_boundary hT s h_not
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

noncomputable def extraWalkB1 {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    PaperBridge (T + 1) :=
  let d := extraWalkCutData hT s h_not
  ⟨d.1,
   ⟨s.walk.1.takeUntil d.1 d.2.1, s.walk.2.takeUntil d.2.1⟩,
   ⟨by have := d.2.2.1; omega, d.2.2.2⟩,
   fun u hu => s.in_strip u (s.walk.1.support_takeUntil_subset d.2.1 hu)⟩

noncomputable def extraWalkB2 {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    PaperBridge (T + 1) :=
  let d := extraWalkCutData hT s h_not
  (suffix_reversed_shifted_gives_bridge s.end_v d.1
    s.end_left.1 s.end_left.2.1 d.2.2.1 d.2.2.2
    (s.walk.1.dropUntil d.1 d.2.1) (s.walk.2.dropUntil d.2.1)
    (fun u hu => s.in_strip u (s.walk.1.support_dropUntil_subset d.2.1 hu))).choose

lemma extraWalk_length_rel {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    s.walk.1.length = (extraWalkB1 hT s h_not).walk.1.length +
                       (extraWalkB2 hT s h_not).walk.1.length := by
  convert walk_split_lengths s.walk.1 (extraWalkCutData hT s h_not |>.2.1) using 1
  · rw [walk_split_lengths]
  · convert walk_split_lengths s.walk.1 (extraWalkCutData hT s h_not |>.2.1) using 1
    grind +locals

/-! ## The sum bound -/

/-- The sum over extra walks is bounded by xc · B². -/
theorem extra_walk_sum_le_proved {T : ℕ} (hT : 1 ≤ T)
    (F : Finset (PaperSAW_A_inf (T + 1)))
    (hF : ∀ s ∈ F, ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    ∑ s ∈ F, xc ^ (s.walk.1.length + 1) ≤
    xc * paper_bridge_partition (T + 1) xc ^ 2 := by
  sorry

end
