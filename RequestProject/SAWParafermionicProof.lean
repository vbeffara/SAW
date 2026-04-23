/-
# Relationship between finite and infinite strip identities

This file shows that `strip_identity_genuine` (finite strip) follows
from `infinite_strip_identity` (infinite strip), given summability
of the bridge partition function.

This demonstrates that the three root sorry's reduce to TWO
independent sorry's:
1. `infinite_strip_identity` (implies strip_identity_genuine)
2. `paper_bridge_decomp_injection` (Hammersley-Welsh)
-/

import Mathlib
import RequestProject.SAWPaperChain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## PaperSAW_B embeds into PaperBridge -/

/-- Each PaperSAW_B T L determines a PaperBridge T. -/
def PaperSAW_B_to_PaperBridge' {T L : ℕ} (s : PaperSAW_B T L) : PaperBridge T where
  end_v := s.saw.w
  walk := s.saw.p
  end_right := s.end_right
  in_strip := fun v hv => (s.in_strip v hv).1

/-
The embedding is injective.
-/
lemma PaperSAW_B_to_PaperBridge_injective' (T L : ℕ) :
    Function.Injective (@PaperSAW_B_to_PaperBridge' T L) := by
  intro s1 s2 h_eq;
  cases s1 ; cases s2 ; simp_all +decide [ PaperSAW_B_to_PaperBridge' ];
  cases ‹SAW paperStart _› ; cases ‹SAW paperStart _› ; aesop

/-! ## B_paper ≤ xc · paper_bridge_partition -/

/-- B_paper(T,L,xc) ≤ xc · paper_bridge_partition(T,xc). -/
lemma B_paper_le_xc_bridge' (T L : ℕ) (hT : 1 ≤ T) :
    B_paper T L xc ≤ xc * paper_bridge_partition T xc := by
  unfold B_paper paper_bridge_partition
  have key : ∀ s : PaperSAW_B T L,
      xc ^ (s.len + 1) = xc * xc ^ (PaperSAW_B_to_PaperBridge' s).walk.1.length := by
    intro s; rw [show (PaperSAW_B_to_PaperBridge' s).walk.1.length = s.len from s.saw.l]
    rw [pow_succ]; ring
  calc ∑' s : PaperSAW_B T L, xc ^ (s.len + 1)
      = ∑' s : PaperSAW_B T L, xc * xc ^ (PaperSAW_B_to_PaperBridge' s).walk.1.length :=
        tsum_congr key
    _ = xc * ∑' s : PaperSAW_B T L, xc ^ (PaperSAW_B_to_PaperBridge' s).walk.1.length := by
        rw [tsum_mul_left]
    _ ≤ xc * ∑' b : PaperBridge T, xc ^ b.walk.1.length := by
        apply mul_le_mul_of_nonneg_left _ xc_pos.le
        have : (fun s : PaperSAW_B T L =>
            xc ^ (PaperSAW_B_to_PaperBridge' s).walk.1.length) =
            (fun b : PaperBridge T => xc ^ b.walk.1.length) ∘
            PaperSAW_B_to_PaperBridge' := by ext; rfl
        rw [this]
        exact tsum_comp_le_tsum_of_inj
          (paper_bridge_summable T hT)
          (fun b => pow_nonneg xc_pos.le _)
          (PaperSAW_B_to_PaperBridge_injective' T L)

/-! ## xc · paper_bridge_partition ≤ 1 from infinite strip identity -/

/-- From the infinite strip identity: xc · paper_bridge_partition ≤ 1. -/
lemma xc_bridge_le_one' (T : ℕ) (hT : 1 ≤ T) :
    xc * paper_bridge_partition T xc ≤ 1 := by
  have hid := infinite_strip_identity T hT
  linarith [mul_nonneg c_alpha_pos.le (A_inf_nonneg T xc xc_pos.le)]

/-! ## B_paper ≤ 1 from infinite strip identity -/

/-- B_paper ≤ 1 from the infinite strip identity. -/
theorem B_paper_le_one_from_infinite' (T L : ℕ) (hT : 1 ≤ T) (_hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 :=
  (B_paper_le_xc_bridge' T L hT).trans (xc_bridge_le_one' T hT)

/-! ## strip_identity_genuine from infinite_strip_identity -/

/-- The finite strip identity follows from the infinite strip identity. -/
theorem strip_identity_from_infinite' (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0,
    div_nonneg (sub_nonneg.mpr (B_paper_le_one_from_infinite' T L hT hL)) c_alpha_pos.le,
    le_refl _, ?_⟩
  have hca : c_alpha ≠ 0 := ne_of_gt c_alpha_pos
  simp only [mul_zero, add_zero]
  rw [mul_div_cancel₀ _ hca, sub_add_cancel]

end