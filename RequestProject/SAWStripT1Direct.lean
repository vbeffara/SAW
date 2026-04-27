/-
# Direct proofs for T=1 strip

Proves B_paper(1,L,xc) < 1 and strip_identity_genuine for T=1.
The algebraic identity c_alpha * xc = (√2-1)/2 is also proved.
-/

import Mathlib
import RequestProject.SAWStripT1Exact
import RequestProject.SAWCutting

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-- Map a PaperSAW_B to a PaperBridge. -/
def paperSAWB_to_bridge' (T L : ℕ) (s : PaperSAW_B T L) : PaperBridge T where
  end_v := s.saw.w
  walk := s.saw.p
  end_right := s.end_right
  in_strip := fun v hv => (s.in_strip v hv).1

lemma paperSAWB_to_bridge'_len (T L : ℕ) (s : PaperSAW_B T L) :
    (paperSAWB_to_bridge' T L s).walk.1.length = s.len := by
  simp [paperSAWB_to_bridge', s.saw.l]

lemma paperSAWB_to_bridge'_injective (T L : ℕ) :
    Function.Injective (paperSAWB_to_bridge' T L) := by
  intro s1 s2 h_eq;
  cases s1 ; cases s2 ; simp_all +decide [ paperSAWB_to_bridge' ];
  cases ‹SAW paperStart _› ; cases ‹SAW paperStart _› ; aesop

/-
PaperBridge 1 weights are summable (sorry-free, from geometric series).
-/
lemma paper_bridge_1_summable :
    Summable (fun b : PaperBridge 1 => xc ^ b.walk.1.length) := by
  have := @paper_bridge_partition_1_eq;
  contrapose! this;
  unfold paper_bridge_partition;
  rw [ tsum_eq_zero_of_not_summable this ] ; norm_num [ xc ];
  exact ne_of_lt ( div_pos ( mul_pos zero_lt_two ( inv_pos.mpr ( Real.sqrt_pos.mpr ( by positivity ) ) ) ) ( sub_pos.mpr ( inv_lt_one_of_one_lt₀ ( by rw [ Real.sq_sqrt ] <;> nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ) ) ) )

/-
B_paper(1,L,xc) ≤ xc · paper_bridge_partition(1,xc) (T=1 specific, sorry-free).
-/
lemma B_paper_1_le (L : ℕ) :
    B_paper 1 L xc ≤ xc * paper_bridge_partition 1 xc := by
  by_cases hL : 1 ≤ L <;> simp_all +decide [ B_paper, paper_bridge_partition ];
  · -- By definition of $B_paper$, we know that
    have hB_paper_def : ∑' (s : PaperSAW_B 1 L), xc ^ (s.len + 1) = xc * ∑' (s : PaperSAW_B 1 L), xc ^ s.len := by
      rw [ ← tsum_mul_left ] ; exact tsum_congr fun _ => by ring;
    have hB_paper_le : ∑' (s : PaperSAW_B 1 L), xc ^ s.len ≤ ∑' (b : PaperBridge 1), xc ^ b.walk.1.length := by
      have hB_paper_le : ∑' (s : PaperSAW_B 1 L), xc ^ s.len ≤ ∑' (b : ↥(Set.range (paperSAWB_to_bridge' 1 L))), xc ^ b.val.walk.1.length := by
        rw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ ( paperSAWB_to_bridge'_injective 1 L ) ) ];
        convert le_rfl;
        exact paperSAWB_to_bridge'_len _ _ _;
      refine le_trans hB_paper_le ?_;
      have hB_paper_le : Summable (fun b : PaperBridge 1 => xc ^ b.walk.1.length) := by
        convert paper_bridge_1_summable using 1;
      convert Summable.tsum_subtype_le _ _;
      rotate_left;
      exact PaperBridge 1;
      exact ℝ;
      all_goals try infer_instance;
      exact fun b => xc ^ b.walk.1.length;
      exact Set.range ( paperSAWB_to_bridge' 1 L );
      exact ⟨ fun h => fun _ _ => h, fun h => h ( fun _ => pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ ) hB_paper_le ⟩;
    exact hB_paper_def.symm ▸ mul_le_mul_of_nonneg_left hB_paper_le ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) );
  · rw [ tsum_eq_sum ];
    any_goals exact ∅;
    · exact mul_nonneg ( show 0 ≤ xc by exact le_of_lt ( show 0 < xc by exact by unfold xc; positivity ) ) ( tsum_nonneg fun _ => pow_nonneg ( show 0 ≤ xc by exact le_of_lt ( show 0 < xc by exact by unfold xc; positivity ) ) _ );
    · rintro ⟨ len, saw, end_right, in_strip ⟩ ; have := in_strip paperStart ; simp_all +decide [ PaperFinStrip ]

/-- 2xc²/(1-xc²) < 1. -/
lemma two_xc_sq_div_lt_one' : 2 * xc ^ 2 / (1 - xc ^ 2) < 1 := by
  rw [div_lt_iff₀] <;> norm_num [xc]
  · rw [Real.sq_sqrt] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two,
      inv_mul_cancel₀ (show (2 + Real.sqrt 2) ≠ 0 by positivity)]
  · exact inv_lt_one_of_one_lt₀ <| one_lt_pow₀
      (Real.lt_sqrt_of_sq_lt <| by linarith [Real.sqrt_nonneg 2]) two_ne_zero

/-- B_paper(1,L,xc) < 1 for all L. -/
lemma B_paper_1_lt_one' (L : ℕ) : B_paper 1 L xc < 1 :=
  calc B_paper 1 L xc ≤ xc * paper_bridge_partition 1 xc := B_paper_1_le L
    _ = 2 * xc ^ 2 / (1 - xc ^ 2) := by rw [paper_bridge_partition_1_eq]; ring
    _ < 1 := two_xc_sq_div_lt_one'

/-- strip_identity_genuine for T = 1 (sorry-free once B_paper_1_le is proved). -/
theorem strip_identity_genuine_T1' (L : ℕ) (_hL : 1 ≤ L) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper 1 L xc + c_eps * E_m := by
  exact ⟨(1 - B_paper 1 L xc) / c_alpha, 0,
          div_nonneg (sub_nonneg.mpr (B_paper_1_lt_one' L).le) c_alpha_pos.le,
          le_refl _,
          by simp only [mul_zero, add_zero]
             rw [mul_div_cancel₀ _ (ne_of_gt c_alpha_pos)]; ring⟩

/-- c_alpha * xc = (√2 - 1) / 2. -/
lemma c_alpha_xc_eq' : c_alpha * xc = (Real.sqrt 2 - 1) / 2 := by
  unfold c_alpha xc
  rw [show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_pi_div_two_sub]
  norm_num
  rw [← div_eq_mul_inv, div_eq_iff] <;> ring <;> norm_num
  · rw [← sq_eq_sq₀] <;> ring <;> norm_num
    · rw [Real.sq_sqrt, Real.sq_sqrt] <;> nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    · exact le_mul_of_one_le_left (Real.sqrt_nonneg _) (Real.le_sqrt_of_sq_le (by norm_num))
  · positivity

end