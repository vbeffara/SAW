/-
# Deriving B_paper_le_one_strip from infinite_strip_identity

The key insight: every walk in PaperSAW_B T L (finite strip) injects into
PaperBridge T (infinite strip). Combined with the infinite strip identity
  1 = c_α · A_inf(T) + xc · paper_bridge_partition(T)
this gives B_paper(T,L,xc) ≤ xc · paper_bridge_partition(T) ≤ 1.

This reduces sorry #1 (B_paper_le_one_strip) to sorry #2 (infinite_strip_identity).
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWCutting
import RequestProject.SAWStripIdentityCorrect
import RequestProject.SAWRecurrenceProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- Map a PaperSAW_B (finite strip walk to right boundary) to a PaperBridge
    (infinite strip walk to right boundary). -/
def paperSAWB_to_bridge (T L : ℕ) (s : PaperSAW_B T L) : PaperBridge T where
  end_v := s.saw.w
  walk := s.saw.p
  end_right := s.end_right
  in_strip := fun v hv => (s.in_strip v hv).1

/-- The mapping preserves walk length. -/
lemma paperSAWB_to_bridge_length (T L : ℕ) (s : PaperSAW_B T L) :
    (paperSAWB_to_bridge T L s).walk.1.length = s.len := by
  simp [paperSAWB_to_bridge, s.saw.l]

/-- The mapping is injective. -/
lemma paperSAWB_to_bridge_injective (T L : ℕ) :
    Function.Injective (paperSAWB_to_bridge T L) := by
  have key : Function.Injective (fun s : PaperSAW_B T L =>
    (⟨s.saw.w, s.saw.p⟩ : Σ w, hexGraph.Path paperStart w)) := by
    intro ⟨n₁, ⟨w₁, p₁, l₁⟩, h₁, hs₁⟩ ⟨n₂, ⟨w₂, p₂, l₂⟩, h₂, hs₂⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h_p⟩ := h
    have h_p' : p₁ = p₂ := eq_of_heq h_p
    subst h_p'
    have h_len : n₁ = n₂ := by omega
    subst h_len; rfl
  intro s₁ s₂ heq
  apply key
  cases s₁; cases s₂
  simp only [paperSAWB_to_bridge, PaperBridge.mk.injEq] at heq
  simp only [Sigma.mk.inj_iff]
  exact ⟨heq.1, heq.2⟩

/-
B_paper(T,L,xc) ≤ xc · paper_bridge_partition(T,xc).
-/
lemma B_paper_le_xc_mul_bridge (T L : ℕ) (hT : 1 ≤ T) :
    B_paper T L xc ≤ xc * paper_bridge_partition T xc := by
  -- By definition of $B_paper$, we have $B_paper T L xc = xc * \sum' s, xc^{s.len}$.
  have hB_paper_def : B_paper T L xc = xc * ∑' s : PaperSAW_B T L, xc ^ s.len := by
    unfold B_paper; rw [ ← tsum_mul_left ] ; congr; ext; ring;
  -- Since $xc > 0$, we can divide both sides of the inequality by $xc$.
  have h_div : ∑' s : PaperSAW_B T L, xc ^ s.len ≤ ∑' b : PaperBridge T, xc ^ b.walk.1.length := by
    -- Since $xc > 0$, we can apply the comparison test for series.
    have h_comparison : Summable (fun b : PaperBridge T => xc ^ b.walk.1.length) := by
      contrapose! hT;
      have h_contra : ∀ F : Finset (PaperBridge T), ∑ b ∈ F, xc ^ b.walk.1.length ≤ 1 / xc := by
        intros F
        apply paper_bridge_partial_sum_le T (by
        rcases T with ( _ | _ | T ) <;> norm_num at *) F;
      convert absurd ( show Summable ( fun b : PaperBridge T => xc ^ ( b.walk.1.length ) ) from ?_ ) hT using 1;
      refine' summable_of_sum_le _ _;
      exacts [ 1 / xc, fun _ => pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _, h_contra ];
    have h_comparison : ∑' s : PaperSAW_B T L, xc ^ s.len ≤ ∑' b : {b : PaperBridge T // ∃ s : PaperSAW_B T L, paperSAWB_to_bridge T L s = b}, xc ^ b.val.walk.1.length := by
      convert rfl.le using 1;
      erw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun s : PaperSAW_B T L => ⟨ paperSAWB_to_bridge T L s, s, rfl ⟩ : PaperSAW_B T L → { b : PaperBridge T // ∃ s : PaperSAW_B T L, paperSAWB_to_bridge T L s = b } ) ⟨ fun a => ?_, fun a => ?_ ⟩ ) ];
      congr! 1;
      ext; simp [paperSAWB_to_bridge_length];
      · exact fun s hs => paperSAWB_to_bridge_injective T L <| by injection hs;
      · aesop;
    refine le_trans h_comparison ?_;
    convert Summable.tsum_subtype_le _ _;
    rotate_left;
    exact PaperBridge T;
    exact ℝ;
    all_goals try infer_instance;
    exact fun b => xc ^ b.walk.1.length;
    exact Set.range ( fun s : PaperSAW_B T L => paperSAWB_to_bridge T L s );
    exact ⟨ fun h => fun _ _ => h, fun h => h ( fun _ => pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ ) ‹_› ⟩;
  exact hB_paper_def.symm ▸ mul_le_mul_of_nonneg_left h_div ( by unfold xc; positivity )

/-- **B_paper(T,L,xc) ≤ 1** derived from infinite_strip_identity. -/
lemma B_paper_le_one_from_identity (T L : ℕ) (hT : 1 ≤ T) (_hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  have h_id := infinite_strip_identity T hT
  have h_bridge_bound : xc * paper_bridge_partition T xc ≤ 1 := by
    have h_A_nonneg : 0 ≤ A_inf T xc := A_inf_nonneg T xc xc_pos.le
    have h_ca_pos := c_alpha_pos
    nlinarith [mul_nonneg h_ca_pos.le h_A_nonneg]
  exact le_trans (B_paper_le_xc_mul_bridge T L hT) h_bridge_bound

end