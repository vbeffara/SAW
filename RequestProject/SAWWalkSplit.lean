/-
# Walk Splitting and Monotonicity Infrastructure

Helper lemmas for splitting walks and monotonicity of B_paper in L.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWDecompHelper

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk prefix/suffix length relation -/

/-- Walk length = prefix length + suffix length. -/
lemma walk_split_lengths' {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    p.length = (p.takeUntil u hu).length + (p.dropUntil u hu).length := by
  have h := p.take_spec hu
  calc p.length = ((p.takeUntil u hu).append (p.dropUntil u hu)).length := by rw [h]
    _ = _ := SimpleGraph.Walk.length_append _ _

/-! ## Monotonicity of B_paper in L -/

/-- PaperFinStrip T L₁ ⊆ PaperFinStrip T L₂ for L₁ ≤ L₂. -/
lemma PaperFinStrip_mono_L {T L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) (v : HexVertex) :
    PaperFinStrip T L₁ v → PaperFinStrip T L₂ v := by
  intro ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  cases hb : v.2.2 <;> simp_all <;> omega

/-- PaperSAW_B T L₁ maps into PaperSAW_B T L₂ for L₁ ≤ L₂. -/
def PaperSAW_B_widen {T L₁ L₂ : ℕ} (hL : L₁ ≤ L₂)
    (s : PaperSAW_B T L₁) : PaperSAW_B T L₂ where
  len := s.len
  saw := s.saw
  end_right := s.end_right
  in_strip := fun v hv => PaperFinStrip_mono_L hL v (s.in_strip v hv)

/-- The widening is injective. -/
lemma PaperSAW_B_widen_injective {T L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    Function.Injective (@PaperSAW_B_widen T L₁ L₂ hL) := by
  intro ⟨n₁, s₁, h₁, g₁⟩ ⟨n₂, s₂, h₂, g₂⟩ h
  simp only [PaperSAW_B_widen] at h
  obtain ⟨rfl, hs⟩ := h
  congr 1

/-
B_paper is monotone increasing in L.
-/
lemma B_paper_mono_L (T L₁ L₂ : ℕ) (hL : L₁ ≤ L₂) (x : ℝ) (hx : 0 ≤ x) :
    B_paper T L₁ x ≤ B_paper T L₂ x := by
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : PaperSAW_B T L₁ ≃ Fin (Nat.card (PaperSAW_B T L₁)), True := by
    haveI := Fintype.ofFinite ( PaperSAW_B T L₁ ) ; exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ Nat.card_eq_fintype_card ], trivial ⟩ ;
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : PaperSAW_B T L₂ ≃ Fin (Nat.card (PaperSAW_B T L₂)), True := by
    exact ⟨ Finite.equivFin _, trivial ⟩;
  have h_inj : Function.Injective (@PaperSAW_B_widen T L₁ L₂ hL) := by
    exact?;
  have h_sum_le : ∑ i : Fin (Nat.card (PaperSAW_B T L₁)), x ^ ((f₁.symm i).len + 1) ≤ ∑ i : Fin (Nat.card (PaperSAW_B T L₂)), x ^ ((f₂.symm i).len + 1) := by
    have h_sum_le : ∑ i ∈ Finset.univ.image (fun i => f₂ (PaperSAW_B_widen hL (f₁.symm i))), x ^ ((f₂.symm i).len + 1) ≤ ∑ i : Fin (Nat.card (PaperSAW_B T L₂)), x ^ ((f₂.symm i).len + 1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => pow_nonneg hx _;
    rw [ Finset.sum_image ] at h_sum_le;
    · aesop;
    · exact fun i _ j _ hij => by simpa [ h_inj.eq_iff ] using f₂.injective hij;
  convert h_sum_le using 1;
  · unfold B_paper;
    rw [ ← Equiv.tsum_eq f₁.symm ];
    rw [ tsum_fintype ];
  · unfold B_paper;
    rw [ ← Equiv.tsum_eq f₂.symm ];
    rw [ tsum_fintype ]

end