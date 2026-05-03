/-
# Connection between finite strip B_paper and infinite strip paper_bridge_partition

B_paper(T, L, xc) ≤ xc · paper_bridge_partition(T, xc)

This follows because each PaperSAW_B T L (finite strip walk to right boundary)
maps injectively to a PaperBridge T (infinite strip bridge) with the same walk,
and B_paper uses vertex weight xc^{n+1} = xc · xc^n while
paper_bridge_partition uses edge weight xc^n.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- Map a PaperSAW_B to a PaperBridge: the walk satisfies the infinite strip
    constraint since PaperFinStrip T L v implies PaperInfStrip T v. -/
def paperSAWB_to_bridge {T L : ℕ} (s : PaperSAW_B T L) : PaperBridge T where
  end_v := s.saw.w
  walk := s.saw.p
  end_right := s.end_right
  in_strip := fun v hv => (s.in_strip v hv).1

/-- The map preserves walk length. -/
lemma paperSAWB_to_bridge_length {T L : ℕ} (s : PaperSAW_B T L) :
    (paperSAWB_to_bridge s).walk.1.length = s.len := by
  simp [paperSAWB_to_bridge]; exact s.saw.l

/-
The map is injective.
-/
lemma paperSAWB_to_bridge_injective (T L : ℕ) :
    Function.Injective (@paperSAWB_to_bridge T L) := by
  intro s₁ s₂ h_eq;
  cases s₁ ; cases s₂ ; simp_all +decide [ paperSAWB_to_bridge ];
  cases ‹SAW paperStart _› ; cases ‹SAW paperStart _› ; aesop

/-
B_paper(T, L, xc) ≤ xc · paper_bridge_partition(T, xc).

    Each finite strip walk of length n has weight xc^{n+1} in B_paper,
    which equals xc · xc^n = xc times the bridge weight. The injection
    from PaperSAW_B to PaperBridge gives the bound.
-/
theorem B_paper_le_xc_mul_bridge (T L : ℕ) (hT : 1 ≤ T) :
    B_paper T L xc ≤ xc * paper_bridge_partition T xc := by
  by_contra h_contra;
  obtain ⟨F, hF⟩ : ∃ F : Finset (PaperSAW_B T L), ∑ s ∈ F, xc ^ (s.len + 1) > xc * paper_bridge_partition T xc := by
    contrapose! h_contra;
    refine' Summable.tsum_le_of_sum_le _ _;
    · refine' summable_of_sum_le _ _;
      exacts [ xc * paper_bridge_partition T xc, fun _ => pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _, h_contra ];
    · assumption;
  -- Since F is a finite set of PaperSAW_B T L, we can map each element to a PaperBridge T.
  have h_map : ∃ G : Finset (PaperBridge T), (∑ s ∈ F, xc ^ (s.len + 1)) = xc * (∑ b ∈ G, xc ^ b.walk.1.length) := by
    -- Since F is finite, the image of F under paperSAWB_to_bridge is also finite.
    have h_image_finite : Set.Finite (Set.image (fun s : PaperSAW_B T L => paperSAWB_to_bridge s) F) := by
      exact F.finite_toSet.image _;
    obtain ⟨ G, hG ⟩ := h_image_finite.exists_finset_coe;
    rw [ show ( ∑ s ∈ F, xc ^ ( s.len + 1 ) ) = ∑ b ∈ G, xc ^ ( b.walk.1.length + 1 ) from ?_ ];
    · exact ⟨ G, by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring ⟩;
    · apply Finset.sum_bij (fun s _ => paperSAWB_to_bridge s);
      · exact fun x hx => hG.symm.subset <| Set.mem_image_of_mem _ hx;
      · exact fun s₁ hs₁ s₂ hs₂ h => paperSAWB_to_bridge_injective T L h;
      · exact fun b hb => by rw [ Set.ext_iff ] at hG; specialize hG b; aesop;
      · exact fun s hs => by rw [ paperSAWB_to_bridge_length s ] ;
  obtain ⟨ G, hG ⟩ := h_map;
  have hG_le : ∑ b ∈ G, xc ^ b.walk.1.length ≤ paper_bridge_partition T xc := by
    refine' Summable.sum_le_tsum _ _ _;
    · exact fun _ _ => pow_nonneg ( by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _;
    · refine' summable_of_sum_le _ _;
      exact 1 / xc;
      · exact fun _ => pow_nonneg ( by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _;
      · grind +suggestions;
  nlinarith [ show 0 < xc by exact div_pos zero_lt_one ( Real.sqrt_pos.mpr ( show 0 < 2 + Real.sqrt 2 by positivity ) ) ]

end