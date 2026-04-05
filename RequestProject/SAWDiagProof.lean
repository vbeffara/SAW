/-
# Diagonal bridge proof infrastructure

This file provides infrastructure connecting diagonal bridges
to the strip identity and saw_count.

The fundamental sorry remains `B_paper_le_one_direct` from
SAWStripIdentityCorrect.lean (the core strip identity).
-/

import Mathlib
import RequestProject.SAWDiagConnection
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Paper-compatible bridges (matching PaperInfStrip exactly)

These bridges use the tighter PaperInfStrip constraints:
- TRUE: -(T-1) ≤ x+y ≤ 0
- FALSE: -T ≤ x+y ≤ -1

This ensures the endpoint (FALSE, x+y=-T) matches PaperSAW_B. -/

/-- A paper-compatible bridge of width T from paperStart. -/
structure PaperBridge (T : ℕ) where
  end_v : HexVertex
  walk : hexGraph.Path paperStart end_v
  end_right : end_v.1 + end_v.2.1 = -(T : ℤ) ∧ end_v.2.2 = false
  in_strip : ∀ v ∈ walk.1.support, PaperInfStrip T v

/-- Paper bridge partition function (edge-count convention). -/
def paper_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : PaperBridge T), x ^ b.walk.1.length

/-- Paper bridge length ≥ T (diagonal coordinate changes by T). -/
lemma paper_bridge_length_ge (T : ℕ) (b : PaperBridge T) :
    T ≤ b.walk.1.length := by
  have h := hexGraph_walk_sum_bound_neg b.walk.1
  have h_start : paperStart.1 + paperStart.2.1 = 0 := by simp [paperStart]
  have h_end := b.end_right.1
  rw [h_start] at h
  omega

/-- Each paper bridge fits in PaperFinStrip for large enough L. -/
lemma paper_bridge_in_fin_strip (T : ℕ) (b : PaperBridge T) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ v ∈ b.walk.1.support, PaperFinStrip T L v := by
  use b.walk.1.length + 1
  refine ⟨by omega, fun v hv => ?_⟩
  constructor
  · exact b.in_strip v hv
  · have hbnd := hexGraph_walk_bound (b.walk.1.takeUntil v hv)
    obtain ⟨hb1, hb2, _, _⟩ := hbnd
    have hlen := b.walk.1.length_takeUntil_le hv
    simp [paperStart] at hb1 hb2
    cases v.2.2 <;> simp <;> omega

/-- Map a PaperBridge to a PaperSAW_B, given it fits in a finite strip. -/
def paperBridgeToSAWB (T L : ℕ) (b : PaperBridge T)
    (hfit : ∀ v ∈ b.walk.1.support, PaperFinStrip T L v) : PaperSAW_B T L :=
  ⟨b.walk.1.length, ⟨b.end_v, b.walk, rfl⟩, b.end_right, hfit⟩

/-- The mapping preserves walk length. -/
lemma paperBridgeToSAWB_len (T L : ℕ) (b : PaperBridge T)
    (hfit : ∀ v ∈ b.walk.1.support, PaperFinStrip T L v) :
    (paperBridgeToSAWB T L b hfit).len = b.walk.1.length := rfl

/-
The mapping is injective.
-/
lemma paperBridgeToSAWB_injective (T L : ℕ)
    {b₁ b₂ : PaperBridge T}
    (hfit₁ : ∀ v ∈ b₁.walk.1.support, PaperFinStrip T L v)
    (hfit₂ : ∀ v ∈ b₂.walk.1.support, PaperFinStrip T L v)
    (h : paperBridgeToSAWB T L b₁ hfit₁ = paperBridgeToSAWB T L b₂ hfit₂) :
    b₁ = b₂ := by
  cases b₁ ; cases b₂ ; simp_all +decide [ paperBridgeToSAWB ];
  grind

/-- Bridge partial sum + 1 is bounded by B_paper. -/
lemma paper_bridge_partial_sum_shifted_le (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (F : Finset (PaperBridge T))
    (hfit : ∀ b ∈ F, ∀ v ∈ b.walk.1.support, PaperFinStrip T L v) :
    ∑ b ∈ F, xc ^ (b.walk.1.length + 1) ≤ 1 := by
  classical
  -- PaperSAW_B T L is finite (same proof as paper_saw_b_finite)
  haveI : Finite (PaperSAW_B T L) := by
    have hfin := paper_fin_strip_finite T L
    have ⟨N, hN⟩ : ∃ N, ∀ s : PaperSAW_B T L, s.len ≤ N := by
      use hfin.toFinset.card; intro s
      have h_supp : s.saw.p.1.support.toFinset ⊆ hfin.toFinset := by
        intro v hv; exact hfin.mem_toFinset.mpr (s.in_strip v (by simpa using hv))
      have := Finset.card_le_card h_supp
      rw [List.toFinset_card_of_nodup s.saw.p.2.support_nodup] at this
      have hslen := s.saw.l
      have : s.saw.p.1.length + 1 = s.saw.p.1.support.length :=
        (SimpleGraph.Walk.length_support s.saw.p.1).symm
      linarith
    exact Finite.of_injective
      (fun s : PaperSAW_B T L => (⟨⟨s.len, Nat.lt_add_one_iff.mpr (hN s)⟩, s.saw⟩ : (Σ n : Fin (N+1), SAW paperStart n)))
      (fun s t h => by cases s; cases t; aesop)
  haveI inst : Fintype (PaperSAW_B T L) := Fintype.ofFinite _
  -- Define the injection from F to PaperSAW_B T L
  let f : (b : PaperBridge T) → b ∈ F → PaperSAW_B T L :=
    fun b hb => paperBridgeToSAWB T L b (hfit b hb)
  -- Map the sum
  have h_sum : ∑ b ∈ F, xc ^ (b.walk.1.length + 1) =
      ∑ s ∈ F.attach.image (fun b => f b.1 b.2), xc ^ (s.len + 1) := by
    rw [Finset.sum_image]
    · conv_lhs => rw [← Finset.sum_attach F]
      exact Finset.sum_congr rfl fun b _ => by simp [f, paperBridgeToSAWB]
    · intro a _ b _ hab
      have := paperBridgeToSAWB_injective T L (hfit a.1 a.2) (hfit b.1 b.2) hab
      exact Subtype.ext this
  rw [h_sum]
  -- The image is a subset of Finset.univ
  calc ∑ s ∈ F.attach.image (fun b => f b.1 b.2), xc ^ (s.len + 1)
      ≤ ∑ s : PaperSAW_B T L, xc ^ (s.len + 1) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun s _ => Finset.mem_univ s)
          (fun s _ _ => pow_nonneg xc_pos.le _)
    _ = B_paper T L xc := by rw [show B_paper T L xc = ∑ s : PaperSAW_B T L, xc ^ (s.len + 1)
          from by unfold B_paper; exact tsum_fintype _]
    _ ≤ 1 := B_paper_le_one_direct T L hT hL

/-
Finite partial sums of paper bridge weights are ≤ 1/xc.
    From B_paper(T,L,xc) = Σ xc^{n+1} ≤ 1, we get Σ xc^n ≤ 1/xc.
    This uses B_paper_le_one (which depends on B_paper_le_one_direct).
-/
lemma paper_bridge_partial_sum_le (T : ℕ) (hT : 1 ≤ T)
    (F : Finset (PaperBridge T)) :
    ∑ b ∈ F, xc ^ b.walk.1.length ≤ 1 / xc := by
  have hL : ∃ L : ℕ, 1 ≤ L ∧ ∀ b ∈ F, ∀ v ∈ b.walk.1.support, PaperFinStrip T L v := by
    have hL_exists : ∀ b ∈ F, ∃ L_b : ℕ, 1 ≤ L_b ∧ ∀ v ∈ b.walk.1.support, PaperFinStrip T L_b v := by
      exact?;
    choose! L hL₁ hL₂ using hL_exists;
    use Finset.sup F L + 1;
    simp_all +decide [ PaperFinStrip ];
    intro b hb a a_1; specialize hL₂ b hb a a_1; constructor <;> intro h <;> constructor;
    · exact hL₂.1 h |>.1;
    · constructor <;> linarith [ hL₂.1 h, show ( L b : ℤ ) ≤ F.sup L from mod_cast Finset.le_sup ( f := L ) hb ];
    · exact hL₂.2 h |>.1;
    · constructor <;> linarith [ hL₂.2 h, show ( L b : ℤ ) ≤ F.sup L from mod_cast Finset.le_sup ( f := L ) hb ];
  obtain ⟨ L, hL₁, hL₂ ⟩ := hL;
  convert div_le_div_of_nonneg_right ( paper_bridge_partial_sum_shifted_le T L hT hL₁ F hL₂ ) ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) using 1;
  rw [ Finset.sum_div _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ pow_succ, mul_div_cancel_right₀ _ ( ne_of_gt xc_pos ) ] ;

/-- paper_bridge_partition T xc ≤ 1/xc. -/
theorem paper_bridge_upper_bound (T : ℕ) (hT : 1 ≤ T) :
    paper_bridge_partition T xc ≤ 1 / xc := by
  exact Real.tsum_le_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => paper_bridge_partial_sum_le T hT F)

end