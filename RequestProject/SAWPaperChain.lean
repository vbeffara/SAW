/-
# Corrected Bridge Chain using Paper (Diagonal) Bridges

## Critical architectural fix

The original `OriginBridge` and `origin_bridge_partition` in SAWBridgeFix.lean
use **x-coordinate strips** (Bridge T: start at x=0, end at x=T, all vertices
in 0 ≤ x ≤ T). The paper's strip identity B ≤ 1 uses **diagonal strips**
(strips defined by x+y coordinates, aligned with Re(z) in the embedding).

The statement `origin_bridge_partition T xc ≤ 1` is **FALSE** for x-coordinate
bridges. For T=1, there are 1 bridge of length 1 and 4 bridges of length 3,
giving sum ≈ xc + 4xc³ ≈ 1.18 > 1. The strip identity only gives B ≤ 1 for
diagonal strips (where the direction factor for right boundary mid-edges has
positive real part).

This file provides the **corrected bridge chain** using `PaperBridge` from
SAWDiagProof.lean (diagonal bridges matching the paper's convention). The
corrected bridge partition satisfies paper_bridge_partition T xc ≤ 1/xc
(proved in paper_bridge_upper_bound, modulo B_paper_le_one_direct).

## Main results

1. `paper_bridge_to_SAW`: PaperBridge injects into SAW paperStart
2. `paper_bridge_sum_le_Z`: Σ paper_bridge_partition(T+1) ≤ Z(xc)
3. `paper_bridge_decay_corrected`: paper_bridge_partition T x ≤ (x/xc)^T / xc
4. `Z_xc_diverges_corrected`: Z(xc) = ∞ (from paper bridge lower bound)
5. `hw_summable_corrected`: Z(x) < ∞ for x < xc
6. `connective_constant_eq_corrected`: μ = √(2+√2)
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## PaperBridge to SAW injection -/

/-- Convert a PaperBridge to a SAW from paperStart. -/
def paperBridge_toSAW {T : ℕ} (b : PaperBridge T) :
    SAW paperStart b.walk.1.length :=
  ⟨b.end_v, b.walk, rfl⟩

/-- The PaperBridge-to-SAW map is injective (as sigma types). -/
lemma paperBridge_toSAW_sigma_injective (T : ℕ) :
    Function.Injective (fun b : PaperBridge T =>
      (⟨b.walk.1.length, paperBridge_toSAW b⟩ : Σ n, SAW paperStart n)) := by
  intro b₁ b₂ h; cases b₁; cases b₂
  unfold paperBridge_toSAW at h; grind

/-- PaperBridges of different widths end at different diagonal coordinates. -/
lemma paper_bridge_endpoints_differ {T₁ T₂ : ℕ} (hT : T₁ ≠ T₂)
    (b₁ : PaperBridge T₁) (b₂ : PaperBridge T₂) :
    b₁.end_v ≠ b₂.end_v := by
  intro h
  have h1 := b₁.end_right.1
  have h2 := b₂.end_right.1
  rw [h] at h1; omega

/-- SAW count from paperStart equals saw_count. -/
lemma saw_count_paperStart (n : ℕ) :
    Fintype.card (SAW paperStart n) = saw_count n :=
  saw_count_vertex_independent paperStart n

/-! ## Paper bridge lower bound (Case 2 of the proof)

The strip identity gives 1 = c_α·A_T + B_T·xc + c_ε·E_T where
B_T·xc is the infinite-strip B_paper limit. From the quadratic
recurrence, B_T ≥ c/T. -/

/-- Paper bridge lower bound: ∃ c > 0, paper_bridge_partition T xc ≥ c/T.
    This is Case 2 of the proof, using the quadratic recurrence. -/
theorem paper_bridge_lower_bound :
    ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ paper_bridge_partition T xc := by
  sorry

/-! ## Bridge sum ≤ Z -/

/-
For a finite set of paper bridges of width T, the total weight is bounded
    by a sum of saw_count values.
-/
lemma paper_bridge_filter_card_le (T n : ℕ) (F : Finset (PaperBridge T)) :
    (F.filter (fun b => b.walk.1.length = n)).card ≤ saw_count n := by
  have h_inj : Function.Injective (fun b : PaperBridge T => (⟨b.walk.1.length, paperBridge_toSAW b⟩ : Σ n, SAW paperStart n)) := by
    exact paperBridge_toSAW_sigma_injective T
  have h_image : Finset.image (fun b : PaperBridge T => (⟨b.walk.1.length, paperBridge_toSAW b⟩ : Σ n, SAW paperStart n)) (Finset.filter (fun b : PaperBridge T => b.walk.1.length = n) F) ⊆ Finset.image (fun s : SAW paperStart n => ⟨n, s⟩) (Finset.univ : Finset (SAW paperStart n)) := by
    intro x hx
    aesop;
  convert Finset.card_le_card h_image using 1;
  · rw [ Finset.card_image_of_injective _ h_inj ];
  · rw [ Finset.card_image_of_injective _ fun a b h => by aesop ] ; norm_num [ saw_count, saw_count_paperStart ]

/-
For finitely many widths, the sum of paper bridge partition values
    is bounded by Z(x) when Z(x) converges.

For finitely many widths, the sum of paper bridge partition values
    is bounded by Z(x) when Z(x) converges.
    Proof: paper bridges inject into SAWs from paperStart, and bridges of
    different widths have different endpoints (by diagonal coordinate),
    so they give distinct SAWs. Then use saw_count_paperStart.
-/
lemma paper_bridge_sum_le_Z (N : ℕ) (hx : 0 < xc)
    (hsum : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    ∑ T ∈ Finset.range N, paper_bridge_partition (T + 1) xc ≤
    ∑' n, (saw_count n : ℝ) * xc ^ n := by
  grind +suggestions

/-! ## Z(xc) diverges (corrected) -/

/-- Z(xc) diverges: from paper bridge lower bound and bridge sum ≤ Z. -/
theorem Z_xc_diverges_corrected :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := paper_bridge_lower_bound
  intro h_summable
  have h_bridge_summable : Summable (fun T : ℕ =>
      paper_bridge_partition (T + 1) xc) :=
    summable_of_sum_range_le
      (fun T => tsum_nonneg fun _ => pow_nonneg xc_pos.le _)
      (fun N => paper_bridge_sum_le_Z N xc_pos h_summable)
  have h_lower : ∀ T : ℕ, c / ((T : ℝ) + 1) ≤
      paper_bridge_partition (T + 1) xc := by
    intro T; have := hc_bound (T + 1) (by omega); push_cast at this ⊢; linarith
  exact absurd
    (Summable.of_nonneg_of_le (fun T => by positivity) h_lower h_bridge_summable)
    (not_summable_of_lower_bound hc_pos (fun n => le_refl _))

/-! ## Paper bridge decay -/

/-
Paper bridge decay: paper_bridge_partition T x ≤ (x/xc)^T / xc.
    Each bridge has length ≥ T, so scaling from xc to x gains (x/xc)^T.
-/
theorem paper_bridge_decay_corrected {T : ℕ} (hT : 1 ≤ T) {x : ℝ}
    (hx : 0 < x) (hxc : x < xc) :
    paper_bridge_partition T x ≤ (x / xc) ^ T / xc := by
  convert Summable.tsum_le_of_sum_le _ _ using 1;
  · infer_instance;
  · exact SummationFilter.instNeBotUnconditional (PaperBridge T)
  · have h_summable : Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
      apply hammersley_welsh_injection x hx hxc;
    have h_summable : Summable (fun n => (saw_count n : ℝ) * x ^ n) → Summable (fun b : PaperBridge T => x ^ b.walk.1.length) := by
      intro h_summable
      have h_finite : ∀ F : Finset (PaperBridge T), ∑ b ∈ F, x ^ b.walk.1.length ≤ ∑' n, (saw_count n : ℝ) * x ^ n := by
        intro F
        have h_finite : ∑ b ∈ F, x ^ b.walk.1.length ≤ ∑ n ∈ Finset.range (F.sup (fun b => b.walk.1.length) + 1), ∑ b ∈ F.filter (fun b => b.walk.1.length = n), x ^ n := by
          simp +decide only [Finset.sum_filter];
          rw [ Finset.sum_comm ];
          simp +zetaDelta at *;
          exact Finset.sum_le_sum fun b hb => by rw [ if_pos ( Finset.le_sup ( f := fun b => ( b.walk.1.length : ℕ ) ) hb ) ] ;
        refine le_trans h_finite <| le_trans ( Finset.sum_le_sum fun n hn => ?_ ) <| Summable.sum_le_tsum _ ( fun n hn => by positivity ) h_summable;
        have h_finite : (F.filter (fun b => b.walk.1.length = n)).card ≤ saw_count n := by
          convert paper_bridge_filter_card_le T n F using 1;
        simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_finite ) ( pow_nonneg hx.le n );
      refine' summable_of_sum_le _ _;
      exacts [ ∑' n : ℕ, ( saw_count n : ℝ ) * x ^ n, fun _ => by positivity, h_finite ];
    exact h_summable ‹_›;
  · intro s;
    -- Each paper bridge of width T has length ≥ T (by paper_bridge_length_ge). For each bridge b:
    have h_bound : ∀ b : PaperBridge T, x ^ b.walk.1.length ≤ (x / xc) ^ T * xc ^ b.walk.1.length := by
      intro b
      have h_length : b.walk.1.length ≥ T := by
        exact paper_bridge_length_ge T b;
      rw [ div_pow, div_mul_eq_mul_div, le_div_iff₀ ];
      · rw [ show x ^ ( b.walk.1.length : ℕ ) = x ^ T * x ^ ( b.walk.1.length - T ) by rw [ ← pow_add, Nat.add_sub_of_le h_length ], show xc ^ ( b.walk.1.length : ℕ ) = xc ^ T * xc ^ ( b.walk.1.length - T ) by rw [ ← pow_add, Nat.add_sub_of_le h_length ] ] ; ring_nf;
        rw [ mul_right_comm ] ; gcongr;
        exact mul_nonneg ( pow_nonneg hx.le _ ) ( pow_nonneg ( by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ );
      · exact pow_pos ( by exact lt_of_le_of_lt ( by positivity ) hxc ) _;
    refine' le_trans ( Finset.sum_le_sum fun b hb => h_bound b ) _;
    -- Since $xc > 0$, we can factor out $(x / xc)^T$ from the sum.
    suffices h_factor : ∑ i ∈ s, xc ^ (i.walk.1.length) ≤ 1 / xc by
      simpa only [ ← Finset.mul_sum _ _ _, one_div ] using mul_le_mul_of_nonneg_left h_factor ( pow_nonneg ( div_nonneg hx.le ( by linarith ) ) _ );
    convert paper_bridge_partial_sum_le T hT s using 1

/-! ## Hammersley-Welsh summability (corrected) -/

/-- Bridge decomposition injection (paper bridges):
    Σ c_n x^n ≤ 2·(Σ_S Π paper_bridge_partition(T+1, x))² -/
theorem paper_bridge_decomp_injection {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

/-
Hammersley-Welsh summability (corrected): Z(x) < ∞ for 0 < x < xc.
-/
/-- Hammersley-Welsh summability (corrected): Z(x) < ∞ for 0 < x < xc.
    Depends on paper_bridge_decomp_injection (the HW decomposition). -/
theorem hw_summable_corrected {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  sorry

/-! ## Main theorem (corrected) -/

/-- **Main Theorem** (Duminil-Copin & Smirnov, 2012, corrected bridge chain):
    The connective constant of the hexagonal lattice equals √(2+√2).

    This version uses the corrected paper bridge definitions (diagonal strips)
    rather than the incorrect x-coordinate bridges. -/
theorem connective_constant_eq_corrected :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) :=
  connective_constant_eq_from_bounds
    Z_xc_diverges_corrected
    (fun x hx hxc => hw_summable_corrected hx hxc)

end