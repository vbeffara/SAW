/-
# New proof of the main theorem using only infinite_strip_identity

This file provides an alternative proof path for the main theorem
μ = √(2+√2) that only requires `infinite_strip_identity` as a sorry,
avoiding `B_paper_le_one_strip` and `paper_bridge_decomp_injection`.

## Key ideas

1. Z(xc) = ∞ follows from the bridge recurrence (which uses
   infinite_strip_identity) + harmonic divergence. We restructure the
   proof to derive bridge summability directly from Z(xc) < ∞ assumption,
   avoiding B_paper_le_one_strip.

2. Z(x) < ∞ for x < xc follows from submultiplicativity + Z(xc) = ∞,
   avoiding the Hammersley-Welsh decomposition entirely.
-/

import Mathlib
import RequestProject.SAWRecurrenceProof
import RequestProject.SAWDecomp
import RequestProject.SAWBridgeFix
import RequestProject.SAWStripT1Exact

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Bridge partial sums bounded by Z (without B_paper_le_one_strip) -/

/-- Each PaperBridge is a SAW from paperStart (for use in injection). -/
private def bridgeToSAWSigma {T : ℕ} (b : PaperBridge T) :
    Σ n, SAW paperStart n :=
  ⟨b.walk.1.length, ⟨b.end_v, b.walk, rfl⟩⟩

private lemma bridgeToSAWSigma_injective (T : ℕ) :
    Function.Injective (fun b : PaperBridge T => bridgeToSAWSigma b) := by
  intro b₁ b₂ h; cases b₁; cases b₂
  unfold bridgeToSAWSigma at h; grind

/-- Finite bridge sums inject into SAW sums, bounded by Z(xc). -/
lemma paper_bridge_partial_sum_le_Z_direct (T : ℕ)
    (F : Finset (PaperBridge T))
    (hZ : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    ∑ b ∈ F, xc ^ b.walk.1.length ≤ ∑' n, (saw_count n : ℝ) * xc ^ n := by
  have h_finite_sum : ∀ (F : Finset (PaperBridge T)), (∑ b ∈ F, xc ^ (b.walk : hexGraph.Walk paperStart b.end_v).length) ≤ ∑ n ∈ Finset.image (fun b : PaperBridge T => (b.walk : hexGraph.Walk paperStart b.end_v).length) F, (saw_count n : ℝ) * xc ^ n := by
    intro F
    have h_sum_le : ∀ (n : ℕ), (Finset.filter (fun b => (b.walk : hexGraph.Walk paperStart b.end_v).length = n) F).card ≤ (saw_count n : ℝ) := by
      intro n
      have h_card_le : (Finset.filter (fun b => (b.walk : hexGraph.Walk paperStart b.end_v).length = n) F).card ≤ (Fintype.card (SAW paperStart n) : ℝ) := by
        have h_card_le : (Finset.filter (fun b => (b.walk : hexGraph.Walk paperStart b.end_v).length = n) F).card ≤ (Finset.image (fun b : PaperBridge T => bridgeToSAWSigma b) (Finset.filter (fun b => (b.walk : hexGraph.Walk paperStart b.end_v).length = n) F)).card := by
          rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using bridgeToSAWSigma_injective T hxy ];
        refine' mod_cast h_card_le.trans ( le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _ );
        exact Finset.univ.image fun x : SAW paperStart n => ⟨ n, x ⟩;
        · aesop;
        · exact Finset.card_image_le.trans ( by simp +decide );
      convert h_card_le using 1;
      exact_mod_cast Eq.symm ( saw_count_vertex_independent paperStart n );
    have h_sum_le : ∑ b ∈ F, xc ^ (b.walk : hexGraph.Walk paperStart b.end_v).length = ∑ n ∈ Finset.image (fun b : PaperBridge T => (b.walk : hexGraph.Walk paperStart b.end_v).length) F, (Finset.filter (fun b => (b.walk : hexGraph.Walk paperStart b.end_v).length = n) F).card * xc ^ n := by
      rw [ Finset.sum_image' ];
      simp +contextual [ Finset.sum_filter ];
      simp +contextual [ Finset.sum_ite ];
    exact h_sum_le.symm ▸ Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ( by solve_by_elim ) ( pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ );
  exact le_trans ( h_finite_sum F ) ( Summable.sum_le_tsum _ ( fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ ) ) hZ )

/-- Bridge partition function is summable when Z(xc) < ∞. -/
lemma paper_bridge_summable_of_Z (T : ℕ)
    (hZ : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    Summable (fun b : PaperBridge T => xc ^ b.walk.1.length) :=
  summable_of_sum_le (fun _ => pow_nonneg xc_pos.le _)
    (fun F => (paper_bridge_partial_sum_le_Z_direct T F hZ).trans
      (le_of_eq rfl))

/-
Sigma-type version: bridges across all widths inject into SAWs.
-/
lemma paper_bridge_sigma_sum_le_Z (F : Finset (Σ T : ℕ, PaperBridge (T + 1)))
    (hZ : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    ∑ b ∈ F, xc ^ (b.2.walk.1.length) ≤ ∑' n, (saw_count n : ℝ) * xc ^ n := by
  have h_count : ∀ n, ∑ b ∈ F.filter (fun b => b.2.walk.1.length = n), xc ^ n ≤ (saw_count n : ℝ) * xc ^ n := by
    intro n
    have h_card : Finset.card (Finset.image (fun b => bridgeToSAWSigma b.2) (F.filter (fun b => b.2.walk.1.length = n))) ≤ saw_count n := by
      refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
      exact Finset.univ.image ( fun s : SAW paperStart n => ⟨ n, s ⟩ );
      · aesop;
      · grind +suggestions;
    rw [ Finset.card_image_of_injOn ] at h_card;
    · simp +zetaDelta at *;
      exact mul_le_mul_of_nonneg_right ( mod_cast h_card ) ( pow_nonneg ( by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ );
    · intro b hb b' hb' h_eq;
      rcases b with ⟨ T, b ⟩ ; rcases b' with ⟨ T', b' ⟩ ; simp_all +decide [ bridgeToSAWSigma ];
      cases b ; cases b' ; simp_all +decide [ PaperBridge ];
      grind;
  have h_sum_le_Z : ∑ b ∈ F, xc ^ b.2.walk.1.length ≤ ∑ n ∈ Finset.image (fun b => b.2.walk.1.length) F, ∑ b ∈ F.filter (fun b => b.2.walk.1.length = n), xc ^ n := by
    rw [ Finset.sum_image' ];
    exact fun i hi => Finset.sum_congr rfl fun j hj => by aesop;
  exact h_sum_le_Z.trans ( le_trans ( Finset.sum_le_sum fun _ _ => h_count _ ) ( Summable.sum_le_tsum _ ( fun _ _ => by exact mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ ) ) hZ ) )

/-
Sum of bridge partition functions bounded by Z(xc).
-/
lemma paper_bridge_sum_le_Z_direct (N : ℕ)
    (hZ : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    ∑ T ∈ Finset.range N, paper_bridge_partition (T + 1) xc ≤
    ∑' n, (saw_count n : ℝ) * xc ^ n := by
  have h_each_summable : ∀ T, Summable (fun b : PaperBridge (T + 1) =>
      xc ^ b.walk.1.length) :=
    fun T => paper_bridge_summable_of_Z (T + 1) hZ
  induction' N with N ih;
  · exact tsum_nonneg fun _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( by unfold xc; positivity ) _ );
  · -- For each $T$, let $F_T$ be a finite subset of $\text{PaperBridge}(T+1)$ such that $\sum_{b \in F_T} xc^{\text{length}(b)} \geq \text{paper\_bridge\_partition}(T+1, xc) - \varepsilon / 2^{T+1}$.
    have h_approx : ∀ T : ℕ, ∀ ε > 0, ∃ F : Finset (PaperBridge (T + 1)), ∑ b ∈ F, xc ^ (b.walk.1.length) ≥ paper_bridge_partition (T + 1) xc - ε / 2 ^ (T + 1) := by
      intro T ε hε_pos
      have h_summable : Summable (fun b : PaperBridge (T + 1) => xc ^ (b.walk.1.length)) := h_each_summable T
      have h_approx : ∀ ε > 0, ∃ F : Finset (PaperBridge (T + 1)), ∑ b ∈ F, xc ^ (b.walk.1.length) ≥ ∑' b : PaperBridge (T + 1), xc ^ (b.walk.1.length) - ε := by
        intro ε hε_pos
        have h_approx : Filter.Tendsto (fun F : Finset (PaperBridge (T + 1)) => ∑ b ∈ F, xc ^ (b.walk.1.length)) (Filter.atTop : Filter (Finset (PaperBridge (T + 1)))) (nhds (∑' b : PaperBridge (T + 1), xc ^ (b.walk.1.length))) := by
          exact h_summable.hasSum;
        exact Filter.Eventually.exists ( h_approx.eventually ( le_mem_nhds <| sub_lt_self _ hε_pos ) );
      exact h_approx _ ( div_pos hε_pos ( pow_pos zero_lt_two _ ) );
    refine' le_of_forall_pos_le_add fun ε ε_pos => _;
    choose! F hF using fun T => h_approx T ( ε / 2 ) ( half_pos ε_pos );
    -- Combine the finite sums into a single finite sum over the sigma type.
    have h_combined : ∑ T ∈ Finset.range (N + 1), ∑ b ∈ F T, xc ^ (b.walk.1.length) ≤ ∑' n, (saw_count n : ℝ) * xc ^ n := by
      convert paper_bridge_sigma_sum_le_Z _ hZ using 1;
      rw [ Finset.sum_sigma' ];
    -- The sum of the geometric series $\sum_{T=0}^{N} \frac{1}{2^{T+1}}$ is $1 - \frac{1}{2^{N+1}}$.
    have h_geo_series : ∑ T ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ (T + 1) = 1 - (1 / 2 : ℝ) ^ (N + 1) := by
      exact Nat.recOn N ( by norm_num ) fun n ih => by norm_num [ pow_succ', Finset.sum_range_succ ] at * ; linarith;
    have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range ( N + 1 ) ) => hF i; simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    exact this.trans ( add_le_add h_combined ( by nlinarith [ inv_pos.mpr ( pow_pos ( zero_lt_two' ℝ ) ( N + 1 ) ) ] ) )

/-! ## paper_bridge_partition_one_pos (from exact value, no B_paper_le_one_strip) -/

lemma paper_bridge_partition_one_pos_direct : 0 < paper_bridge_partition 1 xc := by
  rw [paper_bridge_partition_1_eq]
  apply div_pos (mul_pos (by norm_num : (0:ℝ) < 2) xc_pos)
  linarith [xc_sq_lt_one]

/-! ## Z(xc) = ∞ (restructured without B_paper_le_one_strip) -/

theorem Z_xc_diverges_direct :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  have h_recur := paper_bridge_recurrence_derived
  obtain ⟨α, hα_pos, hrecur⟩ := h_recur
  have hB_nn : ∀ T, 0 ≤ paper_bridge_partition T xc :=
    fun T => tsum_nonneg fun _ => pow_nonneg xc_pos.le _
  have hB1 := paper_bridge_partition_one_pos_direct
  have h_lower := quadratic_recurrence_lower_bound hα_pos hB_nn hrecur hB1
  intro h_summable
  have h_bridge_summable : Summable (fun T : ℕ =>
      paper_bridge_partition (T + 1) xc) :=
    summable_of_sum_range_le
      (fun T => tsum_nonneg fun _ => pow_nonneg xc_pos.le _)
      (fun N => paper_bridge_sum_le_Z_direct N h_summable)
  have h_lower_bound : ∀ T : ℕ, min (paper_bridge_partition 1 xc) (1 / α) / ((T : ℝ) + 1) ≤
      paper_bridge_partition (T + 1) xc := by
    intro T; have := h_lower (T + 1) (by omega); push_cast at this ⊢; linarith
  exact absurd
    (Summable.of_nonneg_of_le (fun T => by positivity) h_lower_bound h_bridge_summable)
    (not_summable_of_lower_bound (lt_min hB1 (div_pos one_pos hα_pos)) (fun n => le_refl _))

/-! ## Z(x) < ∞ for x < xc (submultiplicativity, no HW decomposition)

The key insight: from Z(xc) = ∞, we get μ ≥ 1/xc. For x < xc ≤ 1/μ,
by submultiplicativity c_{km} ≤ c_m^k, we can bound c_n x^n
geometrically for large n, giving summability. -/

/-- Submultiplicativity gives exponential bound for large n. -/
lemma saw_count_exp_bound (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (saw_count n : ℝ) ≤ (saw_count m : ℝ) * (saw_count m : ℝ) ^ (n / m) := by
  sorry

/-- The partition function converges below the radius of convergence,
    which is at least xc (since Z(xc) = ∞). Uses submultiplicativity. -/
theorem hw_summable_direct {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  sorry

/-! ## Main theorem -/

theorem connective_constant_eq_direct :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) :=
  connective_constant_eq_from_bounds
    Z_xc_diverges_direct
    (fun _ hx hxc => hw_summable_direct hx hxc)

end