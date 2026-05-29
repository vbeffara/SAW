/-
# GF bound for extra walks and the inductive step

Imports SAWHWConvBound to get extra_count_le_conv', then proves
the generating function bound for extra walks, hp_sum_step, and hp_sum_le_prod.
-/

import Mathlib
import RequestProject.SAWHWStepHelpers
import RequestProject.SAWHWConvBound
import RequestProject.SAWHWBridgeShift

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 8000000

/-! ## Bridge count any GF bound -/

/-- bridge_count_any ≤ bridge_count + bridge_count at shifted index. -/
lemma bridge_count_any_le_shifted (T k : ℕ) (hT : 1 ≤ T) :
    bridge_count_any T k ≤ bridge_count T k + bridge_count T (k - 1) :=
  bridge_count_any_le_shifted' T k hT

/-
The GF of bridge_count_any is ≤ (1+x) · paper_bridge_partition.
-/
lemma bridge_count_any_gf_le (T : ℕ) (hT : 1 ≤ T) (N : ℕ) (x : ℝ)
    (hx : 0 < x) (hxc : x ≤ xc) :
    ∑ k ∈ Finset.range (N + 1), (bridge_count_any T k : ℝ) * x ^ k ≤
    (1 + x) * paper_bridge_partition T x := by
  -- By bridge_count_any_le_shifted, we have bridge_count_any T k ≤ bridge_count T k + bridge_count T (k - 1).
  have h_le : ∀ k, (bridge_count_any T k : ℝ) ≤ (bridge_count T k : ℝ) + (bridge_count T (k - 1) : ℝ) := by
    exact fun k => mod_cast bridge_count_any_le_shifted T k hT;
  -- By bridge_gf_le_partition, we have that the sum of bridge_count T k * x^k is less than or equal to paper_bridge_partition T x.
  have h_sum_le : ∑ k ∈ Finset.range (N + 1), (bridge_count T k : ℝ) * x ^ k ≤ paper_bridge_partition T x := by
    convert bridge_gf_le_partition T hT N x hx hxc using 1;
  refine le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( h_le i ) ( pow_nonneg hx.le _ ) ) ?_;
  -- The sum of bridge_count T (k - 1) * x^k can be rewritten as x times the sum of bridge_count T j * x^j for j from 0 to N-1.
  have h_sum_shift : ∑ k ∈ Finset.range (N + 1), (bridge_count T (k - 1) : ℝ) * x ^ k = x * ∑ j ∈ Finset.range N, (bridge_count T j : ℝ) * x ^ j := by
    norm_num [ Finset.sum_range_succ', pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    unfold bridge_count; simp +decide [ hT ] ;
    rintro ⟨ w, p, hp ⟩ hw₁ hw₂; rcases p with ⟨ _ | ⟨ a, b ⟩ ⟩ <;> norm_num at *;
    · cases hw₂;
    · cases hp;
  simp_all +decide [ add_mul, Finset.sum_add_distrib ];
  exact add_le_add h_sum_le ( mul_le_mul_of_nonneg_left ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.le_succ _ ) ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) h_sum_le ) hx.le )

/-! ## The main extra sum bound -/

/-- The key generating function bound for extra walks.
    Uses bridge_count_any GF ≤ (1+x) · paper_bridge_partition and
    narrow_suffix GF ≤ 6 · hp_sum, giving constant 12 (since (1+x) ≤ 2). -/
private lemma extra_sum_le (W N : ℕ) (x : ℝ) (hx : 0 < x) (hxc : x < xc) :
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    12 * paper_bridge_partition (W + 1) x * hp_sum W N x := by
  have hx1 : x < 1 := lt_trans hxc xc_lt_one
  -- Step 1: extra_count ≤ convolution of bridge_count_any and narrow_suffix_count
  have h_conv : ∀ n ∈ Finset.range (N + 1),
      (extra_count W n : ℝ) * x ^ n ≤
      (∑ k ∈ Finset.range (n + 1),
        (bridge_count_any (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ)) * x ^ n := by
    intro n _
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx.le _)
    exact extra_count_le_conv' W n
  -- Step 2: Apply Cauchy product
  have h_cauchy :
      ∑ n ∈ Finset.range (N + 1),
        (∑ k ∈ Finset.range (n + 1),
          (bridge_count_any (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ)) * x ^ n ≤
      (∑ k ∈ Finset.range (N + 1), (bridge_count_any (W + 1) k : ℝ) * x ^ k) *
      (∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s) :=
    cauchy_product_le' (fun k => (bridge_count_any (W + 1) k : ℝ))
      (fun s => (narrow_suffix_count W s : ℝ))
      (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) x hx.le N
  -- Step 3: Bound bridge_count_any GF by (1+x) · paper_bridge_partition
  have h_bridge : ∑ k ∈ Finset.range (N + 1), (bridge_count_any (W + 1) k : ℝ) * x ^ k ≤
      (1 + x) * paper_bridge_partition (W + 1) x :=
    bridge_count_any_gf_le (W + 1) (by omega) N x hx hxc.le
  -- Step 4: Bound narrow suffix GF
  have h_suffix : ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s ≤
      6 * hp_sum W N x :=
    narrow_suffix_gf_le' W N x hx hx1
  -- Step 5: Combine using (1+x) · 6 ≤ 12 for x < 1
  have h_bridge_nn : 0 ≤ paper_bridge_partition (W + 1) x :=
    tsum_nonneg fun _ => pow_nonneg hx.le _
  have h_suffix_nn : 0 ≤ ∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le _)
  have h_hp_nn : 0 ≤ hp_sum W N x := hp_sum_nonneg W N x hx.le
  calc ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n
      ≤ ∑ n ∈ Finset.range (N + 1),
          (∑ k ∈ Finset.range (n + 1),
            (bridge_count_any (W + 1) k : ℝ) * (narrow_suffix_count W (n - k) : ℝ)) * x ^ n :=
        Finset.sum_le_sum h_conv
    _ ≤ (∑ k ∈ Finset.range (N + 1), (bridge_count_any (W + 1) k : ℝ) * x ^ k) *
        (∑ s ∈ Finset.range (N + 1), (narrow_suffix_count W s : ℝ) * x ^ s) := h_cauchy
    _ ≤ ((1 + x) * paper_bridge_partition (W + 1) x) *
        (6 * hp_sum W N x) := by
        exact mul_le_mul h_bridge h_suffix h_suffix_nn (by nlinarith)
    _ ≤ (2 * paper_bridge_partition (W + 1) x) *
        (6 * hp_sum W N x) := by
        have h1x : 1 + x ≤ 2 := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1x h_bridge_nn) (by nlinarith)
    _ = 12 * paper_bridge_partition (W + 1) x * hp_sum W N x := by ring

/-- **Key inductive step** (with constant 12):
    hp_sum(W+1) ≤ (1 + 12 · B_{W+1}) · hp_sum(W). -/
lemma hp_sum_step' {x : ℝ} (hx : 0 < x) (hxc : x < xc) (W N : ℕ) :
    hp_sum (W + 1) N x ≤
    (1 + 12 * paper_bridge_partition (W + 1) x) * hp_sum W N x := by
  rw [hp_sum_split]
  have h1 := extra_sum_le W N x hx hxc
  have h2 := hp_sum_nonneg W N x hx.le
  nlinarith

/-! ## The inductive bound (product form) -/

/-- Half-plane walk bound:
    hp_sum(W) ≤ 2 · ∏_{T=1}^W (1 + 12·B_T(x)). -/
theorem hp_sum_le_prod' {x : ℝ} (hx : 0 < x) (hxc : x < xc) (W N : ℕ) :
    hp_sum W N x ≤
    2 * ∏ T ∈ Finset.range W, (1 + 12 * paper_bridge_partition (T + 1) x) := by
  induction W with
  | zero =>
    simp
    have hx1 : x < 1 := lt_trans hxc xc_lt_one
    linarith [hp_sum_zero_le N x hx.le hx1.le]
  | succ W ih =>
    rw [Finset.prod_range_succ]
    have hB_nn : 0 ≤ paper_bridge_partition (W + 1) x :=
      tsum_nonneg fun _ => pow_nonneg hx.le _
    have hF : 0 ≤ 1 + 12 * paper_bridge_partition (W + 1) x := by linarith
    have hstep := hp_sum_step' hx hxc W N
    have h1 : hp_sum (W + 1) N x ≤ (1 + 12 * paper_bridge_partition (W + 1) x) *
        (2 * ∏ T ∈ Finset.range W, (1 + 12 * paper_bridge_partition (T + 1) x)) :=
      le_trans hstep (mul_le_mul_of_nonneg_left ih hF)
    linarith [mul_comm (∏ T ∈ Finset.range W, (1 + 12 * paper_bridge_partition (T + 1) x))
      (1 + 12 * paper_bridge_partition (W + 1) x)]

end