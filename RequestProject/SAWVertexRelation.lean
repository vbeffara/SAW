/-
# Iterated submultiplicativity bounds

From c_{n+m} ≤ c_n · c_m (proved in SAWSubmult.lean), derives:
- c(k·m) ≤ c(m)^k
- c(n) ≤ M · c(m)^⌊n/m⌋  where M = max(c(0),...,c(m-1))
- Summability of Z(x) when c(m) · x^m < 1 for some m
-/

import Mathlib
import RequestProject.SAWSubmult

open Real Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-
Submultiplicativity iterated: c(k·m) ≤ c(m)^k.
-/
lemma saw_count_mul_le_pow (m k : ℕ) :
    (saw_count (k * m) : ℝ) ≤ (saw_count m : ℝ) ^ k := by
  induction' k with k ih;
  · simp +zetaDelta at *;
    refine' Fintype.card_le_one_iff.mpr _;
    rintro ⟨ w₁, ⟨ p₁, hp₁ ⟩, hl₁ ⟩ ⟨ w₂, ⟨ p₂, hp₂ ⟩, hl₂ ⟩;
    cases p₁ <;> cases p₂ <;> aesop;
  · -- By the submultiplicative property, we have c((k + 1) * m) ≤ c(k * m) * c(m).
    have h_submul : (saw_count ((k + 1) * m) : ℝ) ≤ (saw_count (k * m) : ℝ) * (saw_count m : ℝ) := by
      norm_cast;
      convert saw_count_submult' ( k * m ) m using 1 ; ring;
    exact h_submul.trans ( mul_le_mul_of_nonneg_right ih <| Nat.cast_nonneg _ ) |> le_trans <| by ring_nf; norm_num;

/-- The maximum of c(0), ..., c(m-1). -/
noncomputable def saw_count_max (m : ℕ) : ℕ :=
  (Finset.range m).sup saw_count

/-- Each c(r) for r < m is bounded by saw_count_max m. -/
lemma saw_count_le_max (m r : ℕ) (hr : r < m) :
    saw_count r ≤ saw_count_max m :=
  Finset.le_sup (f := saw_count) (Finset.mem_range.mpr hr)

/-- saw_count_max is positive for m ≥ 1. -/
lemma saw_count_max_pos (m : ℕ) (hm : 0 < m) : 0 < saw_count_max m := by
  calc 0 < saw_count 0 := saw_count_pos 0
    _ ≤ saw_count_max m := saw_count_le_max m 0 hm

/-
General submultiplicativity bound: c(n) ≤ saw_count_max(m) · c(m)^⌊n/m⌋.
-/
lemma saw_count_submult_bound (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (saw_count n : ℝ) ≤ (saw_count_max m : ℝ) * (saw_count m : ℝ) ^ (n / m) := by
  -- Write n = (n/m)*m + (n%m) using Nat.div_add_mod. Then c(n) ≤ c((n/m)*m) * c(n%m) by saw_count_submult'.
  have h1 : (saw_count n : ℝ) ≤ (saw_count ((n / m) * m) : ℝ) * (saw_count (n % m) : ℝ) := by
    exact_mod_cast by simpa only [ Nat.div_add_mod' ] using saw_count_submult' ( n / m * m ) ( n % m ) ;
  refine le_trans h1 ?_;
  rw [ mul_comm ];
  gcongr;
  · exact saw_count_le_max m _ ( Nat.mod_lt _ hm );
  · exact_mod_cast saw_count_mul_le_pow m ( n / m )

/-
Summability of c(n) x^n when c(m) · x^m < 1 for some m.
-/
theorem partition_summable_of_small_root {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : 0 < m)
    (hρ : (saw_count m : ℝ) * x ^ m < 1) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  have h_series_conv : Summable (fun n : ℕ => (saw_count_max m : ℝ) * (saw_count m : ℝ) ^ (n / m) * x^n) := by
    -- We can factor out `saw_count_max m` from the sum.
    suffices h_factor : Summable (fun n : ℕ => ((saw_count m : ℝ) * x ^ m) ^ (n / m) * x ^ (n % m)) by
      convert h_factor.mul_left ( saw_count_max m : ℝ ) using 2 ; ring;
      simp +decide [ mul_assoc, ← pow_add, Nat.div_add_mod' ];
    -- We can bound the series by considering the geometric series $\sum_{n=0}^{\infty} \rho^{n/m}$ where $\rho = c(m) \cdot x^m$. Since $\rho < 1$, this series converges.
    have h_geo_series : Summable (fun n : ℕ => ((saw_count m : ℝ) * x ^ m) ^ (n / m)) := by
      have h_pseries : Summable (fun n => ((saw_count m : ℝ) * x ^ m) ^ n) := by
        exact summable_geometric_of_lt_one ( by positivity ) hρ;
      have h_pseries : ∀ k : ℕ, ∑ n ∈ Finset.range (m * (k + 1)), ((saw_count m : ℝ) * x ^ m) ^ (n / m) ≤ m * ∑ n ∈ Finset.range (k + 1), ((saw_count m : ℝ) * x ^ m) ^ n := by
        intro k
        have h_split : ∑ n ∈ Finset.range (m * (k + 1)), ((saw_count m : ℝ) * x ^ m) ^ (n / m) = ∑ i ∈ Finset.range (k + 1), ∑ n ∈ Finset.range m, ((saw_count m : ℝ) * x ^ m) ^ i := by
          induction' k + 1 with k ih <;> simp_all +decide [ Nat.mul_succ, Finset.sum_range_add ];
          norm_num [ Nat.add_div, hm ];
          rw [ Finset.sum_congr rfl fun i hi => by rw [ Nat.div_eq_of_lt ( Finset.mem_range.mp hi ), if_neg ( Nat.not_le_of_gt ( Nat.mod_lt _ hm ) ) ] ] ; norm_num;
        simp_all +decide [ Finset.mul_sum _ _ _ ];
      rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
      · rw [ Filter.tendsto_atTop_atTop ];
        push_neg;
        exact ⟨ m * ∑' n : ℕ, ( saw_count m * x ^ m ) ^ n + 1, fun n => ⟨ m * ( n + 1 ), by nlinarith, lt_of_le_of_lt ( h_pseries n ) ( by nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast, show ( ∑ n ∈ Finset.range ( n + 1 ), ( saw_count m * x ^ m ) ^ n ) ≤ ∑' n : ℕ, ( saw_count m * x ^ m ) ^ n by exact Summable.sum_le_tsum ( Finset.range ( n + 1 ) ) ( fun _ _ => by positivity ) ( by assumption ) ] ) ⟩ ⟩;
      · exact fun n => pow_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) _;
    refine' .of_nonneg_of_le ( fun n => mul_nonneg ( pow_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) _ ) ( pow_nonneg hx.le _ ) ) ( fun n => mul_le_mul_of_nonneg_left ( show x ^ ( n % m ) ≤ x ^ 0 + ∑ k ∈ Finset.range m, x ^ k from _ ) ( pow_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) _ ) ) ( h_geo_series.mul_right _ );
    exact le_add_of_nonneg_of_le ( pow_nonneg hx.le _ ) ( Finset.single_le_sum ( fun k _ => pow_nonneg hx.le k ) ( Finset.mem_range.mpr ( Nat.mod_lt _ hm ) ) );
  refine' h_series_conv.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) ( fun n => _ );
  exact mul_le_mul_of_nonneg_right ( mod_cast saw_count_submult_bound m hm n ) ( pow_nonneg hx.le _ )

end