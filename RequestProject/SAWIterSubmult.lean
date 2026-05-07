/-
# Iterated submultiplicativity and exponential bounds

From the submultiplicativity c_{n+m} ≤ c_n · c_m, we derive:
- c_{km} ≤ c_m^k (iterated submultiplicativity)
- c_{qm+r} ≤ c_m^q · c_r (with remainder)
- Summability of Z(x) for x < xc via geometric comparison
-/

import Mathlib
import RequestProject.SAWSubmult
import RequestProject.SAWMain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Iterated submultiplicativity -/

/-
c_{km} ≤ c_m^k by iterated submultiplicativity.
-/
theorem saw_count_iter_submult (m k : ℕ) :
    (saw_count (k * m) : ℝ) ≤ (saw_count m : ℝ) ^ k := by
  induction' k with k ih;
  · unfold saw_count; norm_num;
    rw [ Fintype.card_le_one_iff ];
    rintro ⟨ a, ⟨ p, hp ⟩, l ⟩ ⟨ b, ⟨ q, hq ⟩, l' ⟩ ; cases p ; cases q ; aesop;
    · cases l';
    · cases l;
  · rw [ Nat.succ_mul, pow_succ' ];
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ih _ );
    · exact_mod_cast by rw [ add_comm ] ; exact saw_count_submult' _ _;
    · positivity

/-
c_{qm+r} ≤ c_m^q · c_r by iterated submultiplicativity with remainder.
-/
theorem saw_count_submult_with_remainder (m q r : ℕ) :
    (saw_count (q * m + r) : ℝ) ≤ (saw_count m : ℝ) ^ q * (saw_count r : ℝ) := by
  exact_mod_cast saw_count_submult' ( q * m ) r |> le_trans <| Nat.mul_le_mul_right _ <| mod_cast saw_count_iter_submult m q

/-
Upper bound on c_n using any fixed m: c_n ≤ c_m^{⌊n/m⌋} · c_{n%m}.
-/
theorem saw_count_div_mod_bound (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (saw_count n : ℝ) ≤ (saw_count m : ℝ) ^ (n / m) * (saw_count (n % m) : ℝ) := by
  have := @saw_count_submult_with_remainder m ( n / m ) ( n % m ) ; simp_all +decide [ Nat.div_add_mod ] ;
  rwa [ Nat.div_add_mod' ] at this

/-! ## Summability from iterated submultiplicativity -/

/-
If c_m · x^m < 1, then Z(x) = Σ c_n x^n < ∞.
-/
theorem partition_summable_of_geometric {x : ℝ} (hx : 0 < x) (m : ℕ) (hm : 0 < m)
    (hrho : (saw_count m : ℝ) * x ^ m < 1) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  -- Let $c = \max_{0 \leq r < m} c_r x^r$.
  set c := sSup (Set.image (fun r => (saw_count r : ℝ) * x ^ r) (Finset.range m)) with hc_def;
  -- Then $c_n x^n \leq c \cdot \rho^{n/m}$ for all $n$.
  have h_bound : ∀ n, (saw_count n : ℝ) * x ^ n ≤ c * ((saw_count m : ℝ) * x ^ m) ^ (n / m : ℕ) := by
    intro n
    have h_bound_step : (saw_count n : ℝ) * x ^ n ≤ (saw_count (n % m) : ℝ) * x ^ (n % m) * ((saw_count m : ℝ) * x ^ m) ^ (n / m : ℕ) := by
      have h_bound_step : (saw_count n : ℝ) ≤ (saw_count (n % m) : ℝ) * (saw_count m : ℝ) ^ (n / m : ℕ) := by
        convert saw_count_div_mod_bound m hm n using 1;
        ring;
      convert mul_le_mul_of_nonneg_right h_bound_step ( pow_nonneg hx.le n ) using 1 ; ring;
      rw [ show x ^ n = x ^ ( n % m ) * x ^ ( m * ( n / m ) ) by rw [ ← pow_add, Nat.mod_add_div ] ] ; ring;
    exact h_bound_step.trans ( mul_le_mul_of_nonneg_right ( le_csSup ( by exact Set.Finite.bddAbove <| Set.toFinite _ ) <| Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_range.mpr <| Nat.mod_lt _ hm ) <| by positivity );
  refine' Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) ( fun n => h_bound n ) _;
  have h_geo_series : Summable (fun n : ℕ => ((saw_count m : ℝ) * x ^ m) ^ (n / m)) := by
    have h_series : ∀ N : ℕ, ∑ n ∈ Finset.range (N * m), ((saw_count m : ℝ) * x ^ m) ^ (n / m) ≤ m * ∑ q ∈ Finset.range N, ((saw_count m : ℝ) * x ^ m) ^ q := by
      intro N; induction' N with N ih <;> simp_all +decide [ Nat.succ_mul, Finset.sum_range_add ] ;
      norm_num [ Nat.add_div, hm ];
      refine le_trans ( add_le_add ih ( Finset.sum_le_sum fun i hi => show ( ( saw_count m : ℝ ) * x ^ m ) ^ ( N + i / m + if m ≤ i % m then 1 else 0 ) ≤ ( ( saw_count m : ℝ ) * x ^ m ) ^ N from ?_ ) ) ?_;
      · exact pow_le_pow_of_le_one ( by positivity ) hrho.le ( by split_ifs <;> linarith [ Nat.div_eq_of_lt ( Finset.mem_range.mp hi ), Nat.mod_lt i hm ] );
      · norm_num [ mul_add ]
    rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
    · rw [ Filter.tendsto_atTop_atTop ];
      push_neg;
      exact ⟨ m * ∑' q : ℕ, ( saw_count m * x ^ m ) ^ q + 1, fun N => ⟨ N * m, by nlinarith, lt_of_le_of_lt ( h_series N ) ( by nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast, show ( ∑ q ∈ Finset.range N, ( saw_count m * x ^ m ) ^ q ) ≤ ∑' q : ℕ, ( saw_count m * x ^ m ) ^ q by exact Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => by positivity ) ( by exact summable_geometric_of_lt_one ( by positivity ) hrho ) ] ) ⟩ ⟩;
    · exact fun n => pow_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) _;
  exact h_geo_series.mul_left c

end