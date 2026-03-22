/-
# Elementary bounds on self-avoiding walks

This file formalizes the elementary bounds on the number of self-avoiding walks
c_n on the hexagonal lattice, from the introduction of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. **Elementary lower bound**: c_n ≥ 1 for all n
2. **Logarithmic submultiplicativity**: log(c_{n+m}) ≤ log(c_n) + log(c_m)
3. **Properties of c_α, c_ε, x_c, and the recurrence constant α = c_α · x_c**
4. **x_c properties**: x_c < 1, x_c² = 1/(2+√2), x_c⁻¹ > 1

## Mathematical context

From the paper (Section 1):
"Elementary bounds on c_n (for instance √2^n ≤ c_n ≤ 3·2^{n-1}) guarantee
that c_n grows exponentially fast."

The submultiplicativity c_{n+m} ≤ c_n · c_m gives, by Fekete's lemma, that
the limit μ = lim c_n^{1/n} exists, and equals inf_{n≥1} c_n^{1/n}.
-/

import RequestProject.SAWSubmult

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Elementary properties of SAW counts -/

/-- The SAW count is at least 1 for all n: there always exists at least
    one n-step SAW from any vertex. -/
lemma saw_count_ge_one (n : ℕ) : 1 ≤ saw_count n :=
  Nat.one_le_iff_ne_zero.mpr (ne_of_gt (saw_count_pos n))

/-- Submultiplicativity in its logarithmic form:
    log(c_{n+m}) ≤ log(c_n) + log(c_m). -/
lemma log_saw_count_submult (n m : ℕ) :
    Real.log (saw_count (n + m)) ≤ Real.log (saw_count n) + Real.log (saw_count m) := by
  rw [← Real.log_mul (by exact_mod_cast (saw_count_pos n).ne')
                       (by exact_mod_cast (saw_count_pos m).ne')]
  exact Real.log_le_log (by exact Nat.cast_pos.mpr (saw_count_pos _)) (by exact_mod_cast saw_count_submult' n m)

/-! ## The connective constant bounds -/

/-- The connective constant is at least 1 (since c_n ≥ 1 for all n). -/
lemma connective_constant_ge_one' : 1 ≤ connective_constant := by
  refine le_csInf ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)⟩ ?_
  rintro x ⟨n, hn, rfl⟩
  exact Real.one_le_rpow (mod_cast saw_count_ge_one n) (by positivity)

/-! ## Properties of c_α and c_ε from the strip identity

The coefficients in the strip identity (Lemma 2) satisfy:
  0 < c_α < 1  and  0 < c_ε < 1

These bounds are important for the iteration argument.
-/

/-- c_α = cos(3π/8) < 1. -/
lemma c_alpha_lt_one : c_alpha < 1 := by
  unfold c_alpha
  rw [show (1 : ℝ) = Real.cos 0 from Real.cos_zero.symm]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by positivity)
    (by linarith [Real.pi_pos]) (by positivity)

/-- c_ε = cos(π/4) < 1. -/
lemma c_eps_lt_one : c_eps < 1 := by
  unfold c_eps
  rw [show (1 : ℝ) = Real.cos 0 from Real.cos_zero.symm]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by positivity)
    (by linarith [Real.pi_pos]) (by positivity)

/-! ## The recurrence constant α = c_α · x_c -/

/-- The recurrence constant α = c_α · x_c is positive. -/
lemma alpha_pos : 0 < c_alpha * xc := mul_pos c_alpha_pos xc_pos

/-- x_c < 1, since √(2+√2) > 1. -/
lemma xc_lt_one : xc < 1 := by
  unfold xc
  rw [div_lt_one (Real.sqrt_pos.mpr two_add_sqrt_two_pos)]
  calc (1 : ℝ) < Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ ≤ Real.sqrt (2 + Real.sqrt 2) :=
        Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg 2])

/-- The recurrence constant α = c_α · x_c satisfies α < 1. -/
lemma alpha_lt_one : c_alpha * xc < 1 := by
  calc c_alpha * xc ≤ c_alpha * 1 := by
        exact mul_le_mul_of_nonneg_left xc_lt_one.le c_alpha_pos.le
    _ = c_alpha := mul_one _
    _ < 1 := c_alpha_lt_one

/-! ## x_c properties -/

/-- x_c² = 1/(2+√2). -/
lemma xc_sq : xc ^ 2 = 1 / (2 + Real.sqrt 2) := by
  unfold xc
  rw [div_pow, one_pow, sq_sqrt two_add_sqrt_two_pos.le]

/-- x_c⁻¹ > 1, since the connective constant is greater than 1. -/
lemma xc_inv_gt_one : 1 < xc⁻¹ := by
  rw [xc_inv]
  calc (1 : ℝ) < Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ ≤ Real.sqrt (2 + Real.sqrt 2) :=
        Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg 2])

/-! ## Summary of elementary bounds

From the introduction of the paper:

1. **Submultiplicativity**: c_{n+m} ≤ c_n · c_m (proved in SAWSubmult.lean)
2. **Existence of μ**: lim c_n^{1/n} = μ exists (proved in SAWMain.lean via Fekete)
3. **Lower bound**: c_n ≥ μ^n (proved in SAWBridge.lean)
4. **Constants**: c_α = cos(3π/8) ∈ (0,1), c_ε = cos(π/4) ∈ (0,1)
5. **Critical fugacity**: x_c = 1/√(2+√2) ∈ (0,1)
6. **Recurrence constant**: α = c_α · x_c ∈ (0,1)
-/

end
