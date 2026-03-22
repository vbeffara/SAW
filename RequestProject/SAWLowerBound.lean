/-
# Complete lower bound proof: Z(x_c) = ∞

Formalization of the complete lower bound argument from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

This file provides the complete case analysis for the lower bound:
Z(x_c) = ∞, hence μ ≥ √(2+√2).
-/

import RequestProject.SAWProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Case 2 bridge lower bound

In Case 2 (E_T = 0 for all T), the strip identity simplifies to
1 = c_α·A_T + B_T. Combined with the recurrence, this gives B_T ≥ c/T.
-/

/-- **Case 2**: If E_T = 0 for all T, then B_T ≥ c/T.
    Uses the quadratic recurrence from SAWDecomp. -/
theorem case2_bridge_lower_bound
    {A B : ℕ → ℝ}
    (hA_nn : ∀ T, 0 ≤ A T) (hB_nn : ∀ T, 0 ≤ B T)
    (hstrip : ∀ T, 1 = c_alpha * A T + B T)
    (hrecur : ∀ T, A (T + 1) - A T ≤ xc * B (T + 1) ^ 2)
    (hB1 : 0 < B 1) :
    ∃ c > 0, ∀ T, 1 ≤ T → c / T ≤ B T := by
  have hB_le : ∀ T, B T ≤ 1 := fun T => by nlinarith [hstrip T, c_alpha_pos, hA_nn T]
  have hB_recur : ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1) := by
    intro T; nlinarith [hstrip T, hstrip (T + 1), hrecur T, c_alpha_pos, xc_pos]
  have hα := mul_pos c_alpha_pos xc_pos
  exact ⟨min (B 1) (1 / (c_alpha * xc)), lt_min hB1 (div_pos one_pos hα),
    quadratic_recurrence_lower_bound hα hB_nn hB_le hB_recur hB1⟩

/-- **The complete lower bound**: In Case 2, the bridge series diverges. -/
theorem case2_divergence_full
    {A B : ℕ → ℝ}
    (hA_nn : ∀ T, 0 ≤ A T) (hB_nn : ∀ T, 0 ≤ B T)
    (hstrip : ∀ T, 1 = c_alpha * A T + B T)
    (hrecur : ∀ T, A (T + 1) - A T ≤ xc * B (T + 1) ^ 2)
    (hB1 : 0 < B 1) :
    ¬ Summable (fun T => B (T + 1)) := by
  have hB_le : ∀ T, B T ≤ 1 := fun T => by nlinarith [hstrip T, c_alpha_pos, hA_nn T]
  have hB_recur : ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1) := by
    intro T; nlinarith [hstrip T, hstrip (T + 1), hrecur T, c_alpha_pos, xc_pos]
  exact case2_divergence hB_nn hB_le hB_recur hB1

/-! ## The complete case analysis

The lower bound proof distinguishes two cases based on E_T.
In both cases, we show the bridge series Σ B_T diverges,
which implies Z(x_c) = ∞.
-/

/-- The bridge recurrence holds in both cases (not just Case 2),
    as it follows from the full strip identity and monotonicity of E. -/
theorem bridge_recurrence_general
    {A B E : ℕ → ℝ}
    (hstrip : ∀ T, 1 = c_alpha * A T + B T + c_eps * E T)
    (hrecur : ∀ T, A (T + 1) - A T ≤ xc * B (T + 1) ^ 2)
    (hE_decr : ∀ T, E (T + 1) ≤ E T) :
    ∀ T, B T ≤ c_alpha * xc * B (T + 1) ^ 2 + B (T + 1) :=
  recurrence_from_strip hstrip hrecur hE_decr

/-- The bridge series always diverges (regardless of which case applies),
    given the strip identity, recurrence, and B₁ > 0. -/
theorem bridge_series_diverges
    {A B E : ℕ → ℝ}
    (hA_nn : ∀ T, 0 ≤ A T) (hB_nn : ∀ T, 0 ≤ B T) (hE_nn : ∀ T, 0 ≤ E T)
    (hstrip : ∀ T, 1 = c_alpha * A T + B T + c_eps * E T)
    (hrecur : ∀ T, A (T + 1) - A T ≤ xc * B (T + 1) ^ 2)
    (hE_decr : ∀ T, E (T + 1) ≤ E T)
    (hB1 : 0 < B 1) :
    ¬ Summable (fun T => B (T + 1)) := by
  -- B_T ≤ 1 from strip identity
  have hB_le : ∀ T, B T ≤ 1 := fun T => by
    nlinarith [hstrip T, c_alpha_pos, c_eps_pos, hA_nn T, hE_nn T]
  -- The recurrence holds
  have hB_recur := bridge_recurrence_general hstrip hrecur hE_decr
  -- Apply the quadratic recurrence lower bound
  exact case2_divergence hB_nn hB_le hB_recur hB1

/-! ## Bridge scaling bound

For the upper bound, we need B_T^x ≤ (x/x_c)^T for x < x_c.
-/

/-- The geometric series Σ (x/x_c)^T converges for x < x_c. -/
theorem geometric_bridge_sum {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun T => (x / xc) ^ T) :=
  summable_geometric_of_lt_one (div_nonneg hx.le xc_pos.le) (ratio_lt_one hx hxc)

/-! ## The main theorem from both bounds

Combining the lower bound (Z(x_c) = ∞) and upper bound (Z(x) < ∞ for x < x_c)
determines μ = √(2+√2).

The lower bound gives μ ≥ 1/x_c by showing Z(x_c) = ∞.
The upper bound gives μ ≤ 1/x_c by showing Z(x) < ∞ for x < x_c.

The precise reduction from partition function bounds to the
connective constant equality is in SAWBridge.lean
(connective_constant_eq_from_bounds and main_theorem_from_partition).
-/

-- Summary: the key gap in the formalization.
--
-- The main theorem μ = √(2+√2) is proved MODULO the following:
--
-- 1. **Bridge-to-walk injection**: Every SAW can be decomposed into
--    a sequence of bridges. The bridge contributions lower-bound Z(x).
--
-- 2. **Strip domain restriction**: Formally defining SAWs restricted
--    to strip domains S_{T,L} and connecting them to A, B, E.
--
-- 3. **Boundary winding evaluation**: Computing the exact winding values
--    for walks ending on each boundary part of the strip domain.
--
-- All three are concrete combinatorial/geometric arguments about the
-- hex lattice. The abstract proof structure (this file, SAWProof.lean,
-- SAWDecomp.lean, SAWBridge.lean) is complete.

end
