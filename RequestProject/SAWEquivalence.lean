/-
# Equivalence between the main theorem and partition function bounds

This file formalizes the key equivalence from Section 1 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

The paper states:
"Establishing the identity μ = √(2+√2) is equivalent to showing that
Z(x) = +∞ for x > 1/√(2+√2) and Z(x) < +∞ for x < 1/√(2+√2)."

This file proves this equivalence precisely:

1. **Forward**: If μ = √(2+√2), then Z diverges above x_c and converges below.
2. **Backward**: If Z diverges above x_c and converges below, then μ = √(2+√2).

We also formalize the connection to the radius of convergence of the
generating function Z(x) = Σ c_n x^n.
-/

import RequestProject.SAWBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The partition function characterization

The generating function Z(x) = Σ c_n · x^n has radius of convergence 1/μ.
The main theorem μ = √(2+√2) is equivalent to: the radius of convergence
of Z(x) is exactly x_c = 1/√(2+√2).
-/

/-- The main theorem is equivalent to showing the radius of convergence is x_c.
    Direction 1: Divergence at x_c + convergence below x_c → μ = √(2+√2). -/
theorem main_thm_from_partition_bounds
    (hdiv : ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n))
    (hconv : ∀ x, 0 < x → x < xc → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) :=
  connective_constant_eq_from_bounds hdiv hconv

/-- Direction 2: If μ = √(2+√2), the partition function diverges above x_c. -/
theorem partition_diverges_of_main_thm
    (hmain : connective_constant = Real.sqrt (2 + Real.sqrt 2))
    {x : ℝ} (hx : 0 < x) (hxc : xc < x) :
    ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  exact partition_diverges_above_inv_cc hx (by rw [hmain, ← xc_inv, inv_inv]; exact hxc)

/-- Direction 2: If μ = √(2+√2), the partition function converges below x_c. -/
theorem partition_converges_of_main_thm
    (hmain : connective_constant = Real.sqrt (2 + Real.sqrt 2))
    {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  exact partition_converges_below_inv_cc hx (by rw [hmain, ← xc_inv, inv_inv]; exact hxc)

/-! ## The partition function Z(x) -/

/-- The partition function Z(x) = Σ c_n · x^n at the critical point. -/
theorem Z_xc_eq_tsum :
    Z xc = ∑' n, (saw_count n : ℝ) * xc ^ n := rfl

/-! ## Summary of the reduction

The proof of Theorem 1 reduces to two partition function bounds:

**Lower bound (μ ≥ √(2+√2))**:
  Show Z(x_c) = +∞, i.e., ¬ Summable (fun n => c_n * x_c^n).
  This follows from:
  - Either E_T^{x_c} > 0 for some T (Case 1), or
  - B_T^{x_c} ≥ c/T for all T, giving Σ B_T = ∞ (Case 2)

**Upper bound (μ ≤ √(2+√2))**:
  Show Z(x) < ∞ for x < x_c, i.e., Summable (fun n => c_n * x^n).
  This follows from:
  - Hammersley-Welsh: Z(x) ≤ 2·∏(1+B_T^x)²
  - Bridge bound: B_T^{x_c} ≤ 1 (from strip identity)
  - Geometric decay: B_T^x ≤ (x/x_c)^T for x < x_c
  - Product convergence: ∏(1+r^T) < ∞ for r < 1

The key identity driving both bounds is the strip identity (Lemma 2):
  1 = c_α · A + B + c_ε · E
which follows from the algebraic identities of the parafermionic observable.
-/

end
