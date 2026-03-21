/-
# Winding analysis and boundary coefficient derivation

Detailed formalization of the winding calculations from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

This file formalizes the detailed computation of the boundary coefficients
c_α = cos(3π/8) and c_ε = cos(π/4) in the strip identity (Lemma 2):

  1 = c_α · A^{x_c}_{T,L} + B^{x_c}_{T,L} + c_ε · E^{x_c}_{T,L}

The coefficients arise from the winding of self-avoiding walks to each
boundary part, combined with the symmetry F(z̄) = F̄(z) of the domain.
-/

import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## σ = 5/8 and the winding weights -/

/-- The winding to the left boundary is ±π. After applying σ = 5/8:
    σ·π = 5π/8. -/
lemma sigma_pi : sigma * Real.pi = 5 * Real.pi / 8 := by
  unfold sigma; ring

/-- cos(5π/8) = -cos(3π/8), giving the coefficient -c_α on the left boundary. -/
lemma cos_sigma_pi_eq_neg_c_alpha :
    Real.cos (sigma * Real.pi) = -c_alpha := by
  unfold sigma c_alpha
  rw [← Real.cos_pi_sub]; ring_nf

/-- The right boundary coefficient: cos(σ·0) = 1. -/
lemma cos_sigma_zero : Real.cos (sigma * 0) = 1 := by simp

/-- σ · 2π/3 = 5π/12. -/
lemma sigma_two_pi_thirds : sigma * (2 * Real.pi / 3) = 5 * Real.pi / 12 := by
  unfold sigma; ring

/-- The combined top/bottom boundary gives coefficient 2·c_ε. -/
lemma top_bottom_coefficient :
    2 * Real.cos (2 * Real.pi / 3 - sigma * (2 * Real.pi / 3)) = 2 * c_eps := by
  unfold sigma c_eps; ring_nf

/-- 2π/3 - 5π/12 = π/4. -/
lemma angle_difference :
    2 * Real.pi / 3 - sigma * (2 * Real.pi / 3) = Real.pi / 4 := by
  unfold sigma; ring

/-- c_ε = √2/2. -/
lemma c_eps_eq_sqrt2_div2 : c_eps = Real.sqrt 2 / 2 := by
  unfold c_eps; exact Real.cos_pi_div_four

/-! ## Derivation of Equation (3) from Equation (2) -/

/-- Equation (3) follows from Equation (2) and the boundary evaluations. -/
theorem equation_3_from_equation_2 (A B E : ℝ)
    (h_eq2 : 0 = -(1 - c_alpha * A) + B + c_eps * E) :
    1 = c_alpha * A + B + c_eps * E := by linarith

/-! ## The symmetry F(z̄) = F̄(z) -/

/-- For conjugate pairs: w + conj w = 2 · Re(w). -/
theorem conjugate_pair_sum (w : ℂ) :
    w + conj w = ↑(2 * w.re) := by
  apply Complex.ext <;> simp [Complex.add_re, Complex.add_im]
  ring

/-! ## The pair cancellation angle -/

/-- 2π/3 + 4·(5π/24) = 3π/2. -/
lemma pair_angle : 2 * Real.pi / 3 + 4 * (5 * Real.pi / 24) = 3 * Real.pi / 2 := by ring

/-- -(2π/3) + 4·(-(5π/24)) = -3π/2. -/
lemma conj_pair_angle : -(2 * Real.pi / 3) + 4 * -(5 * Real.pi / 24) = -(3 * Real.pi / 2) := by ring

/-! ## The triplet cancellation angle -/

/-- 2π/3 + 5π/24 = 7π/8. -/
lemma triplet_angle : 2 * Real.pi / 3 + 5 * Real.pi / 24 = 7 * Real.pi / 8 := by ring

/-- cos(7π/8) = -cos(π/8). -/
lemma cos_seven_pi_eight : Real.cos (7 * Real.pi / 8) = -Real.cos (Real.pi / 8) := by
  rw [show 7 * Real.pi / 8 = Real.pi - Real.pi / 8 by ring]
  exact Real.cos_pi_sub (Real.pi / 8)

/-- The strip identity bounds. -/
theorem strip_bounds' {A B E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hid : 1 = c_alpha * A + B + c_eps * E) :
    B ≤ 1 := by
  nlinarith [c_alpha_pos, c_eps_pos]

end
