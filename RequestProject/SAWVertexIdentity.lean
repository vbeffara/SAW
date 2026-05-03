/-
# Vertex relation algebraic identity

The key algebraic identity for the parafermionic observable vertex relation.

At each vertex v of the hexagonal lattice, for each SAW β ending at a
neighbor u of v (with v not visited by β), the total contribution of β
to the vertex sum at v is zero:

  (u - v) · e^{-iσ·θ(u→v)} + xc · Σ_{w ~ v, w ≠ u} (w - v) · e^{-iσ·θ(v→w)} = 0

This identity factors as:
  e^{i·(3/8)·θ₁} · [e^{-i5π/8} + xc · (e^{iπ/4} + e^{iπ/2})] = 0

where the bracket equals zero by triplet_cancellation.

## Reference
  Section 2 of: Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The vertex relation algebraic identity

The key identity: e^{-i5π/8} + xc · (e^{iπ/4} + e^{iπ/2}) = 0

This follows from the triplet cancellation identity by multiplication
by e^{-i5π/8}. -/

/-
The vertex relation identity: the sum of direction-weighted phases
    at a hex vertex is zero.
    This is equivalent to the triplet cancellation multiplied by e^{-i5π/8}.
-/
lemma vertex_phase_identity :
    Complex.exp (-Complex.I * (5 * ↑Real.pi / 8)) +
    (xc : ℂ) * Complex.exp (Complex.I * (↑Real.pi / 4)) +
    (xc : ℂ) * Complex.exp (Complex.I * (↑Real.pi / 2)) = 0 := by
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
  rw [ show 5 * Real.pi / 8 = Real.pi / 2 + Real.pi / 8 by ring, Real.cos_add, Real.sin_add ] ; norm_num ; ring ; norm_num [ xc ] ; ring;
  constructor <;> rw [ ← Real.sqrt_div_self ] <;> ring;
  · rw [ show ( 2 - Real.sqrt 2 ) = 2 * ( 1 - Real.sqrt 2 / 2 ) by ring, Real.sqrt_mul ] <;> norm_num;
    rw [ show ( 1 - Real.sqrt 2 / 2 ) = ( 2 + Real.sqrt 2 ) ⁻¹ by exact eq_inv_of_mul_eq_one_right ( by ring_nf; norm_num ), Real.sqrt_inv ] ; ring;
    rw [ ← Real.sqrt_div_self ] ; ring;
  · grind

/-
The triplet identity implies the vertex phase identity.
    Proof: multiply triplet_cancellation by e^{-i5π/8}.
-/
lemma vertex_phase_from_triplet :
    (1 : ℂ) + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 →
    Complex.exp (-Complex.I * (5 * ↑Real.pi / 8)) +
    (xc : ℂ) * Complex.exp (Complex.I * (↑Real.pi / 4)) +
    (xc : ℂ) * Complex.exp (Complex.I * (↑Real.pi / 2)) = 0 := by
  exact?

/-- The real part of the boundary sum identity coefficient.
    For right boundary walks (exit angle 0):
    Re[e^{i·0} · e^{-iσ·0}] = Re[1] = 1 -/
lemma right_boundary_re_coeff :
    (Complex.exp (Complex.I * 0) * Complex.exp (-Complex.I * (sigma * 0))).re = 1 := by
  simp [sigma]

/-- For left boundary walks (exit angle π):
    Re[e^{iπ} · e^{-iσπ}] = Re[e^{i(1-σ)π}] = cos(3π/8) = c_alpha -/
lemma left_boundary_re_coeff :
    Real.cos ((1 - sigma) * Real.pi) = c_alpha := by
  unfold sigma c_alpha; congr 1; ring

/-- For escape boundary walks (exit angle 2π/3):
    Re[e^{i2π/3} · e^{-iσ·2π/3}] = cos((1-σ)·2π/3) = cos(π/4) = c_eps -/
lemma escape_boundary_re_coeff_pos :
    Real.cos ((1 - sigma) * (2 * Real.pi / 3)) = c_eps := by
  unfold sigma c_eps; congr 1; ring

/-- For escape boundary walks (exit angle -2π/3):
    cos((1-σ)·(-2π/3)) = cos(π/4) = c_eps -/
lemma escape_boundary_re_coeff_neg :
    Real.cos ((1 - sigma) * (-(2 * Real.pi / 3))) = c_eps := by
  unfold sigma c_eps
  rw [show (1 - 5 / 8 : ℝ) * -(2 * Real.pi / 3) = -(Real.pi / 4) from by ring]
  rw [Real.cos_neg]

end