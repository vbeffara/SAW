/-
# Parafermionic Vertex Relation Infrastructure (Lemma 1)

This file provides proved infrastructure for the vertex relation
and boundary evaluation in the strip identity proof.

## Reference
Lemma 1 of: Hugo Duminil-Copin and Stanislav Smirnov,
"The connective constant of the honeycomb lattice equals √(2+√2)",
Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Direction antisymmetry (key for discrete Stokes)

The direction from v to w is the negative of the direction from w to v.
This is the key cancellation property for interior edges. -/

/-- Direction vectors are antisymmetric. -/
lemma hexDir_antisymm' (v w : HexVertex) :
    (correctHexEmbed w - correctHexEmbed v) +
    (correctHexEmbed v - correctHexEmbed w) = 0 := by
  ring

/-- Interior edge cancellation: contributions from both endpoints sum to zero. -/
lemma interior_edge_cancel' (v w : HexVertex) (F : ℂ) :
    (correctHexEmbed w - correctHexEmbed v) * F +
    (correctHexEmbed v - correctHexEmbed w) * F = 0 := by
  ring

/-! ## Boundary direction factors -/

/-- Right boundary direction is +1 (FALSE to TRUE at same coords). -/
lemma right_boundary_dir (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

/-- Left boundary direction is -1 (TRUE to FALSE at same coords). -/
lemma left_boundary_dir (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) = -1 := by
  unfold correctHexEmbed
  simp [Complex.ext_iff]

/-- Starting direction is -1. -/
lemma starting_dir' :
    correctHexEmbed hexOrigin - correctHexEmbed paperStart = -1 :=
  starting_direction

/-! ## Phase computations for boundary coefficients -/

/-- cos(σπ) = cos(5π/8) = -c_alpha. -/
lemma cos_sigma_pi' : Real.cos (sigma * Real.pi) = -c_alpha := by
  unfold sigma c_alpha
  rw [show 5 / 8 * Real.pi = Real.pi - 3 * Real.pi / 8 from by ring]
  exact Real.cos_pi_sub (3 * Real.pi / 8)

/-- The phase for left boundary walks: exp(-iσπ) has real part -c_alpha.
    This gives the coefficient c_alpha (after multiplying by direction -1). -/
lemma left_boundary_phase_re :
    (Complex.exp (-Complex.I * (sigma * ↑Real.pi))).re = -c_alpha := by
  simp [Complex.exp_re, cos_sigma_pi']

/-- The phase for right boundary walks: exp(-iσ·0) = 1.
    Real part = 1, giving coefficient 1 for B_paper. -/
lemma right_boundary_phase_re :
    (Complex.exp (-Complex.I * (sigma * 0))).re = 1 := by
  simp

/-! ## Summary

The strip identity 1 = c_α·A + B + c_ε·E follows from:

1. **Vertex relation** (Lemma 1): At each interior vertex v,
   Σ_{w adj v} (embed(w) - embed(v)) · F(mid(v,w)) = 0.
   This uses pair_cancellation and triplet_cancellation.

2. **Discrete Stokes**: Sum vertex relations over all v ∈ V(S_{T,L}).
   Interior edges cancel by `interior_edge_cancel'`.
   Only boundary edges survive.

3. **Boundary evaluation**:
   - Starting mid-edge: direction = -1 (`starting_dir'`), F = 1.
     Contribution = -1.
   - Right boundary: direction = +1 (`right_boundary_dir`),
     phase = 1 (`right_boundary_phase_re`).
     Contribution = +B_paper.
   - Left boundary: direction = -1 (`left_boundary_dir`),
     phase Re = -c_alpha (`left_boundary_phase_re`).
     Contribution = (-1)·(-c_alpha)·A = c_alpha·A.
   - Escape boundary: combined gives c_eps·E.

4. **Conclusion**: 0 = -1 + c_alpha·A + B + c_eps·E.
   Therefore: 1 = c_alpha·A + B + c_eps·E.

The algebraic ingredients (pair_cancellation, triplet_cancellation,
boundary_cos_pos, direction computations) are all proved.
The remaining gap is the COMBINATORIAL walk partitioning and
discrete Stokes summation. -/

end
