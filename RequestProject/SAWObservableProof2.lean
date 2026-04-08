/-
# Parafermionic Observable: Infrastructure for B_paper ≤ 1

Key proved results for the proof of B_paper_le_one_direct:

1. boundary_weight_re_nonneg: Every hex edge boundary weight has non-negative
   real part. This is the key geometric ingredient.
2. right_boundary_weight: Right boundary weight = 1.
3. starting_dir_factor: Starting direction = -1.

These are used in the proof of B_paper ≤ 1 via the strip identity.

## Reference

Sections 2-3 of: Hugo Duminil-Copin and Stanislav Smirnov,
"The connective constant of the honeycomb lattice equals √(2+√2)",
Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAWObservable

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Boundary weight definitions -/

/-- The direction factor for a directed edge. -/
def dirFactor (v w : HexVertex) : ℂ :=
  correctHexEmbed w - correctHexEmbed v

/-- The complex weight of a boundary edge: dir * exp(-iσθ). -/
def boundaryWeight (v w : HexVertex) : ℂ :=
  dirFactor v w * Complex.exp (-Complex.I * sigma * hexEdgeAngle' v w)

/-! ## Key boundary weight properties -/

/-- Right boundary edges have weight 1. -/
lemma right_boundary_weight_eq (x y : ℤ) :
    boundaryWeight (x, y, false) (x, y, true) = 1 := by
  unfold boundaryWeight dirFactor hexEdgeAngle' correctHexEmbed sigma
  simp [Complex.ext_iff]

/-- Starting mid-edge has direction factor -1. -/
lemma starting_dir_factor_eq :
    dirFactor paperStart (0, 0, false) = -1 := by
  unfold dirFactor paperStart correctHexEmbed
  simp [Complex.ext_iff]

/-- The real part of every boundary weight is non-negative for hex edges.
    This follows from the geometry: dir(v,w) · exp(-iσθ(v,w)) has
    Re = cos(3θ/8) for appropriate parameterization, which is positive
    since |3θ/8| < π/2.

    This is the key geometric ingredient for B_paper ≤ 1:
    all boundary contributions except the starting mid-edge have
    non-negative real parts. -/
lemma boundary_weight_re_nonneg (v w : HexVertex) (hadj : hexGraph.Adj v w) :
    0 ≤ (boundaryWeight v w).re := by
  rcases v with ⟨ x, y, b ⟩ ; rcases w with ⟨ x', y', b' ⟩ ; simp_all +decide [ hexGraph ];
  unfold boundaryWeight; simp +decide [ *, Complex.exp_re, Complex.exp_im ] ;
  unfold dirFactor; unfold hexEdgeAngle'; unfold correctHexEmbed; norm_num;
  rcases hadj with ( ⟨ rfl, rfl, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ⟩ | ⟨ rfl, rfl, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ⟩ ) <;> norm_num [ sigma ] <;> ring_nf <;> norm_num [ Real.pi_pos.ne' ];
  · rw [ show Real.pi * ( 5 / 12 ) = Real.pi / 4 + Real.pi / 6 by ring, Real.cos_add, Real.sin_add ] ; norm_num ; ring ; norm_num;
    nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_two, Real.sq_sqrt zero_le_three ];
  · rw [ show Real.pi * ( 5 / 12 ) = Real.pi / 4 + Real.pi / 6 by ring, Real.cos_add, Real.sin_add ] ; norm_num ; ring ; norm_num;
    nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_two, Real.sq_sqrt zero_le_three ];
  · exact Real.cos_nonpos_of_pi_div_two_le_of_le ( by linarith [ Real.pi_pos ] ) ( by linarith [ Real.pi_pos ] );
  · nlinarith [ show 0 < Real.sqrt 3 * Real.sin ( Real.pi * ( 5 / 24 ) ) by exact mul_pos ( Real.sqrt_pos.mpr zero_lt_three ) ( Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by linarith [ Real.pi_pos ] ) ), show 0 < Real.cos ( Real.pi * ( 5 / 24 ) ) by exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ];
  · exact add_nonneg ( mul_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) ( by norm_num ) ) ( mul_nonneg ( mul_nonneg ( Real.sqrt_nonneg _ ) ( Real.sin_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ) ) ( by norm_num ) )

/-! ## Note on the vertex relation

The vertex relation at each strip vertex is:
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

This does NOT factor as ∑_w dir(v,w) * exp(-iσθ) = 0 (that sum is nonzero).
Instead, the proof requires grouping walks into pairs and triplets at the
level of individual walks, using:
- pair_cancellation: j * conj(lam)^4 + conj(j) * lam^4 = 0
- triplet_cancellation: 1 + xc * j * conj(lam) + xc * conj(j) * lam = 0

The triplet identity has an extra xc factor for the extended walks
(which visit one more vertex), reflecting the critical fugacity condition.
-/

end
