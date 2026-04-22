/-
# Parafermionic Observable: Core Infrastructure

This file provides the core definitions and lemmas for the parafermionic
observable proof of the strip identity (Lemma 2 of Duminil-Copin & Smirnov 2012).

## Key insight: Winding telescopes for SAWs

On the hexagonal lattice, the winding angle of a self-avoiding walk
(which is a simple path) telescopes:
  W(γ) = exit_angle - entry_angle
This means the phase factor e^{-iσW} depends ONLY on the exit direction,
not on the path taken. This dramatically simplifies the proof.

## Proof structure

1. At each vertex v, walks are grouped into pairs and triplets that cancel
   (vertex relation, Lemma 1).
2. Summing vertex relations over all strip vertices: interior mid-edges
   cancel, only boundary terms survive (discrete Stokes).
3. Evaluating boundary terms gives the strip identity.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Edge directions in the hexagonal lattice

Each edge in hexGraph has a well-defined direction vector in ℂ,
obtained from correctHexEmbed. All edges have unit length. -/

/-- The six possible edge directions on the hex lattice. -/
def hexEdgeDir' (v w : HexVertex) : ℂ :=
  correctHexEmbed w - correctHexEmbed v

/-- From FALSE to TRUE at same coords: direction = 1 (angle 0). -/
lemma hexEdgeDir'_FT_same (x y : ℤ) :
    hexEdgeDir' (x, y, false) (x, y, true) = 1 :=
  false_to_true_dir x y

/-- From TRUE to FALSE at same coords: direction = -1 (angle π). -/
lemma hexEdgeDir'_TF_same (x y : ℤ) :
    hexEdgeDir' (x, y, true) (x, y, false) = -1 := by
  unfold hexEdgeDir'
  have h := false_to_true_dir x y
  unfold correctHexEmbed at h ⊢
  simp [Complex.ext_iff] at h ⊢

/-- The direction from v to w is the negative of the direction from w to v. -/
lemma hexEdgeDir'_antisymm (v w : HexVertex) :
    hexEdgeDir' v w = -hexEdgeDir' w v := by
  unfold hexEdgeDir'; ring

/-! ## Walk exit direction

For a walk v₀ → v₁ → ... → vₙ, the exit direction is the direction
of the last edge (vₙ₋₁ → vₙ). For walks of length 0, we use the
convention that the exit direction equals the entry direction (= 1). -/

/-- The exit direction of a walk: direction of the last edge. -/
noncomputable def walkExitDir' : {v w : HexVertex} → hexGraph.Walk v w → ℂ
  | _, _, .nil => 1
  | v, w, .cons _ .nil => hexEdgeDir' v w
  | _, _, .cons _ (.cons h₂ p) => walkExitDir' (.cons h₂ p)

/-! ## Boundary classification for the infinite strip

In PaperInfStrip T, the boundary mid-edges are:
1. Starting mid-edge: (hexOrigin, paperStart) — the entry point
2. Left boundary: (TRUE(x,-x), FALSE(x,-x)) for x ∈ ℤ — exit at diagCoord 0
3. Right boundary: (FALSE(x,y), TRUE(x,y)) with x+y = -T — exit at diagCoord -T
-/

/-- A vertex is on the left boundary of PaperInfStrip T if it's TRUE with diagCoord 0. -/
def isLeftBoundary' (T : ℕ) (v : HexVertex) : Prop :=
  v.2.2 = true ∧ v.1 + v.2.1 = 0 ∧ PaperInfStrip T v

/-- A vertex is on the right boundary of PaperInfStrip T if it's FALSE with diagCoord -T. -/
def isRightBoundary' (T : ℕ) (v : HexVertex) : Prop :=
  v.2.2 = false ∧ v.1 + v.2.1 = -(T : ℤ) ∧ PaperInfStrip T v

/-! ## Key boundary angle computations

For the strip identity, we need:
- Right boundary: exit direction = 1 (from FALSE to TRUE, same coords), angle 0
- Left boundary: exit direction = -1 (from TRUE to FALSE, same coords), angle π
-/

/-- The coefficient for right boundary contributions.
    Direction × phase = 1 × exp(0) = 1, so Re = 1. -/
lemma right_boundary_coeff_re :
    (1 : ℂ).re = (1 : ℝ) := by simp

/-
The coefficient for left boundary contributions.
    Direction = -1, phase = exp(-i·5π/8), so direction × phase = -exp(-i5π/8).
    Re(-exp(-i5π/8)) = -cos(5π/8) = cos(3π/8) = c_alpha.
-/
lemma left_boundary_coeff_re :
    (-Complex.exp (-Complex.I * ((5 : ℝ) * Real.pi / 8))).re = c_alpha := by
  unfold c_alpha; norm_num [ Complex.exp_re ] ; ring;
  rw [ ← Real.cos_pi_sub ] ; ring

/-- The starting mid-edge contribution is -1 (real). -/
lemma starting_midedge_coeff :
    hexEdgeDir' paperStart hexOrigin = -1 := by
  unfold hexEdgeDir' paperStart hexOrigin correctHexEmbed
  simp [Complex.ext_iff]

/-! ## Observable factorization

Since the winding telescopes for SAWs, the observable at a boundary mid-edge
factors as:
  F(z) = ∑_{γ: a→z} e^{-iσW(γ)} xc^ℓ(γ)
       = e^{-iσ·exit_angle} × ∑_{γ: a→z} xc^ℓ(γ)

because the phase e^{-iσW} = e^{-iσ·exit_angle} is the same for ALL walks
ending at z (since all such walks exit in the same direction).

This means:
- Right boundary: phase = 1, contribution = 1 × ∑ xc^ℓ = B
- Left boundary: phase = e^{-i5π/8}, contribution = -1 × e^{-i5π/8} × ∑ xc^ℓ
  Re = c_alpha × ∑ xc^ℓ = c_alpha × A
- Starting: phase = 1, contribution = -1 × 1 = -1
-/

/-! ## The strip identity proof strategy

The proof combines three ingredients:
1. **Vertex relation** (algebraic, proved): pair_cancellation + triplet_cancellation
   ensure that at each vertex, contributions cancel.
2. **Discrete Stokes** (combinatorial): interior mid-edges cancel in the sum.
3. **Boundary evaluation** (computational): boundary terms give the identity.

The boundary sum = 0 gives:
  0 = -1 + xc × paper_bridge_partition T xc + c_alpha × A_inf T xc
  ⟹ 1 = c_alpha × A_inf T xc + xc × paper_bridge_partition T xc
-/

end