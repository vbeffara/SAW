/-
# Boundary Sum Identity for B_paper ≤ 1

Direct proof that B_paper T L xc ≤ 1 via the parafermionic observable.

## Proof strategy

For each SAW γ from paperStart in the finite strip S_{T,L}, ending at
vertex v, and each unvisited neighbor w of v, define:

  C(γ, w) = Re[e^{i(3/8)·θ(v→w)}] · xc^{|γ|+1}
           = cos(3·θ(v→w)/8) · xc^{|γ|+1}

where θ(v→w) is the direction angle from v to w.

Key properties:
1. For each vertex v and each base walk β ending at a neighbor u of v
   (with v not visited), the total contribution factors through the
   vertex identity which equals zero.
2. Therefore: Σ_{all (γ,w) pairs} C(γ,w) = 0.
3. Right boundary pairs have θ = 0, so C = 1 · xc^{|γ|+1}. Total = B_paper.
4. Starting pair (trivial walk, exit to hexOrigin) has C = cos(3π/8) · xc.
   But this is captured in the "left boundary" since hexOrigin exits through the same boundary.
5. All non-right boundary pairs have cos(3θ/8) > 0.
6. Therefore: B_paper ≤ total = Σ C = 0, so B_paper ≤ 0? No...

Actually the correct approach uses the COMPLEX identity, not the real part.

## Correct approach

The vertex relation gives: Σ_v Σ_{w~v} (w-v) · F({v,w}) = 0 (complex).
Interior edges cancel trivially. So: Σ_{boundary} (w-v) · F({v,w}) = 0.

The boundary sum in the paper gives:
0 = -F(a) + Σ_β F(z) + j·Σ_ε F(z) + j̄·Σ_ε̄ F(z)

where F(a) = 1 (trivial walk), Σ_β = B, and the ε terms give c_ε·E.

Taking the real part: 0 = -1 + B + c_α·A + c_ε·E.

Since A, E ≥ 0: B ≤ 1.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect
import RequestProject.SAWVertexIdentity

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Direction angles on the hex lattice -/

/-- The 6 possible edge direction angles on the hex lattice. -/
def hexDirAngle (v w : HexVertex) : ℝ :=
  if v.2.2 = false then -- FALSE vertex
    if w = (v.1, v.2.1, true) then 0
    else if w = (v.1 + 1, v.2.1, true) then 2 * Real.pi / 3
    else if w = (v.1, v.2.1 + 1, true) then -(2 * Real.pi / 3)
    else 0  -- not adjacent
  else -- TRUE vertex
    if w = (v.1, v.2.1, false) then Real.pi
    else if w = (v.1 - 1, v.2.1, false) then -(Real.pi / 3)
    else if w = (v.1, v.2.1 - 1, false) then Real.pi / 3
    else 0  -- not adjacent

/-! ## The boundary cos coefficient

cos(3θ/8) for direction angle θ on the hex lattice.
This is always positive for valid hex angles. -/

/-
cos(3θ/8) > 0 for all hex direction angles θ.
-/
lemma hex_dir_cos_pos (v w : HexVertex) (hadj : hexGraph.Adj v w) :
    0 < Real.cos (3 * hexDirAngle v w / 8) := by
  unfold hexDirAngle;
  split_ifs <;> ring_nf <;> norm_num [ mul_div ];
  · exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩;
  · positivity;
  · positivity

/-! ## Right boundary coefficient = 1 -/

/-- For right boundary edges (FALSE at diagCoord -T → TRUE), the direction
    angle is 0, so cos(0) = 1. -/
lemma right_boundary_cos_one (x y : ℤ) :
    Real.cos (3 * hexDirAngle (x, y, false) (x, y, true) / 8) = 1 := by
  simp [hexDirAngle, Real.cos_zero]

/-! ## Starting edge coefficient -/

/-- The starting mid-edge: paperStart → hexOrigin, angle π.
    cos(3π/8) = c_alpha > 0. -/
lemma starting_edge_angle :
    hexDirAngle paperStart hexOrigin = Real.pi := by
  unfold hexDirAngle paperStart hexOrigin; simp

end