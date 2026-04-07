/-
# Parafermionic Observable: Helper Lemmas for B_paper ≤ 1

This file decomposes the proof of `B_paper_le_one_direct` into
intermediate lemmas about the parafermionic observable.

## Proof structure

The proof of B_paper ≤ 1 has the following structure:

1. **Vertex relation** (pair/triplet cancellation):
   At each vertex v of the strip, walks ending at v's three mid-edges
   can be grouped into pairs/triplets whose complex contributions cancel.

2. **Summing over vertices** → interior cancellation:
   Interior mid-edges appear in two vertex relations with opposite
   direction factors, cancelling. Only boundary mid-edges survive.

3. **Boundary evaluation**: Extract B ≤ 1 from the boundary sum = 0.

The key insight is that on the hex lattice, the winding TELESCOPES:
  W = exit_angle - entry_angle
because all turns are ±π/3 (less than π, so unambiguous).

## Reference

Sections 2-3 of: Hugo Duminil-Copin and Stanislav Smirnov,
"The connective constant of the honeycomb lattice equals √(2+√2)",
Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Edge angles on the hexagonal lattice

Each edge of the hex lattice has a well-defined direction angle.
These are exactly {0, ±π/3, ±2π/3, π}. -/

/-- Edge angle from v to w (returns 0 for non-adjacent vertices). -/
def hexEdgeAngle' (v w : HexVertex) : ℝ :=
  if v.2.2 = false then
    if w = (v.1, v.2.1, true) then 0
    else if w = (v.1 + 1, v.2.1, true) then 2 * Real.pi / 3
    else if w = (v.1, v.2.1 + 1, true) then -(2 * Real.pi / 3)
    else 0
  else -- v.2.2 = true
    if w = (v.1, v.2.1, false) then Real.pi
    else if w = (v.1 - 1, v.2.1, false) then -(Real.pi / 3)
    else if w = (v.1, v.2.1 - 1, false) then Real.pi / 3
    else 0

/-! ## Winding telescopes on the hex lattice

For any SAW γ from v₀ to vₙ on the hex lattice,
the winding from the entry edge (u → v₀) to the exit edge (vₙ → w) is:
  W = hexEdgeAngle'(vₙ, w) - hexEdgeAngle'(u, v₀)

This is because each turn at an intermediate vertex is ±π/3, and the
winding telescopes: W = Σ (θ_{k+1} - θ_k) = θ_final - θ_initial. -/

/-- The starting edge direction at paperStart.
    Entry from FALSE(0,0) to TRUE(0,0) = paperStart has angle π
    (from TRUE to FALSE is π, so from FALSE to TRUE is 0).
    Actually, the walk enters at paperStart FROM the mid-edge,
    so the entry direction is from FALSE(0,0) towards TRUE(0,0),
    which is angle 0. -/
def paperEntryAngle : ℝ := 0

/-! ## Right boundary exit angle

For right boundary mid-edges: FALSE(x,y) → TRUE(x,y) at x+y=-T.
The exit direction is from FALSE(x,y) to TRUE(x,y), angle 0.
So winding W = exit_angle - entry_angle = 0 - 0 = 0.

This means e^{-iσW} = 1 for all right boundary walks. -/

lemma right_boundary_winding_zero (x y : ℤ) :
    hexEdgeAngle' (x, y, false) (x, y, true) = 0 := by
  simp [hexEdgeAngle']

lemma right_boundary_weight_one (x y : ℤ) :
    Complex.exp (-Complex.I * (sigma * hexEdgeAngle' (x, y, false) (x, y, true))) = 1 := by
  rw [right_boundary_winding_zero]; simp [sigma]

/-! ## Starting mid-edge

The starting mid-edge a connects paperStart = TRUE(0,0) to FALSE(0,0).
The exit direction from paperStart towards FALSE(0,0) is angle π.
The only walk from a to a is the trivial (zero-length) walk.
So F(a) = e^{-iσ·0} · xc^0 = 1.

The direction factor from paperStart to FALSE(0,0) is:
  embed(FALSE(0,0)) - embed(TRUE(0,0)) = -1

So the contribution of a to the boundary sum is (-1) · 1 = -1. -/

lemma starting_midedge_direction :
    correctHexEmbed (0, 0, false) - correctHexEmbed (0, 0, true) = (-1 : ℂ) := by
  unfold correctHexEmbed; simp [Complex.ext_iff]

/-! ## Right boundary direction factor

For right boundary: FALSE(x,y) inside → TRUE(x,y) outside at x+y=-T.
Direction factor: embed(TRUE(x,y)) - embed(FALSE(x,y)) = 1. -/

lemma right_boundary_direction (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = (1 : ℂ) := by
  unfold correctHexEmbed; simp [Complex.ext_iff]

/-! ## Real part of boundary winding factors

For any hex edge angle θ ∈ {0, ±π/3, ±2π/3, π}, the factor
  Re(dir · e^{-iσW})
where σ = 5/8 and W = θ - 0 = θ, satisfies:
  Re(dir · e^{-iσθ}) ≥ 0

This is because on the hex lattice, the direction factor is
e^{iθ} (unit complex number at angle θ), and:
  Re(e^{iθ} · e^{-i5θ/8}) = Re(e^{i3θ/8}) = cos(3θ/8) > 0

by boundary_cos_pos (since |θ| ≤ π implies |3θ/8| < π/2). -/

lemma boundary_contribution_nonneg_re (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    0 < Real.cos (3 * θ / 8) :=
  boundary_cos_pos θ hθ

end
