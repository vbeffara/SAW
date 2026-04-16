/-
# Winding properties for SAWs on the hexagonal lattice

Key geometric facts about the winding of walks on the hex lattice.
These are needed for the strip identity proof (Lemma 2 of the paper).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Direction vectors on the hex lattice -/

/-- The starting mid-edge direction is +1 (horizontal right from hexOrigin to paperStart). -/
lemma starting_mid_edge_dir :
    correctHexEmbed paperStart - correctHexEmbed hexOrigin = 1 := by
  unfold paperStart hexOrigin correctHexEmbed; norm_num [Complex.ext_iff]

/-- From FALSE(x,y) the direction to TRUE(x,y) is +1. -/
lemma dir_false_to_true_same' (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

/-- From TRUE(x,y) the direction to FALSE(x,y) is -1. -/
lemma dir_true_to_false_same' (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) = -1 := by
  have h := false_to_true_dir x y
  have : correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) =
    -(correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false)) := by ring
  rw [this, h]

/-! ## Right boundary winding = 0

For walks in the strip from paperStart to a right boundary FALSE vertex,
the exit to the right boundary mid-edge is in direction +1
(from FALSE(x,y) to TRUE(x,y) outside the strip).

Since the starting direction is also +1 (from hexOrigin to paperStart),
the winding from the starting mid-edge to the right boundary mid-edge
is 0 (same direction).
-/

/-- Right boundary exit direction equals starting direction: both are +1.
    This means the winding from a to any right boundary mid-edge is 0. -/
lemma right_boundary_winding_zero :
    ∀ (x y : ℤ),
      correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) =
      correctHexEmbed paperStart - correctHexEmbed hexOrigin := by
  intro x y
  rw [dir_false_to_true_same', starting_mid_edge_dir]

/-! ## Observable phase at critical spin σ = 5/8

At σ = 5/8, the phase factor e^{-iσ·W} for each boundary type:
- Right boundary (W = 0): phase = 1 → contributes B with coefficient 1
- Left boundary (W = ±π): phase = e^{∓i5π/8} → Re = cos(5π/8) = -c_α
- Escape boundary (W = ±2π/3): combined phase gives coefficient c_ε
-/

/-- For right boundary mid-edges, the observable phase is 1 (winding = 0). -/
lemma right_boundary_phase : Complex.exp (-Complex.I * (sigma * 0)) = 1 := by
  simp

/-- The boundary coefficient c_α = cos(3π/8) is the same as -cos(5π/8). -/
lemma c_alpha_eq_neg_cos : c_alpha = -Real.cos (5 * Real.pi / 8) := by
  unfold c_alpha
  rw [show 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 from by ring]
  rw [Real.cos_pi_sub]; ring

/-- The boundary coefficient c_ε = cos(π/4) = √2/2. -/
lemma c_eps_eq' : c_eps = Real.sqrt 2 / 2 := by
  unfold c_eps
  exact Real.cos_pi_div_four

/-! ## Key observation: phase factors at boundary

For the strip identity, the boundary sum involves:
  0 = -F(a) + Σ_{z∈α} F(z) + Σ_{z∈β} F(z) + j·Σ_{z∈ε} F(z) + j̄·Σ_{z∈ε̄} F(z)

Since the winding is path-independent:
- F(a) = 1 (trivial walk, winding 0, weight x^0 = 1)
- Walks to β have winding 0, so Σ F_β = B_edge (real, positive)
- Walks to α have winding ±π, so after conjugate pairing:
  Σ F_α = F(a) + cos(σπ)·A = 1 - c_α·A
- Walks to ε, ε̄ combine to give c_ε·E

Therefore: 0 = -(1 - c_α·A) + B + c_ε·E
           1 = c_α·A + B + c_ε·E

This is the strip identity (Lemma 2 of the paper).
-/

end
