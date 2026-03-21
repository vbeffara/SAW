/-
# Pair and Triplet Cancellation — Detailed Winding Computations

Detailed formalization of the pair and triplet cancellation arguments
from the proof of Lemma 1 in Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

This file provides the detailed winding computations that underlie
the algebraic identities pair_cancellation and triplet_cancellation:

1. **Pair winding**: For a pair of walks visiting all three mid-edges,
   the loop winding is ±4π/3, giving the factor j·λ̄⁴ + j̄·λ⁴.

2. **Triplet winding**: For a triplet of walks visiting one/two mid-edges,
   the extension winding is ±π/3, giving the factor 1 + x_c·j·λ̄ + x_c·j̄·λ.

3. **The turn factorization**: At σ = 5/8, each turn by ±π/3 contributes
   a factor of λ = exp(-i5π/24) or λ̄ = exp(i5π/24).

## Mathematical context

On the hexagonal lattice, a walk can only turn left or right by π/3
at each vertex. So the winding W(a,b) is always a multiple of π/3.

The complex weight exp(-iσW) factors as:
  exp(-iσW) = ∏_{turns} exp(-iσ(±π/3)) = ∏_{turns} λ^{±1}

where λ = exp(-iσπ/3) = exp(-i5π/24).

In a loop around a hexagonal cell, the total winding is ±2π,
which corresponds to 6 left or 6 right turns. The winding around
a vertex (visiting all three mid-edges) is ±4π/3 = ±4 turns.
-/

import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The turn factor λ

Each step on the hexagonal lattice changes direction by ±π/3.
At σ = 5/8, the weight per turn is:

  left turn:  exp(-iσ·π/3) = exp(-i5π/24) = λ
  right turn: exp(iσ·π/3) = exp(i5π/24) = λ̄
-/

/-- The turn angle on the hexagonal lattice: π/3 = 60°. -/
def turn_angle : ℝ := Real.pi / 3

/-- The weight per left turn: λ = exp(-i·5π/24). -/
theorem lam_eq_left_turn : lam = Complex.exp (-Complex.I * ↑(sigma * turn_angle)) := by
  unfold lam sigma turn_angle; congr 1; push_cast; ring

/-- The weight per right turn: λ̄ = exp(i·5π/24). -/
theorem conj_lam_eq_right_turn : conj lam = Complex.exp (Complex.I * ↑(sigma * turn_angle)) := by
  rw [lam_eq_left_turn, ← Complex.exp_conj]
  congr 1; simp [Complex.conj_ofReal]

/-! ## Pair winding: ±4π/3

For a pair of walks visiting all three mid-edges {p, q, r} adjacent to v:

Walk γ₁: enters at p, goes around v (say clockwise), exits at q.
Walk γ₂: enters at p, goes around v (counterclockwise), exits at r.

The windings satisfy:
  W(γ₁, p→q) = -(4/3)·π  (four left turns = -4π/3)
  W(γ₂, p→r) = +(4/3)·π  (four right turns = +4π/3)

The loop around v (from p through all three mid-edges back near p)
has winding ±4π/3, not ±2π, because the loop visits only 4 of the
6 edges around the hexagonal cell.

This gives: exp(-iσ·W₁(p,q)) = λ̄⁴ and exp(-iσ·W₂(p,r)) = λ⁴.

Combined with the geometric factors j = (q-v)/(p-v) and j̄ = (r-v)/(p-v):

  c(γ₁) + c(γ₂) = (p-v)·exp(-iσ·W(a,p))·x^ℓ · (j·λ̄⁴ + j̄·λ⁴) = 0
-/

/-- The pair loop winding: ±4π/3 corresponds to ±4 turns of π/3.
    4 · σ · π/3 = 4 · 5/8 · π/3 = 5π/6. -/
theorem pair_loop_angle : 4 * sigma * turn_angle = 5 * Real.pi / 6 := by
  unfold sigma turn_angle; ring

/-- The pair factor λ̄⁴ corresponds to 4 left turns.
    exp(-i · 4 · σ · π/3) = exp(-i · 5π/6) = λ⁴. -/
theorem conj_lam_pow_four_eq :
    conj lam ^ 4 = Complex.exp (Complex.I * ↑(4 * sigma * turn_angle)) := by
  rw [conj_lam_eq_right_turn]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- The pair factor λ⁴ corresponds to 4 right turns. -/
theorem lam_pow_four_eq :
    lam ^ 4 = Complex.exp (-Complex.I * ↑(4 * sigma * turn_angle)) := by
  rw [lam_eq_left_turn]; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- **Pair cancellation identity** (restated with geometric meaning):
    j · exp(i · 4σπ/3) + j̄ · exp(-i · 4σπ/3) = 0.

    This means: j · λ̄⁴ + j̄ · λ⁴ = 0.

    Geometrically: the clockwise and counterclockwise loop contributions
    cancel exactly because of the special value σ = 5/8. -/
theorem pair_cancellation_geometric :
    j * Complex.exp (Complex.I * ↑(4 * sigma * turn_angle)) +
    conj j * Complex.exp (-Complex.I * ↑(4 * sigma * turn_angle)) = 0 := by
  rw [← conj_lam_pow_four_eq, ← lam_pow_four_eq]
  exact pair_cancellation

/-! ## Triplet winding: ±π/3

For a triplet of walks visiting one or two mid-edges of v:

Walk γ₁: ends at p (visits only mid-edge p of v).
Walk γ₂: extends γ₁ by one step to q (left turn of π/3).
Walk γ₃: extends γ₁ by one step to r (right turn of π/3).

The windings satisfy:
  W(γ₂, p→q) = -(1/3)·π  (one left turn)
  W(γ₃, p→r) = +(1/3)·π  (one right turn)

This gives:
  exp(-iσ·W₂(p,q)) = λ̄ and exp(-iσ·W₃(p,r)) = λ

The length increases by 1: ℓ(γ₂) = ℓ(γ₃) = ℓ(γ₁) + 1.

Combined with geometric factors j and j̄:

  c(γ₁) + c(γ₂) + c(γ₃) = (p-v)·exp(-iσ·W(a,p))·x^ℓ₁ · (1 + x·j·λ̄ + x·j̄·λ)

This is the ONLY place where x = x_c is used.
-/

/-- The triplet extension angle: σ · π/3 = 5π/24. -/
theorem triplet_extension_angle : sigma * turn_angle = 5 * Real.pi / 24 := by
  unfold sigma turn_angle; ring

/-- The triplet factor conj(λ) corresponds to one left turn. -/
theorem conj_lam_eq_one_left_turn :
    conj lam = Complex.exp (Complex.I * ↑(sigma * turn_angle)) := conj_lam_eq_right_turn

/-- The triplet factor λ corresponds to one right turn. -/
theorem lam_eq_one_right_turn :
    lam = Complex.exp (-Complex.I * ↑(sigma * turn_angle)) := lam_eq_left_turn

/-- **Triplet cancellation identity** (restated with geometric meaning):
    1 + x_c · j · exp(iσπ/3) + x_c · j̄ · exp(-iσπ/3) = 0.

    This means: 1 + x_c · j · λ̄ + x_c · j̄ · λ = 0.

    This is the ONLY place where x = x_c is critical.
    At this value: x_c = 1/(2cos(π/8)), and cos(7π/8) = -cos(π/8) = -1/(2x_c).
    So: j·λ̄ + j̄·λ = 2Re(j·λ̄) = 2cos(2π/3 + 5π/24) = 2cos(7π/8) = -2cos(π/8) = -1/x_c.
    Hence: 1 + x_c·(-1/x_c) = 0. -/
theorem triplet_cancellation_geometric :
    1 + (xc : ℂ) * j * Complex.exp (Complex.I * ↑(sigma * turn_angle)) +
    (xc : ℂ) * conj j * Complex.exp (-Complex.I * ↑(sigma * turn_angle)) = 0 := by
  rw [← conj_lam_eq_right_turn, ← lam_eq_left_turn]
  exact triplet_cancellation

/-! ## Why x = x_c is special

The triplet cancellation requires:
  1 + x · (j · λ̄ + j̄ · λ) = 0

Since j · λ̄ + j̄ · λ = 2 · Re(j · λ̄) is a real number, this determines x:

  x = -1 / (j · λ̄ + j̄ · λ) = -1 / (2 · Re(j · λ̄))

The paper computes:
  j · λ̄ = exp(i2π/3) · exp(i5π/24) = exp(i(2π/3 + 5π/24)) = exp(i·7π/8)

  Re(exp(i·7π/8)) = cos(7π/8) = -cos(π/8)

So: x = -1 / (2 · (-cos(π/8))) = 1 / (2cos(π/8))

And 2cos(π/8) = √(2+√2) (by the half-angle formula).

Therefore x = 1/√(2+√2) = x_c.
-/

/-- The combined phase angle: 2π/3 + 5π/24 = 7π/8. -/
theorem combined_phase_angle :
    2 * Real.pi / 3 + 5 * Real.pi / 24 = 7 * Real.pi / 8 := by ring

/-- cos(7π/8) = -cos(π/8). -/
theorem cos_seven_pi_eighth : Real.cos (7 * Real.pi / 8) = -Real.cos (Real.pi / 8) := by
  rw [show 7 * Real.pi / 8 = Real.pi - Real.pi / 8 from by ring]
  exact Real.cos_pi_sub _

/-- The real part of j · λ̄: Re(j · λ̄) = cos(7π/8) = -cos(π/8). -/
theorem re_j_conj_lam' : (j * conj lam).re = -Real.cos (Real.pi / 8) := by
  exact re_j_conj_lam

/-- x_c is uniquely determined by the triplet cancellation:
    x_c = -1 / (2·Re(j·λ̄)) = 1 / (2·cos(π/8)) = 1/√(2+√2). -/
theorem xc_from_triplet : xc = 1 / (2 * Real.cos (Real.pi / 8)) := by
  rw [show (2 : ℝ) * Real.cos (Real.pi / 8) = Real.sqrt (2 + Real.sqrt 2) from
    (sqrt_two_add_sqrt_two_eq).symm]
  rfl

/-! ## Summary: Why μ = √(2+√2)

The full logical chain from Section 2:

1. The parafermionic observable F is defined for σ = 5/8.
2. Each walk's contribution to the vertex relation factors through turns of ±π/3.
3. Pairs (all 3 mid-edges visited): contributions cancel by j·λ̄⁴ + j̄·λ⁴ = 0.
   This is pure algebra — holds for any x.
4. Triplets (1 or 2 mid-edges visited): contributions cancel by
   1 + x·j·λ̄ + x·j̄·λ = 0, which REQUIRES x = x_c.
5. The vertex relation holds at x = x_c.
6. Summing over a strip domain gives 1 = c_α·A + B + c_ε·E.
7. This gives B^{x_c}_T ≤ 1, from which the upper bound μ ≤ √(2+√2) follows
   via the bridge decomposition.
8. The same identity, combined with the recurrence, gives B_T ≥ c/T,
   from which the lower bound μ ≥ √(2+√2) follows.

The key insight is that the value x_c = 1/√(2+√2) is not guessed but
FORCED by the requirement that the triplet contribution vanishes.
-/

end
