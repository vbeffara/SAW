/-
# Vertex Relation via Triplet Cancellation

The vertex relation at each interior vertex v of the strip domain
follows from the triplet cancellation identity alone.

## Key Insight

Every walk ending at a mid-edge of v is in exactly one TRIPLET:
- TYPE 1: walk γ from a to mid-edge p (from P's side, not visiting v)
- TYPE 2a: extension γ+v→q (from v's side, exiting to q)
- TYPE 2b: extension γ+v→r (from v's side, exiting to r)

The triplet sum is zero by triplet_cancellation:
  (p-v)·weight(γ) + (q-v)·xc·conj(λ)·weight(γ) + (r-v)·xc·λ·weight(γ) = 0

This is simpler than the paper's approach which separates pairs and triplets.
The pair_cancellation identity handles walks visiting all 3 neighbors,
but these are ALSO covered by the triplet partition (since the extension
γ+v→q is always valid: v ∉ γ for TYPE 1 walks).

## Reference

Section 2 of: Hugo Duminil-Copin and Stanislav Smirnov,
"The connective constant of the honeycomb lattice equals √(2+√2)",
Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk classification at a vertex

At a vertex v with neighbors P, Q, R, every walk from a to a mid-edge
of v is either:
1. TYPE 1: arrives at mid-edge p/q/r from the far side (P/Q/R side),
   i.e., the walk's last vertex is P/Q/R and it exits towards v.
2. TYPE 2: arrives at mid-edge p/q/r from v's side,
   i.e., the walk's last vertex is v and it exits towards P/Q/R.

TYPE 2 walks are in bijection with TYPE 1 walks:
- TYPE 2 entering from P, exiting to Q ↔ TYPE 1 from P's side to p
  (remove the last vertex v and change exit from q to p)
-/

/-- A strip walk (vertex-based SAW) ending at a specific vertex. -/
structure VertexWalk (T L : ℕ) (v : HexVertex) where
  len : ℕ
  saw : SAW paperStart len
  endpoint : saw.w = v
  in_strip : ∀ u ∈ saw.p.1.support, PaperFinStrip T L u

/-- The observable weight of a walk: exp(-iσW) · xc^{ℓ+1}.
    The winding W is tracked as an integer multiple of π/3. -/
def walkObservableWeight (T L : ℕ) (v : HexVertex) (s : VertexWalk T L v) : ℂ :=
  Complex.exp (-Complex.I * sigma * (↑(walkWindingInt s.saw.p.1) * Real.pi / 3)) *
  (xc : ℂ) ^ (s.len + 1)

/-! ## The triplet cancellation at a FALSE vertex

At FALSE(x,y), the three neighbors are:
- P = TRUE(x,y): direction (p-v) = 1
- Q = TRUE(x+1,y): direction (q-v) = j = exp(i2π/3)
- R = TRUE(x,y+1): direction (r-v) = conj(j) = exp(-i2π/3)

A TYPE 1 walk from P's side extends to v, then exits to Q or R.
Turn at v from P→v to v→Q: -π/3 = -1 unit → weight factor conj(λ)
Turn at v from P→v to v→R: +π/3 = +1 unit → weight factor λ

Triplet sum:
  1 · weight + j · xc · conj(λ) · weight + conj(j) · xc · λ · weight
  = weight · [1 + xc · j · conj(λ) + xc · conj(j) · λ]
  = weight · 0  (by triplet_cancellation)
-/

/-- The triplet cancellation identity restated. -/
lemma triplet_sum_zero :
    (1 : ℂ) + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 :=
  triplet_cancellation

/-
For FALSE vertices: the three direction vectors.
-/
lemma false_directions (x y : ℤ) :
    (correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1) ∧
    (correctHexEmbed (x + 1, y, true) - correctHexEmbed (x, y, false) = j) ∧
    (correctHexEmbed (x, y + 1, true) - correctHexEmbed (x, y, false) = conj j) := by
  exact ⟨false_to_true_dir x y, by
    unfold correctHexEmbed j; ring;
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring;
    norm_num, by
      unfold correctHexEmbed j;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Real.cos_two_mul, Real.sin_two_mul, mul_div_assoc ];
      constructor <;> ring⟩

/-! ## Boundary edge types in the strip

For the strip identity, we classify boundary mid-edges:
1. Starting mid-edge a: between hexOrigin and paperStart.
   Direction: embed(hexOrigin) - embed(paperStart) = -1.
   Winding: 0 (trivial walk). Weight: xc^0 = 1.
   Contribution to boundary sum: -1 · 1 = -1.

2. Right boundary (β): FALSE(x,y) with x+y = -T → TRUE(x,y) outside.
   Direction: embed(TRUE(x,y)) - embed(FALSE(x,y)) = 1.
   Winding from a: 0 (direction preserved).
   Contribution: +1 · B_paper.

3. Left boundary (α\{a}): TRUE(x,-x) with x ≠ 0 → FALSE(x,-x) outside.
   Direction: embed(FALSE(x,-x)) - embed(TRUE(x,-x)) = -1.
   Winding from a: ±π (direction reverses).
   Contribution: -cos(5π/8) · A = +c_alpha · A.

4. Escape boundary (ε, ε̄): diagonal edges.
   Contribution: c_eps · E (non-negative).
-/

/-- The starting mid-edge direction is -1. -/
lemma starting_midedge_dir :
    correctHexEmbed hexOrigin - correctHexEmbed paperStart = -1 :=
  starting_direction

/-- Right boundary direction is +1. -/
lemma right_boundary_dir (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

end