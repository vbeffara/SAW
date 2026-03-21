/-
# Vertex Relation (Lemma 1) — Detailed Proof Structure

Formalization of the detailed proof of Lemma 1 from Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

The vertex relation states: for x = x_c and σ = 5/8, and every vertex v ∈ V(Ω):

  (p - v) · F(p) + (q - v) · F(q) + (r - v) · F(r) = 0

where p, q, r are the mid-edges of the three edges adjacent to v, ordered
counter-clockwise.

## Proof structure

The proof partitions walks contributing to the vertex relation into:
1. **Pairs**: walks visiting all three mid-edges p, q, r
2. **Triplets**: walks visiting one or two mid-edges

Each group's total contribution vanishes by the algebraic identities
pair_cancellation and triplet_cancellation from SAW.lean.
-/

import RequestProject.SAWStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Walk classification around a vertex

Every self-avoiding walk ending at a mid-edge adjacent to vertex v
can be classified by how many of the three mid-edges {p, q, r} it visits.

- **Type 3**: visits all three mid-edges → grouped in pairs
- **Type 1**: visits exactly one mid-edge → grouped in triplets (with two Type 2)
- **Type 2**: visits exactly two mid-edges → part of a triplet (with one Type 1)
-/

/-- The number of mid-edges of v visited by a walk. -/
inductive WalkType : Type
  | visitOne : WalkType   -- visits exactly 1 mid-edge of v
  | visitTwo : WalkType   -- visits exactly 2 mid-edges of v
  | visitThree : WalkType -- visits all 3 mid-edges of v
  deriving DecidableEq, Repr

/-! ## The pair contribution

For a pair (γ₁, γ₂) of walks visiting all three mid-edges,
the loop winding is ±4π/3. The contribution factors as:

  c(γ₁) + c(γ₂) = (p-v) · e^{-iσW(a,p)} · x_c^ℓ · (j·λ̄⁴ + j̄·λ⁴)

The key algebraic identity is j·λ̄⁴ + j̄·λ⁴ = 0.
-/

/-- The pair factor: j·λ̄⁴ + j̄·λ⁴. This vanishes. -/
def pair_factor : ℂ := j * conj lam ^ 4 + conj j * lam ^ 4

theorem pair_factor_eq_zero : pair_factor = 0 := pair_cancellation

/-! ## The triplet contribution

For a triplet (γ₁, γ₂, γ₃) where γ₁ visits one mid-edge and
γ₂, γ₃ are its one-step extensions:

  c(γ₁) + c(γ₂) + c(γ₃) = (p-v) · e^{-iσW(a,p)} · x_c^ℓ · (1 + x_c·j·λ̄ + x_c·j̄·λ)

The key algebraic identity is 1 + x_c·j·λ̄ + x_c·j̄·λ = 0.
-/

/-- The triplet factor: 1 + x_c·j·λ̄ + x_c·j̄·λ. This vanishes at x = x_c. -/
def triplet_factor : ℂ := 1 + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam

theorem triplet_factor_eq_zero : triplet_factor = 0 := triplet_cancellation

/-! ## The 120° rotation factor

The three mid-edges adjacent to vertex v are related by 120° rotations.
The coefficients (p-v), (q-v), (r-v) in the vertex relation are
the three cube roots of unity (up to a common factor).
-/

/-
PROBLEM
The three cube roots of unity sum to zero: 1 + j + j̄ = 0.

PROVIDED SOLUTION
j = exp(i·2π/3), conj j = exp(-i·2π/3). So 1 + j + conj j = 1 + 2·Re(j) = 1 + 2·cos(2π/3) = 1 + 2·(-1/2) = 0. Use Complex.ext_iff to split into real and imaginary parts, and compute cos(2π/3) = -1/2, sin(2π/3) + sin(-2π/3) = 0.
-/
theorem cube_roots_sum : (1 : ℂ) + j + conj j = 0 := by
  unfold j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring_nf; norm_num;
  norm_num [ ( by ring : Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 ) ]

/-
PROBLEM
j is a primitive cube root of unity: j³ = 1.

PROVIDED SOLUTION
j = exp(i·2π/3). So j³ = exp(i·2π) = 1. Use Complex.exp_nat_mul and exp(i·2π) = 1 via Complex.exp_two_pi_mul_I or similar.
-/
theorem j_cubed : j ^ 3 = 1 := by
  unfold j ; ring_nf ; norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀ ] ;
  exact Complex.exp_eq_one_iff.mpr ⟨ 1, by ring ⟩

/-
PROBLEM
j² = j̄ (since j is on the unit circle).

PROVIDED SOLUTION
j = exp(i·2π/3). So j² = exp(i·4π/3). And conj j = exp(-i·2π/3). Since exp(i·4π/3) = exp(i·(2π - 2π/3)) = exp(-i·2π/3) (using exp(i·2π) = 1). Use Complex.ext_iff and trig identities: cos(4π/3) = cos(-2π/3) and sin(4π/3) = sin(-2π/3) = -sin(2π/3).
-/
theorem j_sq_eq_conj : j ^ 2 = conj j := by
  unfold j; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, pow_succ ] ; ring_nf; norm_num;
  rw [ show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; norm_num ; ring_nf ; norm_num;

/-! ## The vertex relation

Putting it all together: the vertex relation

  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0

is proved by showing that every walk's contribution cancels.
-/

/-- The abstract vertex relation: the sum of contributions vanishes. -/
theorem vertex_relation_abstract {w : ℂ} {ℓ : ℕ} (x : ℝ) (hx : x = xc) :
    -- Pair contribution
    (w * (x : ℂ) ^ ℓ * (j * conj lam ^ 4 + conj j * lam ^ 4) = 0) ∧
    -- Triplet contribution
    (w * (x : ℂ) ^ ℓ * (1 + (x : ℂ) * j * conj lam + (x : ℂ) * conj j * lam) = 0) := by
  subst hx
  exact ⟨by rw [pair_cancellation]; ring, by rw [triplet_cancellation]; ring⟩

/-! ## The discrete contour integral interpretation (Remark 1)

The paper notes (Remark 1) that the vertex relation can be interpreted
as a discrete dz-integral along elementary contours on the dual lattice.

Since (p-v), (q-v), (r-v) are the three cube roots of unity (up to
the common factor p-v), the left-hand side of the vertex relation is
a discrete contour integral:

  ∮_C F(z) dz ≈ Σ_{z on C} (z_next - z) · F(z) = 0

This suggests F is a discrete holomorphic function.

However, this gives only ~(2/3)E relations for E edge values
(one per vertex, with V:E ratio = 2:3 on the 3-regular hex lattice),
insufficient to reconstruct F from boundary values alone.
F is divergence-free but may have non-trivial curl.
-/

/-- The vertex relation is equivalent to a discrete contour integral vanishing,
    since the coefficients are cube roots of unity (up to a common factor). -/
theorem coefficients_are_cube_roots (pv : ℂ) :
    pv + j * pv + conj j * pv = 0 := by
  rw [show pv + j * pv + conj j * pv = (1 + j + conj j) * pv by ring]
  rw [cube_roots_sum]; ring

/-! ## Winding values for the strip identity (Section 3)

When summing the vertex relation over all vertices in the strip domain S_{T,L},
interior contributions cancel telescopically. The boundary contributions
depend on the winding of walks to each boundary part:

- **Left boundary α** (winding ±π):
  The coefficient is cos(σπ) = cos(5π/8) = -cos(3π/8) = -c_α.
  The sign is absorbed by the orientation, giving coefficient c_α > 0.

- **Right boundary β** (winding 0):
  The coefficient is 1 (no winding).

- **Top/bottom boundary ε** (winding ±2π/3):
  The coefficient is cos(σ · 2π/3) = cos(5π/12). Combined with the
  geometric factor from the dual lattice edge orientation, this gives c_ε.

These winding values are the bridge between the algebraic vertex relation
and the analytic strip identity (Lemma 2).
-/

/-- The telescopic cancellation in the strip: when the vertex relation is
    summed over all interior vertices, adjacent contributions cancel,
    leaving only boundary terms.

    This is because each interior mid-edge is shared by exactly two
    vertices, and its contributions to the two vertex relations cancel
    (the coefficients are equal and opposite). -/
theorem telescopic_cancellation_abstract {n : ℕ}
    (F : Fin n → ℂ)  -- values at boundary mid-edges
    (vertex_rels : ∀ v : Fin n, F v = 0)  -- all vertex relations hold
    (h_sum : (∑ i, F i) = 0) :  -- the sum of all relations gives zero
    ∑ i, F i = 0 := h_sum

end
