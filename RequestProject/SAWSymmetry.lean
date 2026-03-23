/-
# The conjugation symmetry of the parafermionic observable

Formalization of the symmetry F(z̄) = F̄(z) used in the derivation of
the strip identity (Lemma 2, Section 3) of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The parafermionic observable F(z) = F(a,z,x_c,σ) has a conjugation symmetry
when the domain Ω has a reflection symmetry mapping z ↦ z̄.

**Key property**: For the strip domain S_{T,L}, which is symmetric under
complex conjugation (i.e., reflection across the real axis), we have

  F(z̄) = F̄(z)

This follows because:
1. The domain is symmetric: z ∈ Ω iff z̄ ∈ Ω
2. Complex conjugation maps walks γ : a → z to walks γ̄ : a → z̄
3. The winding reverses: W_{γ̄}(a, z̄) = -W_γ(a, z)
4. The length is preserved: ℓ(γ̄) = ℓ(γ)

Hence F(z̄) = Σ_{γ:a→z̄} e^{-iσ·W_γ(a,z̄)} · x_c^{ℓ(γ)}
            = Σ_{γ:a→z} e^{-iσ·(-W_γ(a,z))} · x_c^{ℓ(γ)}
            = Σ_{γ:a→z} e^{iσ·W_γ(a,z)} · x_c^{ℓ(γ)}
            = conj(F(z))

## Application

The symmetry is used in evaluating boundary sums in the strip identity.
For the left boundary α, the sum over conjugate pairs gives:

  Σ_{z∈α\{a}} F(z) = Σ pairs (F(z) + F(z̄))/2 · 2
                    = Σ pairs Re(F(z)) · 2 (modulo phase)

With the specific winding values, this produces the coefficient c_α.

## Note on the hex lattice reflection

The hex graph as formalized (bipartite with adjacency offsets (0,0), (1,0), (0,1))
does NOT admit an x-coordinate–preserving reflection as a graph automorphism.
This is because the offset triangle {(0,0), (1,0), (0,1)} is not symmetric under
any reflection that preserves the first coordinate.

**Counterexample**: The naive map (x,y,b) ↦ (x,-y-1,!b) does NOT preserve
adjacency: (0,0,false) adj (1,0,true) but the reflected pair
(0,-1,true) is NOT adj (1,-1,false).

The paper's conjugation symmetry F(z̄) = F̄(z) is a property of the
CONTINUOUS embedding, not a graph automorphism. Formalizing it correctly
would require either:
(a) Changing the lattice coordinatization to one with y-reflection symmetry, or
(b) Proving the strip identity via a direct boundary computation that avoids
    the need for a graph automorphism.

The coordinate-swap automorphism (x,y,b) ↦ (y,x,b) IS a valid graph automorphism
(proved below), but it doesn't preserve the strip structure (it swaps x and y
coordinates).
-/

import RequestProject.SAWObservable

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The coordinate-swap automorphism

The map (x,y,b) ↦ (y,x,b) is a graph automorphism of hexGraph.
This corresponds to a reflection of the hex lattice across the diagonal.
-/

/-- The coordinate-swap map on hex vertices: (x, y, b) ↦ (y, x, b). -/
def hexSwap (v : HexVertex) : HexVertex :=
  (v.2.1, v.1, v.2.2)

/-- The swap is an involution. -/
theorem hexSwap_involution (v : HexVertex) :
    hexSwap (hexSwap v) = v := by
  simp only [hexSwap]

/-- The swap preserves adjacency.
    The adjacency offsets {(0,0), (1,0), (0,1)} are permuted by
    the swap (x,y) ↦ (y,x) to {(0,0), (0,1), (1,0)}, which is the same set. -/
theorem hexSwap_adj {v w : HexVertex} (h : hexGraph.Adj v w) :
    hexGraph.Adj (hexSwap v) (hexSwap w) := by
  unfold hexSwap hexGraph at *
  simp only at *
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-- The swap maps walks to walks. -/
def hexSwapWalk {v w : HexVertex} (p : hexGraph.Walk v w) :
    hexGraph.Walk (hexSwap v) (hexSwap w) := by
  induction p with
  | nil => exact SimpleGraph.Walk.nil
  | cons h _ ih => exact SimpleGraph.Walk.cons (hexSwap_adj h) ih

/-- The swap preserves walk length. -/
theorem hexSwapWalk_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexSwapWalk p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp only [hexSwapWalk, SimpleGraph.Walk.length_cons]; exact congr_arg (· + 1) ih

/-- hexSwap is injective (it's an involution). -/
lemma hexSwap_injective : Function.Injective hexSwap := by
  intro u v h
  have := congr_arg hexSwap h
  simp [hexSwap_involution] at this
  exact this

/-
PROBLEM
The swap maps paths to paths.

PROVIDED SOLUTION
The support of hexSwapWalk p is the List.map hexSwap of p.support. Since hexSwap is injective (it's an involution), and p.IsPath means p.support is nodup, the mapped support is also nodup. First prove the support equality by induction on p, then use List.Nodup.map with hexSwap_injective.
-/
theorem hexSwapWalk_isPath {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) : (hexSwapWalk p).IsPath := by
      -- By definition of `hexSwapWalk`, the support of `hexSwapWalk p` is the image of `p.support` under `hexSwap`.
      have h_support : (hexSwapWalk p).support = List.map hexSwap p.support := by
        induction' p with v w p ih;
        · rfl;
        · unfold hexSwapWalk at * ; aesop;
      simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      exact List.Nodup.map ( fun x y hxy => by simpa using hexSwap_injective hxy ) hp

/-! ## Winding reversal under reflection

Under the reflection z ↦ z̄, the winding of a walk reverses sign:
  W_{γ̄}(a, z̄) = -W_γ(a, z)

This is because reflection reverses the direction of turns:
a left turn becomes a right turn and vice versa.
-/

/-- **Winding reversal** (abstract statement):
    The winding of the reflected walk is the negative of the original winding.
    This follows from the fact that reflection reverses the orientation.
    Algebraically: e^{-i(-w)} = conj(e^{-iw}) for real w. -/
theorem winding_reversal_abstract :
    ∀ (w : ℝ), Complex.exp (Complex.I * ↑w) =
      conj (Complex.exp (-Complex.I * ↑w)) := by
  intro w
  conv_rhs => rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext
  · simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  · simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-! ## The symmetry F(z̄) = F̄(z) (abstract form)

For a symmetric domain with starting point on the axis of symmetry:
-/

/-- The sum of a complex number and its conjugate is twice the real part. -/
theorem sum_conj_eq_two_re (z : ℂ) : z + conj z = ↑(2 * z.re) := by
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re]; ring
  · simp [Complex.add_im, Complex.conj_im]

/-- The sum of a complex number and its conjugate has zero imaginary part. -/
theorem sum_conj_im_zero (z : ℂ) : (z + conj z).im = 0 := by
  simp [Complex.add_im, Complex.conj_im]

/-! ## Application to the strip identity

For the left boundary α:
- Walks from a to the top part of α have winding +π
- Walks from a to the bottom part of α have winding -π
- These come in conjugate pairs (by the reflection symmetry)

The sum over a conjugate pair (z, z̄):
  F(z) + F(z̄) = F(z) + conj(F(z)) = 2·Re(F(z))

For z on the top part of α:
  Re(F(z)) = Re(e^{-iσπ} · Σ x_c^{ℓ(γ)})
           = cos(σπ) · A_{z}
           = cos(5π/8) · A_{z}
           = -cos(3π/8) · A_{z}
           = -c_α · A_{z}

So the total left boundary sum is:
  Σ_{z∈α} F(z) = F(a) + Σ_{pairs} (F(z) + F(z̄))
              = 1 + (-c_α) · A
              = 1 - c_α · A
-/

/-- The left boundary coefficient computation:
    cos(σπ) = cos(5π/8) = -cos(3π/8) = -c_α. -/
theorem left_boundary_coeff' : Real.cos (5 * Real.pi / 8) = -c_alpha := by
  unfold c_alpha
  rw [show 5 * Real.pi / 8 = Real.pi - 3 * Real.pi / 8 by ring]
  exact Real.cos_pi_sub _

/-- For the right boundary β, winding is 0, so the coefficient is cos(0) = 1.
    The sum is simply B. -/
theorem right_boundary_coeff' : Real.cos 0 = 1 := Real.cos_zero

/-- For the top/bottom boundary ε ∪ ε̄, the combined coefficient involves:
    j·e^{-iσ·2π/3} + j̄·e^{iσ·2π/3}
    = e^{i·2π/3}·e^{-i·5π/12} + e^{-i·2π/3}·e^{i·5π/12}
    = e^{i·π/4} + e^{-i·π/4}
    = 2·cos(π/4)
    = 2·c_ε

    So the combined contribution from the top/bottom boundary is c_ε · E
    (after accounting for the factor of 2 from the symmetry). -/
theorem top_bottom_coefficient' :
    Real.cos (Real.pi / 4) = c_eps := by rfl

/-- The angle computation: 2π/3 - 5π/12 = π/4. -/
theorem top_bottom_angle :
    2 * Real.pi / 3 - 5 * Real.pi / 12 = Real.pi / 4 := by ring

/-! ## Summary

The conjugation symmetry F(z̄) = F̄(z) is essential for the strip identity.
It allows us to:

1. **Pair up boundary terms**: Each boundary mid-edge z (not on the axis)
   is paired with z̄, and the sum F(z) + F(z̄) = 2·Re(F(z)).

2. **Extract real coefficients**: The complex weights e^{-iσW} become
   real coefficients cos(σW) after pairing.

3. **Derive positive partition functions**: The real coefficients
   c_α = cos(3π/8) > 0 and c_ε = cos(π/4) > 0 are positive,
   giving the identity 1 = c_α·A + B + c_ε·E with all terms ≥ 0.

Without this symmetry, the strip identity would involve complex coefficients
and would not directly give the partition function bounds needed for the proof.

### Note on formalization status

The hex graph as formalized does not admit an x-preserving reflection.
The coordinate-swap (x,y) ↦ (y,x) IS a valid automorphism (proved above),
but it doesn't correspond to complex conjugation in the embedding.

To fully formalize the strip identity, one would need to either:
(a) Modify the hex lattice coordinatization, or
(b) Prove the boundary evaluation directly without a graph automorphism.

The abstract algebraic content (pair/triplet cancellation, vertex relation,
strip identity structure) is fully proved. The gap is the geometric connection
to the specific strip domain.
-/

end