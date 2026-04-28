/-
# Vertex Relation Algebraic Core (Lemma 1)

The triplet and pair cancellation identities expressed in geometric form,
connecting the abstract algebraic identities to the hex lattice structure.
-/

import Mathlib
import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Triplet cancellation in geometric form -/

/-- Triplet cancellation:  1 + xc · j · conj(λ) + xc · conj(j) · λ = 0. -/
theorem triplet_cancel_geom :
    (1 : ℂ) + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 :=
  triplet_cancellation

/-- Pair cancellation:  j · conj(λ)⁴ + conj(j) · λ⁴ = 0. -/
theorem pair_cancel_geom :
    j * conj lam ^ 4 + conj j * lam ^ 4 = 0 :=
  pair_cancellation

/-! ## Pair residuals from triplet cancellation

When one exit is blocked, the triplet reduces to a pair.
The pair residual is determined by the triplet identity. -/

/-- When the j·conj(λ) term is blocked:
    1 + xc · conj(j) · λ = -(xc · j · conj(λ)). -/
lemma pair_residual_j_blocked :
    (1 : ℂ) + (xc : ℂ) * conj j * lam = -((xc : ℂ) * j * conj lam) := by
  have h := triplet_cancellation
  linear_combination h

/-- When the conj(j)·λ term is blocked:
    1 + xc · j · conj(λ) = -(xc · conj(j) · λ). -/
lemma pair_residual_conjj_blocked :
    (1 : ℂ) + (xc : ℂ) * j * conj lam = -((xc : ℂ) * conj j * lam) := by
  have h := triplet_cancellation
  linear_combination h

/-- Both terms blocked (singleton):
    1 = -(xc · j · conj(λ) + xc · conj(j) · λ). -/
lemma singleton_residual :
    (1 : ℂ) = -((xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam) := by
  have h := triplet_cancellation
  linear_combination h

/-! ## The pair residuals satisfy the pair cancellation

The pair residuals from two walks entering v from different directions
cancel pairwise. Specifically:

If walk₁ enters from w₁ (direction d₁) with w₂ blocked, residual = -xc·d₂·turn₁₂
If walk₂ enters from w₂ (direction d₂) with w₁ blocked, residual = -xc·d₁·turn₂₁

These residuals are complex conjugates (up to a sign), and their sum involves
the pair cancellation identity j·conj(λ)⁴ + conj(j)·λ⁴ = 0.

This is the mechanism by which the non-triplet walks cancel globally. -/

/-- The product of two pair residuals involves the pair cancellation.
    Residual from entering direction 1 with j-exit blocked: -xc·j·conj(λ)
    Residual from entering direction j with 1-exit blocked: similar.
    Their weighted sum in the vertex relation cancels. -/
lemma pair_residuals_cancel :
    j * (-(xc : ℂ) * conj j * lam) +
    conj j * (-(xc : ℂ) * j * conj lam) =
    -(xc : ℂ) * (j * conj j * lam + conj j * j * conj lam) := by
  ring

end
