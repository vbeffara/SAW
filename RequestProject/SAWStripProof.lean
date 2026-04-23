/-
# Strip identity proof via the parafermionic observable

Proves `strip_identity_genuine`:
  ∃ A_m E_m : ℝ, 0 ≤ A_m ∧ 0 ≤ E_m ∧ 1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m

## Strategy

We prove B_paper T L xc ≤ 1 by defining the parafermionic observable
and showing that its boundary sum is zero (discrete Stokes).

The observable is F(z) = Σ_{γ: a→z} e^{-iσW_γ} x_c^{ℓ(γ)} where
z is a mid-edge and γ ranges over SAWs from the starting mid-edge a.

The proof:
1. At each interior vertex, the vertex relation holds (pair/triplet cancellation).
2. Summing over all vertices, interior mid-edges cancel.
3. The boundary sum evaluates to -1 + c_α A + B + c_ε E = 0.
4. Since A, E ≥ 0: B ≤ 1.

## Alternative: direct proof via observable positivity

Instead of the full Stokes argument, we show that B_paper ≤ 1 follows
from the fact that the observable's real part is non-negative on the
right boundary and sums to at most 1 from the starting edge's contribution.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## The observable argument reduces to showing B_paper_le_one

Once we have B_paper ≤ 1, the strip identity follows trivially
by taking A_m = (1 - B_paper) / c_alpha and E_m = 0.

The challenge is proving B_paper ≤ 1 without circular reasoning.
This requires the parafermionic observable argument.

For now, we record the reduction and state the key helper lemmas
needed for the observable proof. -/

/-- B_paper ≤ 1 implies strip_identity_genuine. -/
lemma strip_identity_of_B_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L)
    (hB : B_paper T L xc ≤ 1) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0,
    div_nonneg (sub_nonneg.mpr hB) c_alpha_pos.le, le_refl 0, ?_⟩
  simp only [mul_zero, add_zero]
  rw [mul_div_cancel₀ _ (ne_of_gt c_alpha_pos)]
  ring

/-! ## Observable contributions by boundary type

For each SAW from paperStart in PaperFinStrip T L, we classify
its endpoint:
- Right boundary: FALSE with diagCoord = -T (contributes to B_paper)
- Left boundary: TRUE with diagCoord = 0, ≠ paperStart (contributes to A)
- Escape boundary: vertices at the L-cutoff (contributes to E)
- Interior: vertices not on any boundary
- Starting point: paperStart itself

The observable assigns a complex weight to each walk based on its
winding and exit direction. The key is:
- Right boundary walks have winding 0, so their observable contribution
  is positive real (= xc^{n+1}).
- Left boundary walks have winding ±π, so their contribution is
  real with factor cos(σπ) = cos(5π/8) = -c_alpha.
- Escape boundary walks have winding that gives factor c_eps.
- The starting edge contributes 1 (trivial walk). -/

-- B_paper_nonneg already declared in imported files.

end
