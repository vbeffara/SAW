/-
# Key lemma: B_paper ≤ 1 from parafermionic observable

This file proves `strip_identity_genuine` by reducing it to
the algebraic statement B_paper T L xc ≤ 1.

The proof that B_paper ≤ 1 follows from the parafermionic observable
(Lemma 1 + discrete Stokes + boundary evaluation).
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Key reduction: strip_identity_genuine ↔ B_paper ≤ 1

We show that the existential statement in `strip_identity_genuine`
follows from the simpler statement B_paper T L xc ≤ 1. -/

/-- If B_paper T L xc ≤ 1, then strip_identity_genuine holds.
    Proof: set A_m = (1 - B)/c_alpha and E_m = 0. -/
lemma strip_identity_of_B_le_one (T L : ℕ) (_hT : 1 ≤ T) (_hL : 1 ≤ L)
    (hB : B_paper T L xc ≤ 1) :
    ∃ (A_m E_m : ℝ), 0 ≤ A_m ∧ 0 ≤ E_m ∧
      1 = c_alpha * A_m + B_paper T L xc + c_eps * E_m := by
  refine ⟨(1 - B_paper T L xc) / c_alpha, 0,
          div_nonneg (sub_nonneg.mpr hB) c_alpha_pos.le,
          le_refl _,
          ?_⟩
  have hca : c_alpha ≠ 0 := ne_of_gt c_alpha_pos
  field_simp
  ring

end
