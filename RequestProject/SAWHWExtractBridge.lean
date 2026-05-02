/-
# Bridge Extraction Helpers

Helper lemmas connecting diagCoord bounds to the PaperInfStrip condition.
-/

import Mathlib
import RequestProject.SAWHWDecompHelper

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## diagCoord range implies PaperInfStrip -/

/-- If a FALSE vertex has diagCoord in [-T, -1], it satisfies PaperInfStrip T. -/
lemma false_in_strip {T : ℕ} (x y : ℤ)
    (hlow : -(T : ℤ) ≤ x + y) (hhigh : x + y ≤ -1) :
    PaperInfStrip T (x, y, false) := by
  unfold PaperInfStrip; simp; omega

/-- If a TRUE vertex has diagCoord in [-(T-1), 0], it satisfies PaperInfStrip T. -/
lemma true_in_strip {T : ℕ} (x y : ℤ)
    (hlow : -((T : ℤ) - 1) ≤ x + y) (hhigh : x + y ≤ 0) :
    PaperInfStrip T (x, y, true) := by
  unfold PaperInfStrip; simp; omega

end
