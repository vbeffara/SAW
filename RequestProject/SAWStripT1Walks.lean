/-
# Walk characterization in the width-1 strip
-/

import Mathlib
import RequestProject.SAWRecurrenceProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Bipartiteness -/

/-- A walk from TRUE to FALSE has odd length. -/
lemma walk_true_to_false_odd {v w : HexVertex} (p : hexGraph.Walk v w)
    (hv : v.2.2 = true) (hw : w.2.2 = false) : Odd p.length := by
  contrapose! hv;
  have h_parity : ∀ {v w : HexVertex} (p : hexGraph.Walk v w), v.2.2 ≠ w.2.2 ↔ Odd p.length := by
    intros v w p;
    induction p <;> simp_all +decide [ parity_simps ];
    rename_i u v w huv p ih; cases huv; simp_all +decide [ parity_simps ] ;
    grind;
  grind

/-- Every PaperBridge 1 has odd walk length. -/
lemma paper_bridge_1_odd_length (b : PaperBridge 1) : Odd b.walk.1.length :=
  walk_true_to_false_odd b.walk.1
    (show paperStart.2.2 = true from rfl) b.end_right.2

/-! ## xc² < 1 -/

lemma xc_sq_lt_one : xc ^ 2 < 1 := by
  have : xc < 1 := xc_lt_one'
  nlinarith [xc_pos]

lemma one_sub_xc_sq_pos : 0 < 1 - xc ^ 2 := by linarith [xc_sq_lt_one]

/-! ## Explicit bridges -/

/-- Right bridge of length 1: paperStart → (0, -1, false). -/
def rightBridge0 : PaperBridge 1 where
  end_v := ((0 : ℤ), (-1 : ℤ), false)
  walk := ⟨.cons (by right; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, by decide⟩)⟩ :
    hexGraph.Adj paperStart ((0 : ℤ), (-1 : ℤ), false)) .nil,
    by simp [SimpleGraph.Walk.cons_isPath_iff, paperStart]⟩
  end_right := ⟨by decide, rfl⟩
  in_strip := by
    intro v hv; simp [SimpleGraph.Walk.support, paperStart] at hv
    rcases hv with rfl | rfl <;> (unfold PaperInfStrip; simp)

/-- Left bridge of length 1: paperStart → (-1, 0, false). -/
def leftBridge0 : PaperBridge 1 where
  end_v := ((-1 : ℤ), (0 : ℤ), false)
  walk := ⟨.cons (by right; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by decide, rfl⟩)⟩ :
    hexGraph.Adj paperStart ((-1 : ℤ), (0 : ℤ), false)) .nil,
    by simp [SimpleGraph.Walk.cons_isPath_iff, paperStart]⟩
  end_right := ⟨by decide, rfl⟩
  in_strip := by
    intro v hv; simp [SimpleGraph.Walk.support, paperStart] at hv
    rcases hv with rfl | rfl <;> (unfold PaperInfStrip; simp)

/-! ## Width-1 strip: neighbor characterization -/

/-- In PaperInfStrip 1, a TRUE vertex has exactly 2 strip-neighbors. -/
lemma strip1_true_neighbors (k : ℤ) :
    ∀ w : HexVertex, hexGraph.Adj ((k : ℤ), -k, true) w → PaperInfStrip 1 w →
      w = ((k : ℤ), -k-1, false) ∨ w = (k-1, -k, false) := by
  unfold hexGraph PaperInfStrip at *;
  grind

/-- In PaperInfStrip 1, a FALSE vertex has exactly 2 strip-neighbors. -/
lemma strip1_false_neighbors (k : ℤ) :
    ∀ w : HexVertex, hexGraph.Adj ((k : ℤ), -k-1, false) w → PaperInfStrip 1 w →
      w = ((k : ℤ), -k, true) ∨ w = (k+1, -(k+1), true) := by
  rintro w hw hw'; unfold hexGraph at hw; simp_all +decide [ PaperInfStrip ] ;
  grind

/-
paperStart has exactly 2 strip-neighbors in PaperInfStrip 1.
-/
lemma paperStart_strip1_neighbors :
    ∀ w : HexVertex, hexGraph.Adj paperStart w → PaperInfStrip 1 w →
      w = ((0 : ℤ), (-1 : ℤ), false) ∨ w = ((-1 : ℤ), (0 : ℤ), false) := by
  exact strip1_true_neighbors 0

/-! ## Classification of length-1 bridges -/

/-
Every PaperBridge 1 of length 1 is either rightBridge0 or leftBridge0.
-/
lemma paper_bridge_1_length1_classification (b : PaperBridge 1)
    (hlen : b.walk.1.length = 1) :
    b = rightBridge0 ∨ b = leftBridge0 := by
  rcases b with ⟨ end_v, walk, end_right, in_strip ⟩;
  rcases walk with ( _ | ⟨ _, _, walk ⟩ ) <;> simp_all +decide;
  cases paperStart_strip1_neighbors end_v ‹_› ( by tauto ) <;> aesop

end