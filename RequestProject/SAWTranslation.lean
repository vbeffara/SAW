/-
# Translation invariance of bridge partition functions

This file proves that hexTranslate preserves key properties needed
for the Hammersley-Welsh bridge decomposition.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## diagCoord preservation under hexTranslate -/

/-- hexTranslate with dx+dy=0 preserves diagCoord. -/
lemma hexTranslate_preserves_diagCoord (dx dy : ℤ) (h : dx + dy = 0) (v : HexVertex) :
    (hexTranslate dx dy v).1 + (hexTranslate dx dy v).2.1 = v.1 + v.2.1 := by
  unfold hexTranslate; simp; linarith

/-- hexTranslate preserves sublattice type. -/
lemma hexTranslate_preserves_bool (dx dy : ℤ) (v : HexVertex) :
    (hexTranslate dx dy v).2.2 = v.2.2 := by
  unfold hexTranslate; simp

/-- hexTranslate with dx+dy=0 preserves PaperInfStrip membership. -/
lemma hexTranslate_preserves_strip' (dx dy : ℤ) (h : dx + dy = 0)
    (T : ℕ) (v : HexVertex) (hv : PaperInfStrip T v) :
    PaperInfStrip T (hexTranslate dx dy v) := by
  unfold PaperInfStrip at *
  unfold hexTranslate
  simp only
  rw [show (v.1 + dx + (v.2.1 + dy)) = v.1 + v.2.1 + (dx + dy) by ring, h, add_zero]
  rw [show (v.2.2) = (v.2.2) from rfl]
  exact hv

/-- hexTranslate (dx, -dx) sends paperStart to (dx, -dx, true). -/
lemma hexTranslate_paperStart (dx : ℤ) :
    hexTranslate dx (-dx) paperStart = (dx, -dx, true) := by
  unfold hexTranslate paperStart; simp

/-- The inverse of hexTranslate is hexTranslate with negated offsets. -/
lemma hexTranslate_neg_cancel (dx dy : ℤ) (v : HexVertex) :
    hexTranslate (-dx) (-dy) (hexTranslate dx dy v) = v := by
  unfold hexTranslate; ext <;> simp

/-! ## Walk translation -/

/-- Translate a walk by (dx, dy). -/
def translateWalk (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    hexGraph.Walk (hexTranslate dx dy v) (hexTranslate dx dy w) := by
  induction p with
  | nil => exact .nil
  | cons h _ ih =>
    exact .cons ((hexTranslate_adj dx dy _ _).mp h) ih

/-- Translation preserves walk length. -/
lemma translateWalk_length (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (translateWalk dx dy p).length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    show (SimpleGraph.Walk.cons _ (translateWalk dx dy _)).length = _
    simp [ih]

/-
Translation preserves path property.
-/
lemma translateWalk_isPath (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) : (translateWalk dx dy p).IsPath := by
  have h_support : ∀ {v w : HexVertex} (p : hexGraph.Walk v w), (translateWalk dx dy p).support = List.map (hexTranslate dx dy) p.support := by
    intros v w p; induction p <;> simp_all +decide [ translateWalk ] ;
  rw [ SimpleGraph.Walk.isPath_def ] at *;
  rw [ h_support, List.nodup_map_iff_inj_on ];
  · exact fun x hx y hy hxy => hexTranslate_injective dx dy hxy;
  · assumption

end