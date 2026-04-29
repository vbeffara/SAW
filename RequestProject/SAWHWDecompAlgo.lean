/-
# Helper lemmas for the bridge decomposition

Key infrastructure for the Hammersley-Welsh argument.
-/

import Mathlib
import RequestProject.SAWBridgeDecompCore
import RequestProject.SAWHWAlgorithm

open Real Filter Topology

noncomputable section

/-! ## PaperInfStrip monotonicity in width -/

/-- PaperInfStrip is monotone in the width parameter. -/
lemma PaperInfStrip_mono_width {v : HexVertex} {T T' : ℕ}
    (h : PaperInfStrip T v) (hT : T ≤ T') :
    PaperInfStrip T' v := by
  unfold PaperInfStrip at *
  cases hb : v.2.2 <;> simp_all <;> omega

/-! ## Walk diagonal coordinate bounds -/

/-- Walk dc stays within ±length of start. -/
lemma walk_dc_bound {v w : HexVertex} (p : hexGraph.Walk v w) (u : HexVertex)
    (hu : u ∈ p.support) :
    |hexDiagCoord u - hexDiagCoord v| ≤ p.length := by
  induction' p with v w p ih generalizing u;
  · aesop;
  · cases hu;
    · exact le_trans ( by norm_num ) ( Nat.cast_nonneg _ );
    · rename_i h₁ h₂ h₃;
      have := hexDiagCoord_adj_bound ‹_›;
      exact abs_le.mpr ⟨ by norm_num; linarith [ abs_le.mp ( h₂ u h₃ ), abs_le.mp this ], by norm_num; linarith [ abs_le.mp ( h₂ u h₃ ), abs_le.mp this ] ⟩

/-- The endpoint's dc is within ±length of the start's dc. -/
lemma walk_endpoint_dc_bound {v w : HexVertex} (p : hexGraph.Walk v w) :
    |hexDiagCoord w - hexDiagCoord v| ≤ p.length :=
  walk_dc_bound p w p.end_mem_support

/-- For a SAW from paperStart, every vertex has dc ≥ -n. -/
lemma saw_dc_lower {n : ℕ} (s : SAW paperStart n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) :
    -(n : ℤ) ≤ hexDiagCoord v := by
  have h := walk_dc_bound s.p.1 v hv
  unfold hexDiagCoord paperStart at h
  simp at h
  rw [s.l] at h
  unfold hexDiagCoord
  linarith [(abs_le.mp h).1]

/-- For a SAW from paperStart, every vertex has dc ≤ n. -/
lemma saw_dc_upper {n : ℕ} (s : SAW paperStart n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) :
    hexDiagCoord v ≤ (n : ℤ) := by
  have h := walk_dc_bound s.p.1 v hv
  unfold hexDiagCoord paperStart at h
  simp at h
  rw [s.l] at h
  unfold hexDiagCoord
  linarith [(abs_le.mp h).2]

/-- The walk has exactly n+1 vertices in its support. -/
lemma saw_support_length {start : HexVertex} {n : ℕ} (s : SAW start n) :
    s.p.1.support.length = n + 1 := by
  rw [SimpleGraph.Walk.length_support, s.l]

/-! ## Bridge translation invariance -/

/-- Translation preserves walk length for shifted walks. -/
lemma shiftWalk_length' (dx dy : ℤ) {v w : HexVertex}
    (p : hexGraph.Walk v w) :
    (shiftWalk dx dy p).length = p.length :=
  shiftWalk_length dx dy p

end
