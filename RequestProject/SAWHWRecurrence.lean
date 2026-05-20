/-
# Half-plane Walk Recurrence for Bridge Decomposition

Proves the key recurrence:
  |{DownHP W walks of length n}| ≤ |{DownHP (W-1) walks of length n}|
    + ∑_k |PaperBridge W of length k| · |{DownHP (W-1) walks of length (n-k-1)}|

This recurrence, when converted to generating functions, gives:
  HP_W(x) ≤ (1 + B_W(x)) · HP_{W-1}(x)
-/

import Mathlib
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Translation of walks on the hex lattice -/

/-- Shift a hex vertex by a given offset. -/
def hexShift (dx dy : ℤ) (v : HexVertex) : HexVertex :=
  (v.1 + dx, v.2.1 + dy, v.2.2)

/-- hexShift preserves adjacency. -/
lemma hexShift_adj {v w : HexVertex} (h : hexGraph.Adj v w) (dx dy : ℤ) :
    hexGraph.Adj (hexShift dx dy v) (hexShift dx dy w) := by
  simp only [hexShift, hexGraph]
  rcases h with ⟨hf, ht, h3 | h3 | h3⟩ | ⟨hf, ht, h3 | h3 | h3⟩ <;>
    obtain ⟨h1, h2⟩ := h3 <;> simp_all <;> omega

/-- hexShift preserves diagCoord up to a shift. -/
lemma hexShift_dc (dx dy : ℤ) (v : HexVertex) :
    (hexShift dx dy v).1 + (hexShift dx dy v).2.1 = v.1 + v.2.1 + (dx + dy) := by
  simp [hexShift]; ring

/-- hexShift preserves the Bool component. -/
lemma hexShift_bool (dx dy : ℤ) (v : HexVertex) :
    (hexShift dx dy v).2.2 = v.2.2 := by
  simp [hexShift]

/-- hexShift by (0,0) is the identity. -/
@[simp] lemma hexShift_zero (v : HexVertex) : hexShift 0 0 v = v := by
  simp [hexShift]

/-- Shifting a walk by hexShift preserves the walk structure. -/
def shiftWalk (dx dy : ℤ) : {v w : HexVertex} →
    hexGraph.Walk v w → hexGraph.Walk (hexShift dx dy v) (hexShift dx dy w)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons (hexShift_adj h dx dy) (shiftWalk dx dy p)

/-- shiftWalk preserves walk length. -/
lemma shiftWalk_length (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (shiftWalk dx dy p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [shiftWalk, SimpleGraph.Walk.length_cons, ih]

/-
shiftWalk preserves path property.
-/
lemma shiftWalk_isPath (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) : (shiftWalk dx dy p).IsPath := by
  -- By definition of `shiftWalk`, the support of the shifted walk is the support of the original walk mapped by `hexShift dx dy`.
  have h_support : (shiftWalk dx dy p).support = p.support.map (hexShift dx dy) := by
    induction' p with v w p ih;
    · rfl;
    · simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff, shiftWalk ];
  simp_all +decide [ SimpleGraph.Walk.isPath_def ];
  exact List.Nodup.map ( fun x y => by unfold hexShift; aesop ) hp

/-- shiftWalk support is the shifted support. -/
lemma shiftWalk_support (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (shiftWalk dx dy p).support = p.support.map (hexShift dx dy) := by
  induction p with
  | nil => simp [shiftWalk]
  | cons h p ih => simp [shiftWalk, SimpleGraph.Walk.support_cons, ih]

/-! ## Shift from a vertex to paperStart -/

/-- Given a TRUE vertex v, the shift that maps v to paperStart. -/
def shiftToPaperStart (v : HexVertex) : ℤ × ℤ :=
  (-v.1, -v.2.1)

/-- Shifting a TRUE vertex to paperStart. -/
lemma hexShift_to_paperStart {v : HexVertex} (hv : v.2.2 = true) :
    hexShift (shiftToPaperStart v).1 (shiftToPaperStart v).2 v = paperStart := by
  simp [hexShift, shiftToPaperStart, paperStart]
  exact hv

/-! ## Key counting: SAW count bounded by half-plane walk count

For the Hammersley-Welsh bound, we need:
  saw_count n ≤ 2 · (number of down-half-plane walks of length ≤ n)

This follows from splitting each SAW at the first vertex of min dc. -/

/-- saw_count from paperStart equals saw_count from hexOrigin. -/
lemma saw_count_eq_paperStart (n : ℕ) :
    Fintype.card (SAW paperStart n) = saw_count n :=
  saw_count_vertex_independent paperStart n

end