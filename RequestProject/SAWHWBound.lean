/-
# Hammersley-Welsh Bridge Decomposition: Helper Infrastructure

Helper lemmas for the bridge decomposition proof.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWReCoord

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Walk dc bounds -/

/-- Each vertex in a walk of length n from paperStart has dc in [-n, n]. -/
lemma saw_vertex_dc_bound {n : ℕ} (s : SAW paperStart n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) :
    -(n : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ n := by
  have hlen : (s.p.1.takeUntil v hv).length ≤ n :=
    (s.p.1.length_takeUntil_le hv).trans (le_of_eq s.l)
  have h1 := hexGraph_walk_sum_bound_neg (s.p.1.takeUntil v hv)
  have h2 := hexGraph_walk_sum_bound_pos (s.p.1.takeUntil v hv)
  simp [paperStart] at h1 h2
  constructor <;> linarith [show ((s.p.1.takeUntil v hv).length : ℤ) ≤ n from by exact_mod_cast hlen]

/-! ## hexFlip preserves bridge structure -/

/-- hexFlip maps diagCoord d to -d. -/
lemma hexFlip_dc (v : HexVertex) : (hexFlip v).1 + (hexFlip v).2.1 = -(v.1 + v.2.1) := by
  simp [hexFlip]; ring

/-- hexFlip is an involution. -/
lemma hexFlip_involution (v : HexVertex) : hexFlip (hexFlip v) = v := by
  simp [hexFlip, Bool.not_not]

/-- hexFlip maps paperStart to hexOrigin. -/
lemma hexFlip_paperStart : hexFlip paperStart = hexOrigin := by
  simp [hexFlip, paperStart, hexOrigin]

/-- hexFlip maps hexOrigin to paperStart. -/
lemma hexFlip_hexOrigin : hexFlip hexOrigin = paperStart := by
  simp [hexFlip, paperStart, hexOrigin]

/-- The product formula: ∏(1+aₜ) = ∑_{S⊂range N} ∏_{t∈S} aₜ -/
lemma prod_one_add_eq (N : ℕ) (a : ℕ → ℝ) :
    ∏ T ∈ Finset.range N, (1 + a T) =
    ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, a T := by
  simp [add_comm, Finset.prod_add]

/-- paper_bridge_partition is nonneg for x > 0. -/
lemma paper_bridge_partition_nonneg' (T : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ paper_bridge_partition T x :=
  tsum_nonneg fun _ => pow_nonneg hx.le _

end
