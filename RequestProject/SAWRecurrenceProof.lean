/-
# Bridge recurrence from the infinite strip identity

Derives the quadratic recurrence for bridges from:
1. The infinite strip identity: 1 = c_α · A_inf(T) + xc · B(T)
2. The cutting argument: A_inf(T+1) - A_inf(T) ≤ xc · B(T+1)²

The infinite strip identity follows from the parafermionic observable
argument (Lemma 2 of Duminil-Copin & Smirnov 2012) applied to the
infinite strip S_T. In the infinite strip, there is NO escape boundary
(the strip extends infinitely in both directions), so E = 0 and the
identity simplifies to 1 = c_α · A + xc · B.
-/

import Mathlib
import RequestProject.SAWCuttingProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## The infinite strip identity

For the infinite strip S_T with T ≥ 1, the parafermionic observable gives:
  1 = c_α · A_inf(T, xc) + xc · paper_bridge_partition(T, xc)

**Proof outline:**
1. Define F(z) at each mid-edge z of S_T.
2. The vertex relation (Lemma 1) holds at each vertex v ∈ V(S_T).
3. Sum over all vertices (discrete Stokes): interior mid-edges cancel.
4. Only LEFT boundary (diagCoord = 0) and RIGHT boundary (diagCoord = -T)
   mid-edges survive. There is NO escape boundary in the infinite strip.
5. Boundary evaluation:
   - Starting mid-edge a: F(a) = 1, direction factor = -1, contributes -1.
   - Left boundary (diagCoord = 0, TRUE, ≠ paperStart): winding = ±π,
     so Re(exp(-iσπ)) = -cos(5π/8) = cos(3π/8) = c_α. Contributes c_α · A_inf.
   - Right boundary (diagCoord = -T, FALSE): winding = 0,
     so exp(-iσ·0) = 1. Contributes xc · paper_bridge_partition
     (the factor xc converts from edge-weight to vertex-weight).
6. Total: 0 = -1 + c_α · A_inf + xc · paper_bridge_partition.

**Status: sorry.** This is a consequence of the vertex relation (Lemma 1)
applied to the infinite strip. The algebraic ingredients (pair_cancellation,
triplet_cancellation) are proved. The combinatorial walk partitioning and
discrete Stokes summation remain to be formalized.
-/
lemma infinite_strip_identity (T : ℕ) (hT : 1 ≤ T) :
    1 = c_alpha * A_inf T xc + xc * paper_bridge_partition T xc := by
  sorry

/-! ## No PaperBridge of width 0

A PaperBridge 0 requires end_v with diagCoord = 0 and FALSE sublattice.
But PaperInfStrip 0 only allows FALSE vertices with -0 ≤ d ≤ -1, which
is empty. So PaperBridge 0 is empty. -/

lemma paperBridge_zero_empty (b : PaperBridge 0) : False := by
  have hend := b.end_right
  have hstrip := b.in_strip b.end_v (b.walk.1.end_mem_support)
  unfold PaperInfStrip at hstrip
  simp [hend.2] at hstrip
  omega

instance : IsEmpty (PaperBridge 0) := ⟨fun b => paperBridge_zero_empty b⟩

lemma paper_bridge_partition_zero : paper_bridge_partition 0 xc = 0 := by
  simp [paper_bridge_partition, tsum_empty]

/-! ## Derivation of the bridge recurrence

From the infinite strip identity and the cutting argument, we derive
the quadratic recurrence for the bridge partition function. -/

/-- Key algebraic step: B(T) - B(T+1) = c_α/xc · (A(T+1) - A(T)). -/
lemma bridge_diff_eq (T : ℕ) (hT : 1 ≤ T) :
    paper_bridge_partition T xc - paper_bridge_partition (T + 1) xc =
    c_alpha / xc * (A_inf (T + 1) xc - A_inf T xc) := by
  have h1 := infinite_strip_identity T hT
  have h2 := infinite_strip_identity (T + 1) (by omega)
  have hxc : xc ≠ 0 := ne_of_gt xc_pos
  field_simp
  linarith

/-- The bridge recurrence: B(T) ≤ c_α · B(T+1)² + B(T+1).

    Proof:
    B(T) - B(T+1) = c_α/xc · (A(T+1) - A(T))  [from identity]
                   ≤ c_α/xc · xc · B(T+1)²      [from cutting argument]
                   = c_α · B(T+1)²
    Therefore B(T) ≤ c_α · B(T+1)² + B(T+1). -/
theorem bridge_recurrence_proved (T : ℕ) (hT : 1 ≤ T) :
    paper_bridge_partition T xc ≤
    c_alpha * paper_bridge_partition (T + 1) xc ^ 2 +
    paper_bridge_partition (T + 1) xc := by
  have hdiff := bridge_diff_eq T hT
  have hcut := cutting_argument_proved T hT
  have hxc_pos := xc_pos
  have hca_pos := c_alpha_pos
  have h_diff_le : paper_bridge_partition T xc - paper_bridge_partition (T + 1) xc ≤
      c_alpha * paper_bridge_partition (T + 1) xc ^ 2 := by
    rw [hdiff]
    have h1 : c_alpha / xc * (A_inf (T + 1) xc - A_inf T xc) ≤
           c_alpha / xc * (xc * paper_bridge_partition (T + 1) xc ^ 2) :=
      mul_le_mul_of_nonneg_left hcut (div_nonneg hca_pos.le hxc_pos.le)
    calc c_alpha / xc * (A_inf (T + 1) xc - A_inf T xc)
        ≤ c_alpha / xc * (xc * paper_bridge_partition (T + 1) xc ^ 2) := h1
      _ = c_alpha * paper_bridge_partition (T + 1) xc ^ 2 := by
          field_simp
  linarith

/-- The bridge recurrence in existential form (matching paper_bridge_recurrence). -/
theorem paper_bridge_recurrence_derived :
    ∃ α > 0, ∀ T : ℕ,
      paper_bridge_partition T xc ≤ α * paper_bridge_partition (T + 1) xc ^ 2 +
        paper_bridge_partition (T + 1) xc := by
  refine ⟨c_alpha, c_alpha_pos, fun T => ?_⟩
  by_cases hT : 1 ≤ T
  · exact bridge_recurrence_proved T hT
  · push_neg at hT
    interval_cases T
    rw [paper_bridge_partition_zero]
    exact add_nonneg
      (mul_nonneg c_alpha_pos.le (sq_nonneg _))
      (tsum_nonneg fun _ => pow_nonneg xc_pos.le _)

end
