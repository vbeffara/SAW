/-
# Cutting argument for the bridge recurrence

The cutting argument from Section 3 of Duminil-Copin & Smirnov (2012):
A walk from the left boundary of S_{T+1} to the left boundary
that reaches the right boundary of S_{T+1} (but not of S_T)
can be cut at the first point reaching the right boundary,
giving two bridges of width T+1.

This gives: A_{T+1} - A_T ≤ xc · B_{T+1}²

Combined with the strip identity 1 = c_α·A_T + B_T + c_ε·E_T:
B_T ≤ c_α·xc · B_{T+1}² + B_{T+1}

This is the quadratic recurrence.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Infinite strip walks -/

/-- A walk from paperStart to a LEFT boundary vertex (TRUE, diagCoord = 0)
    that is NOT paperStart, staying in PaperInfStrip T. -/
structure PaperSAW_A_inf (T : ℕ) where
  end_v : HexVertex
  walk : hexGraph.Path paperStart end_v
  end_left : end_v.1 + end_v.2.1 = 0 ∧ end_v.2.2 = true ∧ end_v ≠ paperStart
  in_strip : ∀ v ∈ walk.1.support, PaperInfStrip T v

/-- Partition function for walks to the left boundary in the infinite strip. -/
def A_inf (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : PaperSAW_A_inf T), x ^ (s.walk.1.length + 1)

/-- A_inf is non-negative. -/
lemma A_inf_nonneg (T : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_inf T x :=
  tsum_nonneg fun s => pow_nonneg hx _

/-! ## Cutting argument

A walk from paperStart to the left boundary in S_{T+1} that reaches
diagCoord -(T+1) can be cut at the first such vertex, giving two bridges.
-/

/-- A walk in A_inf (T+1) that is NOT in A_inf T must reach diagCoord -(T+1). -/
lemma A_inf_diff_reaches_boundary {T : ℕ} (s : PaperSAW_A_inf (T + 1))
    (h_not_in_T : ¬ ∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    ∃ v ∈ s.walk.1.support, v.1 + v.2.1 = -(T + 1 : ℤ) ∧ v.2.2 = false := by
  sorry

/-- Cutting a walk at the first vertex with diagCoord -(T+1)
    gives two bridges of width T+1. The product of their lengths
    is at most the walk length - 1 (we lose one connecting vertex).

    A_{T+1} - A_T ≤ xc · B_{T+1}² -/
lemma cutting_argument (T : ℕ) (hT : 1 ≤ T) :
    A_inf (T + 1) xc - A_inf T xc ≤
    xc * paper_bridge_partition (T + 1) xc ^ 2 := by
  sorry

/-! ## The recurrence from strip identity + cutting

The quadratic recurrence follows from:
1. Strip identity: 1 = c_α · A_inf T xc + paper_bridge_partition T xc + c_ε · E_inf T xc
2. A_{T+1} - A_T ≤ xc · B_{T+1}² (cutting argument)
3. E_{T+1} ≤ E_T (monotonicity of escape partition function)

Subtracting strip identity at T and T+1:
0 = c_α · (A_{T+1} - A_T) + (B_{T+1} - B_T) + c_ε · (E_{T+1} - E_T)

Since E_{T+1} ≤ E_T: c_ε · (E_{T+1} - E_T) ≤ 0
So: B_T - B_{T+1} ≤ c_α · (A_{T+1} - A_T)
And: B_T - B_{T+1} ≤ c_α · xc · B_{T+1}²
Therefore: B_T ≤ c_α · xc · B_{T+1}² + B_{T+1}
-/

/-- The recurrence from strip identity + cutting.
    This is an alternative proof of paper_bridge_recurrence that
    makes the dependency on the strip identity explicit. -/
theorem bridge_recurrence_from_identity
    (h_strip : ∀ T : ℕ, 1 ≤ T →
      paper_bridge_partition T xc ≤ 1 / xc)
    (h_cut : ∀ T : ℕ, 1 ≤ T →
      A_inf (T + 1) xc - A_inf T xc ≤ xc * paper_bridge_partition (T + 1) xc ^ 2) :
    ∃ α > 0, ∀ T : ℕ,
      paper_bridge_partition T xc ≤ α * paper_bridge_partition (T + 1) xc ^ 2 +
        paper_bridge_partition (T + 1) xc := by
  sorry

end
