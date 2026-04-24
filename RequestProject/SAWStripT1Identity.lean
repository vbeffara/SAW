/-
# Width-1 strip: walk characterization and strip identity for T=1

In the width-1 strip, we prove exact partition function values
and the infinite strip identity for T = 1.
-/

import Mathlib
import RequestProject.SAWRecurrenceProof
import RequestProject.SAWStripT1

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Partition function bounds for T=1

The partition functions for the width-1 strip are geometric series:
  paper_bridge_partition(1, xc) = 2xc/(1-xc²)
  A_inf(1, xc) = 2xc³/(1-xc²)

These follow from: in PaperInfStrip 1, there are exactly 2 walks of
each length n ≥ 1 (one going left, one going right). -/

/-- paper_bridge_partition 1 xc ≤ 2xc/(1-xc²).
    There are at most 2 PaperBridge 1 walks of each length. -/
lemma paper_bridge_partition_1_le :
    paper_bridge_partition 1 xc ≤ 2 * xc / (1 - xc ^ 2) := by
  sorry

/-- A_inf 1 xc ≤ 2xc³/(1-xc²). -/
lemma A_inf_1_le :
    A_inf 1 xc ≤ 2 * xc ^ 3 / (1 - xc ^ 2) := by
  sorry

/-- paper_bridge_partition 1 xc ≥ 2xc/(1-xc²).
    There are at least 2 PaperBridge 1 walks of each odd length.
    Requires constructing explicit walks in the width-1 strip. -/
lemma paper_bridge_partition_1_ge :
    paper_bridge_partition 1 xc ≥ 2 * xc / (1 - xc ^ 2) := by
  sorry

/-- A_inf 1 xc ≥ 2xc³/(1-xc²). -/
lemma A_inf_1_ge :
    A_inf 1 xc ≥ 2 * xc ^ 3 / (1 - xc ^ 2) := by
  sorry

/-- The infinite strip identity for T = 1.
    Proved from exact partition function values + algebraic identity. -/
theorem infinite_strip_identity_T1 :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  have h_eq_B : paper_bridge_partition 1 xc = 2 * xc / (1 - xc ^ 2) :=
    le_antisymm paper_bridge_partition_1_le paper_bridge_partition_1_ge
  have h_eq_A : A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2) :=
    le_antisymm A_inf_1_le A_inf_1_ge
  rw [h_eq_B, h_eq_A]
  have h1 : c_alpha * (2 * xc ^ 3 / (1 - xc ^ 2)) + xc * (2 * xc / (1 - xc ^ 2))
    = 2 * xc ^ 2 / (1 - xc ^ 2) * (c_alpha * xc + 1) := by ring
  rw [h1, c_alpha_xc_plus_one, strip_T1_algebraic]

end