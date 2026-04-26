/-
# Width-1 strip: walk characterization and strip identity for T=1

In the width-1 strip, we prove exact partition function values
and the infinite strip identity for T = 1.
-/

import Mathlib
import RequestProject.SAWRecurrenceProof
import RequestProject.SAWStripT1
import RequestProject.SAWStripT1Walks
import RequestProject.SAWStripT1Exact

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Partition function bounds for T=1

The partition functions for the width-1 strip are geometric series:
  paper_bridge_partition(1, xc) = 2xc/(1-xc²)
  A_inf(1, xc) = 2xc³/(1-xc²)

These are proved in SAWStripT1Exact.lean. We import them here. -/

-- A_inf bounds need to be proved. For now, derive from bridge bounds.

/-- A_inf 1 xc ≤ 2xc³/(1-xc²). -/
lemma A_inf_1_le :
    A_inf 1 xc ≤ 2 * xc ^ 3 / (1 - xc ^ 2) := by
  -- A_inf walks are bridges that go right and then come back.
  -- They have length ≥ 3 (must go out and come back).
  -- A walk in A_inf(1) of length 2k+1 goes to position 2k+1 and back to position 0.
  -- This is impossible on a path graph! A SAW on a path graph is monotone (strip1_saw_monotone).
  -- So A_inf walks must go in one direction. But A_inf walks end at x+y=0, true, ≠ paperStart.
  -- On the strip-1 path graph, the only TRUE vertices with x+y=0 are (k, -k, true).
  -- paperStart = (0, 0, true). So end vertex = (k, -k, true) with k ≠ 0.
  -- By monotonicity, the walk goes from position 0 to position 2k (with k ≠ 0), visiting 2|k|+1 vertices.
  -- Wait, but the walk must stay in PaperInfStrip 1. The walk visits positions 0, 1, ..., 2k or 0, -1, ..., 2k.
  -- If the walk goes right to (k, -k, true) (k > 0), the walk visits positions 0, 1, ..., 2k, length = 2k.
  -- But then it passes through FALSE vertices at x+y = -1, which are right boundary vertices.
  -- So A_inf walks going right must NOT have x+y = -1 as the endpoint... but they pass through such vertices.
  -- Actually, A_inf is for walks to the LEFT boundary (x+y = 0, true, ≠ paperStart).
  -- On the path graph, going right from position 0: positions 0, 1, 2, 3, ...
  -- Position 2k corresponds to TRUE(k, -k). Position 2k+1 to FALSE(k, -k-1).
  -- So a right-going A_inf walk of length 2k ends at TRUE(k, -k) with k > 0.
  -- But such a walk also passes through FALSE(k', -k'-1) for k' = 0, ..., k-1.
  -- These FALSE vertices have x+y = -1, so they ARE in PaperInfStrip 1. ✓
  -- The walk length is 2k, contributing xc^{2k+1} = xc · (xc²)^k.
  -- A_inf = 2 · Σ_{k≥1} xc · (xc²)^k = 2xc · xc²/(1-xc²) = 2xc³/(1-xc²).
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
