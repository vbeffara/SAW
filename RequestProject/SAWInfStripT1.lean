/-
# Infinite strip identity for T = 1

Proves 1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc
directly from the T=1 algebraic structure, without using the general
sorry'd `infinite_strip_identity`.

The width-1 strip is a path graph, so all partition functions can be
computed as geometric series.

## Status
- paper_bridge_partition_1_eq: proved (exact value 2xc/(1-xc²))
- A_inf_1_exact: proved
- infinite_strip_identity_T1_clean: proved FROM A_inf_1_exact (algebraic)

The A_inf_1_exact computation requires showing that PaperSAW_A_inf 1
walks biject with {left, right} × ℕ+ via the strip-1 path graph
structure (strip1_saw_monotone).
-/

import Mathlib
import RequestProject.SAWStripT1Exact
import RequestProject.SAWStripT1
import RequestProject.SAWCutting

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## A_inf for T=1: walks to the left boundary in the infinite strip

PaperSAW_A_inf 1 walks are SAWs from paperStart = (0,0,TRUE) to a
TRUE vertex at d=0 that is ≠ paperStart, staying in PaperInfStrip 1.

In PaperInfStrip 1, the graph is a path:
  ... TRUE(-1,1) - FALSE(-1,0) - TRUE(0,0) - FALSE(0,-1) - TRUE(1,-1) - ...

By monotonicity (strip1_saw_monotone), every SAW goes entirely left or
entirely right. A walk of length 2k (k ≥ 1) ends at TRUE(±k, ∓k).

So A_inf 1 xc = 2 · Σ_{k=1}^∞ xc^{2k+1} = 2xc³/(1-xc²). -/

/-
A_inf 1 xc = 2xc³/(1-xc²).
    **Status: sorry.** Requires enumerating PaperSAW_A_inf 1 walks
    using the strip-1 path graph structure. Must NOT use the general
    sorry'd `infinite_strip_identity`.
-/
theorem A_inf_1_exact :
    A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2) := by
  have := @strip_identity_genuine 1 1 ; norm_num at *;
  have := @paper_bridge_partition_1_eq; norm_num at *;
  grind +suggestions

/-- The infinite strip identity for T = 1, proved from exact values.
    Does NOT use the general (sorry'd) infinite_strip_identity. -/
theorem infinite_strip_identity_T1_clean :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  rw [A_inf_1_exact, paper_bridge_partition_1_eq]
  have h1 : c_alpha * (2 * xc ^ 3 / (1 - xc ^ 2)) + xc * (2 * xc / (1 - xc ^ 2))
    = 2 * xc ^ 2 / (1 - xc ^ 2) * (c_alpha * xc + 1) := by ring
  rw [h1, c_alpha_xc_plus_one, strip_T1_algebraic]

end