/-
# Hammersley-Welsh Bridge Decomposition — Step-by-Step

Building blocks for the bridge decomposition proof.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWReCoord
import RequestProject.SAWHWBound

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Last vertex at min dc -/

/-
In any non-empty walk on hex lattice where the walk stays in dc ∈ [-M, 0],
    if v is a vertex at dc = -M and no later vertex (by walk order) also has dc = -M,
    then v is FALSE. (If v were TRUE at dc=-M, the next step goes to FALSE at dc≤-M,
    but dc≥-M forces dc=-M, giving a later vertex at dc=-M, contradiction.)
-/
lemma last_at_min_dc_is_false {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (M : ℕ) (hM : 1 ≤ M)
    (hv_dc : v.1 + v.2.1 = 0) (hv_true : v.2.2 = true)
    (hstrip : ∀ u ∈ p.support, -(M : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (z : HexVertex) (hz : z ∈ p.support)
    (hz_dc : z.1 + z.2.1 = -(M : ℤ))
    (hz_ne_w : z ≠ w)
    (hz_last : ∀ u ∈ p.support,
      u.1 + u.2.1 = -(M : ℤ) → u ≠ z →
      -- u appears before z in the walk
      True) :
    z.2.2 = false := by
  have h_no_true_at_min : ∀ u ∈ p.support, u.2.2 = true → u.1 + u.2.1 > -M ∨ u = w := by
    intros u hu hu_true
    by_cases hu_last : u = w;
    · exact Or.inr hu_last;
    · apply Classical.byContradiction
      intro h_contra;
      exact absurd ( no_true_at_min_dc_in_strip p hp M hM ( by linarith ) hstrip u hu hu_true hu_last ) ( by aesop );
  grind

/-- In a downward half-plane walk from paperStart (all dc ∈ [-M, 0]),
    any vertex at dc = -M that is not the walk endpoint must be FALSE.
    (This uses the bipartite structure: TRUE at dc=-M would force visiting
    FALSE at same dc, but self-avoidance limits the neighbors.) -/
lemma min_dc_vertex_is_false_in_hp
    {w : HexVertex}
    (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (M : ℕ) (hM : 1 ≤ M)
    (hstrip : ∀ u ∈ p.support, -(M : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (v : HexVertex) (hv : v ∈ p.support)
    (hv_dc : v.1 + v.2.1 = -(M : ℤ))
    (hv_ne_w : v ≠ w) :
    v.2.2 = false := by
  by_contra h
  have hv_true : v.2.2 = true := by
    cases hb : v.2.2 <;> simp_all
  have hstart : paperStart.1 + paperStart.2.1 > -(M : ℤ) := by simp [paperStart]; omega
  have hgt := no_true_at_min_dc_in_strip p hp M hM hstart hstrip v hv hv_true hv_ne_w
  linarith

/-! ## Prefix to a min-dc FALSE vertex is a PaperBridge -/

/-- The prefix of a downward half-plane walk to a FALSE vertex at dc=-M
    is a valid PaperBridge of width M. This uses bridge_satisfies_paper_inf_strip. -/
lemma hp_prefix_is_bridge
    {w : HexVertex}
    (p : hexGraph.Path paperStart w) (M : ℕ) (hM : 1 ≤ M)
    (hstrip : ∀ u ∈ p.1.support, -(M : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (v : HexVertex) (hv : v ∈ p.1.support)
    (hv_dc : v.1 + v.2.1 = -(M : ℤ))
    (hv_false : v.2.2 = false) :
    ∃ (b : PaperBridge M), b.walk.1.length = (p.1.takeUntil v hv).length := by
  exact prefix_to_first_min_is_bridge p M hM v hv hv_dc hv_false
    (fun u hu => hstrip u (p.1.support_takeUntil_subset hv hu))

/-! ## After the min-dc vertex, dc increases -/

/-
If v is FALSE at dc=-M in a walk, and u is the next vertex after v,
    then u is TRUE with dc = -(M-1). This is because all FALSE neighbors
    of FALSE(a,b) with dc=-M are TRUE, and the only TRUE neighbor at
    dc ≤ -M is TRUE(a,b) at dc=-M (which violates PaperInfStrip).
-/
lemma next_after_min_dc_false
    {a b : ℤ} {u : HexVertex}
    (h_adj : hexGraph.Adj (a, b, false) u)
    (h_dc : a + b = -(M : ℤ))
    (h_strip : -(M : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (h_not_same : u ≠ (a, b, true)) :
    u.1 + u.2.1 = -(M : ℤ) + 1 := by
  cases u ; simp_all +decide [ hexGraph ];
  grind

/-! ## The Hammersley-Welsh inequality -/

/-- The Hammersley-Welsh bridge decomposition inequality.
    For all 0 < x ≤ 1 and N ≥ 0:
    ∑_{n=0}^{N} c_n x^n ≤ 2 ∏_{T=1}^{N} (1 + B_T(x))² -/
theorem hw_injection_bound_v2 {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 := by
  sorry

end