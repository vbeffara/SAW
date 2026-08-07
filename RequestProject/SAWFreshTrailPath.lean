/-
# Fresh trails in the strip are self-avoiding walks

The observable `freshObs T L prev next` sums over `FreshTrail`s, i.e. over
*trails* (no repeated edge) rather than over *paths* (no repeated vertex).  On
the honeycomb lattice these two notions almost coincide, and this file makes
that precise for the strip:

**Main result** (`freshTrail_isPath`): if `prev ≠ paperStart`, then the walk of
any `FreshTrail T L prev next` is a path, i.e. a self-avoiding walk.

The proof is a degree count.  At a degree-3 vertex a trail uses an odd number of
incident edges at each of its two (distinct) endpoints and an even number
elsewhere.

* at the terminal vertex `prev` the freshness of `s(prev, next)` leaves at most
  two usable edges, so the count is exactly `1`;
* at `paperStart` the third neighbour is `hexOrigin`, which lies outside the
  strip, so again at most two edges are usable and the count is exactly `1`.

`hex_trail_is_path_of_endpoint_bounds` then upgrades the trail to a path.

This is the structural input for the boundary evaluation of the strip identity
(`bdry_A_eval`, `bdry_B_eval` in `SAWStripBoundarySum.lean`): it is what
identifies the fresh trails ending on a boundary mid-edge with the
self-avoiding walks counted by `A_paper` and `B_paper`.
-/

import Mathlib
import RequestProject.SAWVertexRelationProof
import RequestProject.SAWHexPathHelpers
import RequestProject.SAWVEdgeCountAux

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Parity of the incident-edge count -/

/-- At the *initial* vertex of a walk whose two endpoints differ, the number of
incident edges is odd. -/
lemma vEdgeCount_odd_at_start {s t : HexVertex} (w : hexGraph.Walk s t)
    (hst : s ≠ t) : Odd (vEdgeCount s w) := by
  have h := vEdgeCount_parity s t w s
  rw [if_pos rfl, if_neg hst] at h
  exact Nat.odd_iff.2 (by simpa using h)

/-! ## The starting vertex is used exactly once -/

lemma hexNeighbors3_paperStart_zero' : hexNeighbors3 paperStart 0 = hexOrigin := rfl

/-- The edge from `paperStart` to `hexOrigin` never occurs in a strip trail:
`hexOrigin` lies outside the strip. -/
lemma freshTrail_start_edge_not_mem {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) :
    s(hexNeighbors3 paperStart 0, paperStart) ∉ γ.walk.edges := by
  intro hmem
  rw [hexNeighbors3_paperStart_zero'] at hmem
  have : hexOrigin ∈ γ.walk.support :=
    γ.walk.fst_mem_support_of_mem_edges hmem
  exact hexOrigin_not_in_strip T (γ.in_strip _ this).1

/-- A fresh trail whose terminal vertex is not `paperStart` uses exactly one
edge at `paperStart`. -/
lemma freshTrail_vEdgeCount_start {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) (hne : prev ≠ paperStart) :
    vEdgeCount paperStart γ.walk = 1 := by
  have hle : vEdgeCount paperStart γ.walk ≤ 2 :=
    vEdgeCount_le_two_excluding paperStart 0 γ.walk γ.is_trail
      (freshTrail_start_edge_not_mem γ)
  have hodd : Odd (vEdgeCount paperStart γ.walk) :=
    vEdgeCount_odd_at_start γ.walk (Ne.symm hne)
  obtain ⟨m, hm⟩ := hodd
  omega

/-! ## The terminal vertex is used exactly once -/

/-- A fresh trail whose terminal vertex `prev` is not `paperStart` uses exactly
one edge at `prev`: the freshness of `s(prev, next)` leaves only two of the
three edges at `prev` available, and the count is odd. -/
lemma freshTrail_vEdgeCount_end {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) (hne : prev ≠ paperStart) :
    vEdgeCount prev γ.walk = 1 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, next = hexNeighbors3 prev j := by
    rcases hexNeighbors3_complete prev next γ.adj with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hfresh : s(hexNeighbors3 prev j, prev) ∉ γ.walk.edges := by
    rw [← hj, Sym2.eq_swap]; exact γ.fresh
  have hle : vEdgeCount prev γ.walk ≤ 2 :=
    vEdgeCount_le_two_excluding prev j γ.walk γ.is_trail hfresh
  have hodd : Odd (vEdgeCount prev γ.walk) :=
    vEdgeCount_odd_at_endpoint γ.walk γ.is_trail prev hne rfl
  obtain ⟨m, hm⟩ := hodd
  omega

/-! ## Fresh trails are self-avoiding walks -/

/-- **Fresh trails ending away from `paperStart` are self-avoiding walks.** -/
theorem freshTrail_isPath {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) (hne : prev ≠ paperStart) :
    γ.walk.IsPath :=
  hex_trail_is_path_of_endpoint_bounds γ.walk γ.is_trail
    (le_of_eq (freshTrail_vEdgeCount_start γ hne))
    (le_of_eq (freshTrail_vEdgeCount_end γ hne)) (Ne.symm hne)

/-- The self-avoiding walk underlying a fresh trail. -/
def FreshTrail.toSAW {T L : ℕ} {prev next : HexVertex}
    (γ : FreshTrail T L prev next) (hne : prev ≠ paperStart) :
    SAW paperStart γ.walk.length where
  w := prev
  p := ⟨γ.walk, freshTrail_isPath γ hne⟩
  l := rfl

end
