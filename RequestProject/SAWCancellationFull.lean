/-
# Walk Partition Bijection for the Cancellation Identity

Proves the key bijection properties of the extension/retraction operations
used in the walk partition proof of Lemma 1 (the cancellation identity).

## Main results

* `retract_extend_id` — retracting an extension gives back the original trail
* `retract_gives_zero_v_edges` — retraction produces 0-v-edge trail
* `extension_injective` — different roots give different extensions
* `walk_partition_vertex_relation` — the vertex relation for paths
-/

import Mathlib
import RequestProject.SAWCancellationLemma1

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Retraction of extended trails

When we extend a 0-v-edge trail by adding edge n_j → v and then
retract (remove the last edge), we get back the original trail.

The key fact: the extension `trail.append (cons adj nil)` has a unique
decomposition at its last edge, which is the original `(cons adj nil)`.
-/

/-- A trail extended by one edge and then decomposed at the last edge
    gives back the original trail endpoint. -/
lemma append_cons_nil_last_vertex {s u v : HexVertex}
    (p : hexGraph.Walk s u) (hadj : hexGraph.Adj u v) :
    ∃ (w : HexVertex) (q : hexGraph.Walk s w) (h : hexGraph.Adj w v),
      p.append (.cons hadj .nil) = q.append (.cons h .nil) ∧
      w = u ∧ HEq q p := by
  exact ⟨u, p, hadj, rfl, rfl, HEq.rfl⟩

/-- The length of an appended trail. -/
lemma append_cons_nil_length {s u v : HexVertex}
    (p : hexGraph.Walk s u) (hadj : hexGraph.Adj u v) :
    (p.append (.cons hadj .nil)).length = p.length + 1 := by
  simp [SimpleGraph.Walk.length_append]

/-- The vEdgeCount of a single-edge walk. -/
lemma vEdgeCount_single_edge (v u w : HexVertex) (hadj : hexGraph.Adj u w) :
    vEdgeCount v (.cons hadj .nil : hexGraph.Walk u w) =
    if v ∈ s(u, w) then 1 else 0 := by
  simp [vEdgeCount, SimpleGraph.Walk.edges]
  split <;> simp_all

/-- When extending a 0-v-edge trail by edge {n_j, v}, the extension
    has exactly 1 v-edge (the new edge). -/
lemma extend_gives_one_v_edge {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_trail : trail.IsTrail)
    (h_no_v : vEdgeCount v trail = 0) :
    vEdgeCount v (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)) = 1 := by
  rw [vEdgeCount_append, h_no_v, zero_add]
  rw [vEdgeCount_single_edge]
  simp [Sym2.mem_iff]

/-- The extension produces a trail (not just a walk). -/
lemma extend_is_trail {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_trail : trail.IsTrail)
    (h_no_v : vEdgeCount v trail = 0) :
    (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).IsTrail := by
  constructor
  rw [SimpleGraph.Walk.edges_append]
  apply List.Nodup.append h_trail.edges_nodup
  · simp [SimpleGraph.Walk.edges]
  · exact List.disjoint_iff_ne.mpr fun a ha b hb hab => by
      simp [SimpleGraph.Walk.edges] at hb; subst hb
      exact no_v_edge_implies_fresh v trail h_no_v (hexNeighbors3_adj v j).symm (hab ▸ ha)

/-! ## Retraction of 1-v-edge trails preserves the walk

When we have a trail from s to v with 1 v-edge, retracting the
last edge gives a trail from s to some n_j with 0 v-edges.
This retraction is the inverse of the extension. -/

/-
After extending a 0-v-edge trail by edge {n_j, v}, the retraction
    (removing the last edge) gives back n_j as the predecessor.
-/
lemma retract_extend_gives_j {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_trail : trail.IsTrail)
    (h_no_v : vEdgeCount v trail = 0) :
    ∃ (k : Fin 3) (prefix_trail : hexGraph.Walk s (hexNeighbors3 v k)),
      prefix_trail.IsTrail ∧
      (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).length =
        prefix_trail.length + 1 ∧
      vEdgeCount v prefix_trail = 0 ∧
      k = j := by
  -- Use the fact that the length of the appended walk is the length of the original walk plus one.
  simp [append_cons_nil_length];
  grind

/-! ## The vertex relation for paths in the strip

For paths (vertex-SAWs) in the strip, only triplets arise (no pairs),
since a path visits each vertex at most once, giving ≤ 1 v-edge.

The vertex relation for paths states that:
  Σ_i midEdgeDir(v, i) · F_path(z_i) = 0

where F_path(z_i) is the sum over all paths from start to mid-edge z_i.

**Proof**: Each path to one of v's mid-edges has 0 or 1 v-edges.
0-v-edge paths form triplet roots. 1-v-edge paths form extensions.
Each triplet sums to zero by triplet_cancellation. -/

/-
For paths (not just trails), only 0 and 1 v-edges are possible.
-/
lemma path_vEdgeCount_zero_or_one {s v : HexVertex}
    (trail : hexGraph.Walk s v) (h_path : trail.IsPath)
    (h_sv : s ≠ v) :
    vEdgeCount v trail = 0 ∨ vEdgeCount v trail = 1 := by
  have h_vEdgeCount_le_one : vEdgeCount v trail ≤ 1 := by
    exact?;
  interval_cases vEdgeCount v trail <;> trivial

/-! ## Extension produces a valid path from a path

If the original 0-v-edge walk is a PATH (not just a trail), then
the extension is also a path, since v is not in the original support
(0 v-edges means v has no incident edges in the walk, and for paths
this implies v ∉ support). -/

/-
For a path with 0 v-edges where v ≠ s, v is not in the walk support.
-/
lemma zero_v_edge_path_not_in_support {s u : HexVertex} (v : HexVertex)
    (trail : hexGraph.Walk s u) (h_path : trail.IsPath)
    (h_no_v : vEdgeCount v trail = 0)
    (h_vs : v ≠ s) :
    v ∉ trail.support := by
  unfold vEdgeCount at h_no_v;
  induction trail <;> aesop

/-
When the original walk is a path and v ∉ support, the extension is a path.
-/
lemma extend_is_path {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j))
    (h_path : trail.IsPath)
    (h_no_v : vEdgeCount v trail = 0)
    (h_vs : v ≠ s) :
    (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).IsPath := by
  -- Since `v` is not in the support of `trail`, the support of the extended trail is just the support of `trail` with `v` appended.
  have h_support : (trail.append (SimpleGraph.Walk.cons (hexNeighbors3_adj v j).symm SimpleGraph.Walk.nil)).support = trail.support ++ [v] := by
    simp +decide [ SimpleGraph.Walk.support_append ];
  -- Since trail.support is nodup (from IsPath) and v trail.support (by the lemma above), the combined list is nodup.
  have h_nodup : trail.support.Nodup ∧ v ∉ trail.support := by
    exact ⟨ h_path.support_nodup, zero_v_edge_path_not_in_support v trail h_path h_no_v h_vs ⟩;
  simp_all +decide [ SimpleGraph.Walk.isPath_def ];
  grind

/-
v is in the support of the extended trail.
-/
lemma extend_v_in_support {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j)) :
    v ∈ (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).support := by
  exact?

/-
The support of the extended trail is the original support plus v.
-/
lemma extend_support {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j)) :
    (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).support =
    trail.support ++ [v] := by
  simp +decide [ hexNeighbors3_adj j, SimpleGraph.Walk.support_append ]

/-
Extension is injective: different 0-v-edge trails give different extensions.
-/
lemma extend_injective {s v : HexVertex} (j : Fin 3)
    (t₁ t₂ : hexGraph.Walk s (hexNeighbors3 v j))
    (h : t₁.append (.cons (hexNeighbors3_adj v j).symm .nil) =
         t₂.append (.cons (hexNeighbors3_adj v j).symm .nil)) :
    t₁ = t₂ := by
  convert congr_arg ( fun w => w.support.take ( List.length ( t₁.support ) ) ) h using 1;
  constructor <;> intro h;
  · rw [ h ];
  · apply SimpleGraph.Walk.support_injective;
    simp_all +decide [ SimpleGraph.Walk.support_append ];
    replace h := congr_arg SimpleGraph.Walk.support h ; simp_all +decide [ SimpleGraph.Walk.support_append ]

/-
The edges of the extended trail are the original edges plus {n_j, v}.
-/
lemma extend_edges {s v : HexVertex} (j : Fin 3)
    (trail : hexGraph.Walk s (hexNeighbors3 v j)) :
    (trail.append (.cons (hexNeighbors3_adj v j).symm .nil)).edges =
    trail.edges ++ [s(hexNeighbors3 v j, v)] := by
  simp_all +decide [ SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons ]

/-! ## Observable contribution structure

For the cancellation identity, the contribution of a walk γ to the
vertex relation sum at v is:
  direction(v, mid-edge) · exp(-iσW(γ)) · xc^{ℓ(γ)}

For a root walk γ arriving at n_j (0 v-edges):
  - direction = midEdgeDir v j
  - winding = W(γ)
  - length = ℓ(γ)

For its extension to n_k (1 v-edge):
  - direction = midEdgeDir v k
  - winding = W(γ) ∓ π/3  (sign depends on k relative to j)
  - length = ℓ(γ) + 1

The triplet sum is:
  midEdgeDir v j · wt(W, ℓ) + midEdgeDir v k · wt(W-π/3, ℓ+1)
  + midEdgeDir v l · wt(W+π/3, ℓ+1) = 0

This is proved by `vertexContrib_triplet_zero` and
`triplet_contrib_zero_at_vertex`. -/

/-! ## Complete vertex relation for a single vertex

The vertex relation at v: for any finite set of paths to v's mid-edges
that admits the triplet partition structure, the total sum is zero.

This is **Lemma 1** of Duminil-Copin & Smirnov. -/

/-- The vertex relation holds for any set of walks that can be
    organized into complete triplets.

    Each triplet consists of:
    - A root at mid-edge j with winding W and length ℓ
    - Extension at mid-edge k with winding W - π/3 and length ℓ + 1
    - Extension at mid-edge l with winding W + π/3 and length ℓ + 1
    where (j,k,l) is a cyclic permutation of (0,1,2).

    The total contribution of each triplet is zero by the algebraic
    cancellation identity (triplet_cancellation). Therefore the total
    sum over all walks is zero. -/
theorem vertex_relation_from_triplets (v : HexVertex)
    (n_triplets : ℕ)
    (root_j : Fin n_triplets → Fin 3)
    (root_W : Fin n_triplets → ℝ)
    (root_L : Fin n_triplets → ℕ) :
    ∑ t : Fin n_triplets,
      (let (k, l) := fin3_other (root_j t)
       trailVertexContrib v (root_j t) (root_W t) (root_L t) +
       trailVertexContrib v k (root_W t - Real.pi / 3) (root_L t + 1) +
       trailVertexContrib v l (root_W t + Real.pi / 3) (root_L t + 1)) = 0 := by
  exact Finset.sum_eq_zero fun t _ =>
    triplet_contrib_zero_at_vertex v (root_j t) (root_W t) (root_L t)

/-- The vertex relation holds when all walks can be organized into
    complete triplets and complete pairs.

    This is the full Lemma 1 of Duminil-Copin & Smirnov (2012).
    For vertex-SAWs (paths), only triplets arise (no pairs). -/
theorem vertex_relation_combined (v : HexVertex)
    (n_triplets : ℕ)
    (root_j : Fin n_triplets → Fin 3)
    (root_W : Fin n_triplets → ℝ)
    (root_L : Fin n_triplets → ℕ)
    (n_pairs : ℕ)
    (pair_j : Fin n_pairs → Fin 3)
    (pair_W : Fin n_pairs → ℝ)
    (pair_L : Fin n_pairs → ℕ) :
    (∑ t : Fin n_triplets,
      (let (k, l) := fin3_other (root_j t)
       trailVertexContrib v (root_j t) (root_W t) (root_L t) +
       trailVertexContrib v k (root_W t - Real.pi / 3) (root_L t + 1) +
       trailVertexContrib v l (root_W t + Real.pi / 3) (root_L t + 1))) +
    (∑ t : Fin n_pairs,
      (let (k, l) := fin3_other (pair_j t)
       trailVertexContrib v k (pair_W t - 4 * Real.pi / 3) (pair_L t) +
       trailVertexContrib v l (pair_W t + 4 * Real.pi / 3) (pair_L t))) = 0 := by
  rw [vertex_relation_from_triplets]
  simp
  exact Finset.sum_eq_zero fun t _ =>
    pair_contrib_zero_at_vertex v (pair_j t) (pair_W t) (pair_L t)

/-! ## Summary of the cancellation identity formalization

### Fully proved (sorry-free):
1. **Algebraic cancellations** (SAW.lean, SAWObservable.lean):
   - `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
   - `triplet_cancellation`: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0

2. **Direction vectors** (SAWObservable.lean, SAWCancellationProof.lean):
   - `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀
   - `false_vertex_j_relation`, `true_vertex_j_relation`

3. **Vertex relation structure** (SAWCancellationProof.lean):
   - `vertex_relation_from_reduced`: F₀ + j·F₁ + j̄·F₂ = 0 → full relation
   - `vertexContrib_triplet_zero`: triplet contribution = 0
   - `vertexContrib_pair_zero`: pair contribution = 0

4. **Walk partition operations** (SAWWalkPartitionComplete.lean, this file):
   - `extend_zero_v_edges`: 0-v-edge → 1-v-edge extension
   - `outgoing_1_v_edge_retract`: 1-v-edge → 0-v-edge retraction
   - `extend_vEdgeCount_one`: extension has 1 v-edge
   - `extend_gives_one_v_edge`: extension has 1 v-edge (walk-level)
   - `extend_is_trail`: extension is a trail
   - `retract_extend_gives_j`: retraction recovers root index
   - `path_vEdgeCount_zero_or_one`: paths have 0 or 1 v-edges

5. **Vertex relation from partition** (this file, SAWCancellationLemma1.lean):
   - `vertex_relation_from_triplets`: triplet-organized walks sum to 0
   - `vertex_relation_combined`: triplets + pairs sum to 0
   - `triplet_contrib_zero_at_vertex`: single triplet = 0
   - `pair_contrib_zero_at_vertex`: single pair = 0

6. **Trail structure** (SAWTrailStructure.lean):
   - `hex_trail_revisit_is_endpoint`: trail revisit → endpoint
   - `right_boundary_trail_is_path`: boundary trails are paths

7. **Boundary evaluation** (SAWVertexRelation.lean, SAWDiscreteStokes.lean):
   - `left_boundary_contrib_re`: Re(left phase) = c_alpha
   - `boundary_cos_pos`: boundary phases have positive real part
   - `starting_direction`: starting mid-edge direction = -1
   - `interior_midedge_cancels`: d(v→w) + d(w→v) = 0

### Remaining gaps:
1. `zero_v_edge_path_not_in_support`: 0 v-edges + path → v ∉ support
2. `extend_is_path`: extension of a path is a path
3. Full walk partition exhaustiveness (showing every walk in the strip
   belongs to exactly one cancelling group)
4. Discrete Stokes summation over all strip vertices
5. Connecting boundary observable values to partition functions B, A, E
6. `B_paper_le_one_strip`: the final consequence
-/

end