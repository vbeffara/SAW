/-
# Cancellation Identity — Lemma 1 of Duminil-Copin & Smirnov (2012)

Provides a clean statement and partial proof of Lemma 1:

  If x = xc and σ = 5/8, then for every vertex v ∈ V(Ω):
    (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0
  where p, q, r are the three mid-edges adjacent to v.

## Proof structure

The proof partitions walks ending at v's mid-edges into groups:

1. **Triplets**: A walk γ₁ visiting only 1 mid-edge can be extended to
   γ₂ and γ₃ visiting 2 mid-edges. The triplet contribution is:
     dⱼ·wt(W,ℓ) + dₖ·wt(W-π/3,ℓ+1) + dₗ·wt(W+π/3,ℓ+1) = 0

2. **Pairs**: Walks visiting all 3 mid-edges are paired by loop reversal.
     dₖ·wt(W-4π/3,ℓ) + dₗ·wt(W+4π/3,ℓ) = 0

## Status

- Algebraic cancellation: PROVED (triplet_cancellation, pair_cancellation)
- Walk partition operations: PROVED (extend_zero_v_edges, outgoing_1_v_edge_retract)
- Walk partition bijection: partially proved (extend_vEdgeCount_one, etc.)
- Full vertex relation: this file states and decomposes it
-/

import Mathlib
import RequestProject.SAWWalkPartitionComplete
import RequestProject.SAWObservableFormal

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Observable at a mid-edge

F(z) = Σ_{γ: a → z, γ ⊂ Ω} e^{-iσW(γ)} · x^{ℓ(γ)}

where the sum is over all trails from the starting mid-edge a to z
that stay inside the domain Ω. -/

/-- An observable walk from paperStart to mid-edge (prev → next),
    staying in PaperInfStrip T.
    Uses IsTrail (edge-SAW) rather than IsPath (vertex-SAW). -/
structure StripTrailToMidEdge (T : ℕ) (prev next : HexVertex) where
  trail : hexGraph.Walk paperStart prev
  is_trail : trail.IsTrail
  adj : hexGraph.Adj prev next
  in_strip : ∀ u ∈ trail.support, PaperInfStrip T u

/-- The length (vertex count) of a strip trail. -/
def StripTrailToMidEdge.vertexCount {T : ℕ} {prev next : HexVertex}
    (γ : StripTrailToMidEdge T prev next) : ℕ :=
  γ.trail.length + 1

/-- The full support including the mid-edge endpoint. -/
def StripTrailToMidEdge.fullSupport {T : ℕ} {prev next : HexVertex}
    (γ : StripTrailToMidEdge T prev next) : List HexVertex :=
  γ.trail.support ++ [next]

/-- The winding of the trail. -/
def StripTrailToMidEdge.winding {T : ℕ} {prev next : HexVertex}
    (γ : StripTrailToMidEdge T prev next) : ℝ :=
  hexWalkWinding γ.fullSupport

/-- The complex weight of the trail: e^{-iσW} · xc^ℓ. -/
def StripTrailToMidEdge.weight {T : ℕ} {prev next : HexVertex}
    (γ : StripTrailToMidEdge T prev next) : ℂ :=
  walkWeight γ.winding γ.vertexCount xc sigma

/-! ## The vertex relation sum

At each vertex v ∈ V(Ω), the vertex relation sum is:
  S(v) = Σ_{i=0}^{2} midEdgeDir(v, i) · F(hexNeighbors3 v i)

The cancellation identity says S(v) = 0. -/

/-- The contribution of a single trail to the vertex relation at v.
    The trail ends at the mid-edge from hexNeighbors3 v i toward v
    (or from v toward hexNeighbors3 v i). The direction is midEdgeDir v i. -/
def trailVertexContrib (v : HexVertex) (i : Fin 3)
    (winding : ℝ) (len : ℕ) : ℂ :=
  midEdgeDir v i * walkWeight winding len xc sigma

/-! ## The walk partition for vertex-SAWs

For vertex-SAWs (paths, where each vertex is visited at most once),
the walk partition is into TRIPLETS only (no pairs), since a path
visits at most 2 edges at v.

### Classification:
- **Root** (0 v-edges): trail from start to nⱼ, half-edge nⱼ → v.
  v is NOT in the trail's support. Can be extended both directions.

- **Extension** (1 v-edge): trail from start to v, half-edge v → nₖ.
  v IS the trail endpoint, entered from one neighbor.
  Retracts to a unique root.

### Proved operations:
- `extend_zero_v_edges`: 0-edge root → 1-edge extension ✓
- `outgoing_1_v_edge_retract`: 1-edge extension → 0-edge root ✓
- `extend_vEdgeCount_one`: extension has exactly 1 v-edge ✓
- `path_vEdgeCount_le_one`: paths have ≤ 1 v-edge ✓
- `path_fresh_vEdgeCount_zero`: fresh vertex means 0 v-edges ✓

### Algebraic cancellation:
- `vertexContrib_triplet_zero`: triplet sum = 0 ✓
- `vertexContrib_pair_zero`: pair sum = 0 ✓
-/

/-! ## Triplet cancellation from the walk partition

The vertex relation at v follows by grouping walks into triplets:

For each root walk γ (from start to nⱼ, 0 v-edges):
  Group = {γ, ext(γ,k), ext(γ,l)} where {j,k,l} = {0,1,2}

  Contribution = dⱼ · wt(W_γ, ℓ_γ)
               + dₖ · wt(W_γ - π/3, ℓ_γ + 1)
               + dₗ · wt(W_γ + π/3, ℓ_γ + 1)
               = 0  (by vertexContrib_triplet_zero)

Summing over all root walks: total = Σ_{roots} 0 = 0. -/

/-
The triplet contribution for a root arriving at index j with
    winding W and vertex-count ℓ vanishes at any vertex v.

    This uses the critical value xc and spin σ = 5/8.
-/
theorem triplet_contrib_zero_at_vertex (v : HexVertex) (j : Fin 3)
    (W : ℝ) (ℓ : ℕ) :
    let (k, l) := fin3_other j
    trailVertexContrib v j W ℓ +
    trailVertexContrib v k (W - Real.pi / 3) (ℓ + 1) +
    trailVertexContrib v l (W + Real.pi / 3) (ℓ + 1) = 0 := by
  unfold trailVertexContrib
  fin_cases j <;> simp [fin3_other]
  · exact vertexContrib_triplet_zero v W ℓ
  ·
    -- Apply the triplet_sum_perm1_zero � theorem� to conclude the proof.
    apply triplet_sum_perm1_zero
  ·
    -- Apply the triplet_sum_perm2_zero � theorem� to conclude the proof.
    apply triplet_sum_perm2_zero

/-
The pair contribution for walks at indices k and l with
    windings W - 4π/3 and W + 4π/3 vanishes.
-/
theorem pair_contrib_zero_at_vertex (v : HexVertex) (j : Fin 3)
    (W : ℝ) (ℓ : ℕ) :
    let (k, l) := fin3_other j
    trailVertexContrib v k (W - 4 * Real.pi / 3) ℓ +
    trailVertexContrib v l (W + 4 * Real.pi / 3) ℓ = 0 := by
  unfold trailVertexContrib
  fin_cases j <;> simp [fin3_other]
  · exact vertexContrib_pair_zero v W ℓ
  ·
    convert pair_sum_zero v W using 1;
    constructor;
    · exact?;
    · intro h; specialize h ℓ; simp_all +decide [ walkVertexContrib ] ;
      convert congr_arg ( fun x => x * j ) h using 1 <;> ring;
      rw [ show midEdgeDir v 1 = j * midEdgeDir v 0 from ?_, show midEdgeDir v 2 = conj j * midEdgeDir v 0 from ?_ ] ; ring;
      · grind +suggestions;
      · exact midEdgeDir_j_relation v |>.2;
      · exact midEdgeDir_j_relation v |>.1
  ·
    rw [ show midEdgeDir v 1 = j * midEdgeDir v 0 from ?_ ];
    · unfold j walkWeight; ring;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, pow_add ];
      unfold sigma; norm_num [ ( by ring : Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 ), ( by ring : Real.pi * ( 4 / 3 ) = Real.pi + Real.pi / 3 ), Real.sin_add, Real.cos_add ] ; ring_nf ; norm_num;
      norm_num [ ( by ring : Real.pi * ( 5 / 6 ) = Real.pi - Real.pi / 6 ), Real.sin_add, Real.cos_add ] ; ring_nf ; norm_num [ Real.sqrt_nonneg, Real.pi_pos.le ] ; ring_nf ; norm_num;
    · exact midEdgeDir_j_relation v |>.1

/-! ## The vertex relation (Lemma 1) — formal statement

**Lemma 1** (Cancellation Identity). For every vertex v ∈ V(Ω):
  Σ_{i=0}^{2} midEdgeDir(v, i) · F(vertexMidEdgesIncoming v i) = 0

Proof: Partition all trails to v's mid-edges into triplets and pairs.
Each group contributes zero. Therefore the total is zero.

### Formal structure:
The proof reduces to showing that for any finite set of walks to
v's three mid-edges, if the walks can be partitioned into cancelling
groups, then the total sum is zero.

This is captured by `sum_zero_of_partition_cancel` from
SAWCancellationProof.lean, combined with the triplet/pair cancellation
theorems above. -/

/-- **Lemma 1** (Duminil-Copin & Smirnov 2012): The vertex relation.

    For each vertex v, if walks to v's three mid-edges are partitioned
    into groups, where each group is either:
    - A triplet (root j, extension k, extension l) satisfying
      winding and length relations, OR
    - A pair (member k, member l) satisfying winding and length relations,
    then the total vertex relation sum is zero.

    This is the abstract form of Lemma 1. The concrete application
    requires showing that ALL walks in the strip satisfy this partition. -/
theorem lemma1_vertex_relation_abstract (v : HexVertex)
    {n : ℕ} (idx : Fin n → Fin 3) (W : Fin n → ℝ) (L : Fin n → ℕ)
    -- Partition into groups:
    {m : ℕ} (group : Fin n → Fin m)
    -- Each group sums to zero:
    (h_cancel : ∀ g : Fin m,
      ∑ i ∈ Finset.univ.filter (fun i => group i = g),
        trailVertexContrib v (idx i) (W i) (L i) = 0) :
    ∑ i : Fin n, trailVertexContrib v (idx i) (W i) (L i) = 0 :=
  sum_zero_of_partition_cancel _ group h_cancel

/-! ## Concrete vertex relation for vertex-SAWs

For the special case of vertex-SAWs (where only triplets arise),
the partition is simpler: every walk is either a root (0 v-edges)
or an extension (1 v-edge), and each root generates a triplet
with its two extensions.

**Key fact**: On the hexagonal lattice, vertex-SAW walks have at most
1 v-edge (by `path_vEdgeCount_le_one`). So only triplets arise,
and the walk partition is into triplets only. -/

/-
For vertex-SAWs in the strip, the walk partition is into triplets.
    Every arrival walk (0 v-edges) generates two extensions (1 v-edge),
    and each extension retracts to a unique arrival walk.
-/
theorem vertex_relation_vertex_saws (v : HexVertex)
    {n : ℕ} (idx : Fin n → Fin 3) (W : Fin n → ℝ) (L : Fin n → ℕ)
    -- The walks are organized into triplets:
    -- Each triplet consists of a root at index j and extensions at k, l
    {t : ℕ} (triplet_root : Fin t → Fin n)
    (triplet_ext1 : Fin t → Fin n)
    (triplet_ext2 : Fin t → Fin n)
    -- The triplets cover all walks:
    (h_cover : ∀ i : Fin n,
      (∃ g, triplet_root g = i) ∨
      (∃ g, triplet_ext1 g = i) ∨
      (∃ g, triplet_ext2 g = i))
    -- Each walk is in exactly one group:
    (h_disjoint : Function.Injective (fun g : Fin t × Fin 3 =>
      match g.2 with
      | 0 => triplet_root g.1
      | 1 => triplet_ext1 g.1
      | 2 => triplet_ext2 g.1))
    -- The winding and length relations hold:
    (h_relations : ∀ g : Fin t,
      let (k, l) := fin3_other (idx (triplet_root g))
      idx (triplet_ext1 g) = k ∧
      idx (triplet_ext2 g) = l ∧
      W (triplet_ext1 g) = W (triplet_root g) - Real.pi / 3 ∧
      W (triplet_ext2 g) = W (triplet_root g) + Real.pi / 3 ∧
      L (triplet_ext1 g) = L (triplet_root g) + 1 ∧
      L (triplet_ext2 g) = L (triplet_root g) + 1) :
    ∑ i : Fin n, trailVertexContrib v (idx i) (W i) (L i) = 0 := by
  -- Each triplet (root, ext1, ext2) sums to zero by triplet_contrib_zero_at_vertex
  -- The total sum is the sum of triplet contributions, each zero
  convert lemma1_vertex_relation_abstract _ _ _ _ _ using 1;
  any_goals exact t;
  rotate_left;
  exact v;
  use fun i => idx ( triplet_root i );
  exact fun g => W ( triplet_root g );
  exact fun g => L ( triplet_root g );
  exact fun g => g;
  simp +decide [ Finset.sum_filter ];
  constructor <;> intro h;
  · exact fun h => Finset.sum_eq_zero fun i _ => h i;
  · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image triplet_root Finset.univ ∪ Finset.image triplet_ext1 Finset.univ ∪ Finset.image triplet_ext2 Finset.univ ) ) ];
    · rw [ Finset.sum_union, Finset.sum_union ] <;> norm_num [ Finset.disjoint_right, h_disjoint.eq_iff ];
      · rw [ Finset.sum_image, Finset.sum_image, Finset.sum_image ];
        · rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ];
          exact Finset.sum_eq_zero fun i _ => by simpa [ h_relations i ] using triplet_contrib_zero_at_vertex v ( idx ( triplet_root i ) ) ( W ( triplet_root i ) ) ( L ( triplet_root i ) ) ;
        · intro g hg g' hg' h_eq;
          have := @h_disjoint ( g, 2 ) ( g', 2 ) ; simp +decide [ h_eq ] at this;
          exact this;
        · intro g hg g' hg' h_eq;
          have := @h_disjoint ( g, 1 ) ( g', 1 ) ; simp +decide [ h_eq ] at this;
          exact this;
        · intro g hg g' hg' h_eq;
          have := @h_disjoint ( g, 0 ) ( g', 0 ) ; simp +decide [ h_eq ] at this;
          grind;
      · intro a x hx; have := @h_disjoint ( x, 0 ) ( a, 1 ) ; simp +decide [ hx ] at this;
      · intro g; constructor <;> intro x hx <;> have := @h_disjoint ( x, 0 ) ( g, 2 ) <;> simp +decide [ hx ] at this;
        have := @h_disjoint ( x, 1 ) ( g, 2 ) ; simp +decide [ hx ] at this;
    · intro i hi hi'; specialize h_cover i; aesop;

/-! ## Summary

### Proved in this file:
1. `triplet_contrib_zero_at_vertex` — each triplet contributes zero
2. `pair_contrib_zero_at_vertex` — each pair contributes zero
3. `lemma1_vertex_relation_abstract` — vertex relation from partition

### Remaining for full Lemma 1:
1. `vertex_relation_vertex_saws` — vertex relation for vertex-SAW partition
   (requires connecting the abstract framework to concrete walk properties)
2. Showing that ALL walks in the strip satisfy the partition conditions
   (requires the extension/retraction bijection)
3. The discrete Stokes summation over all vertices
-/

end