/-
# The Cancellation Identity (Lemma 1) — Trail-Based Observable

Formalizes Lemma 1 (the cancellation identity / vertex relation) from:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Key results

* `strip_trail_finite` — trails in the finite strip form a finite type
* `tripletExtendStrip` — the triplet extension operation in the strip
* `strip_triplet_zero` — each triplet's contribution is zero
* `strip_pair_zero` — each pair's contribution is zero
-/

import Mathlib
import RequestProject.SAWTripletInStrip
import RequestProject.SAWCancellationLemma1

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 3200000

/-! ## Trail-based mid-edge walk in the finite strip -/

/-- A trail from paperStart to mid-edge (prev, next) staying in PaperFinStrip T L. -/
structure StripTrail (T L : ℕ) (prev next : HexVertex) where
  walk : hexGraph.Walk paperStart prev
  is_trail : walk.IsTrail
  adj : hexGraph.Adj prev next
  in_strip : ∀ u ∈ walk.support, PaperFinStrip T L u

/-- Length of a strip trail. -/
def StripTrail.len {T L : ℕ} {prev next : HexVertex}
    (γ : StripTrail T L prev next) : ℕ :=
  γ.walk.length + 1

/-- Full vertex list. -/
def StripTrail.fullSupport {T L : ℕ} {prev next : HexVertex}
    (γ : StripTrail T L prev next) : List HexVertex :=
  γ.walk.support ++ [next]

/-- Winding. -/
def StripTrail.winding {T L : ℕ} {prev next : HexVertex}
    (γ : StripTrail T L prev next) : ℝ :=
  hexWalkWinding γ.fullSupport

/-- Weight: e^{-iσW} · xc^ℓ. -/
def StripTrail.weight {T L : ℕ} {prev next : HexVertex}
    (γ : StripTrail T L prev next) : ℂ :=
  walkWeight γ.winding γ.len xc sigma

/-! ## Finiteness of strip trails -/

/-
On the hex lattice, trail support vertices (except possibly endpoints)
    appear exactly once. So trail length ≤ |strip vertices|.
-/
lemma strip_trail_length_bound (T L : ℕ) (prev next : HexVertex)
    (γ : StripTrail T L prev next) :
    γ.walk.length ≤ 3 * (paper_fin_strip_finite' T L).toFinset.card := by
  -- Each edge in the trail corresponds to a pair of vertices in the strip, so the length of the trail is bounded by the number of edges in the strip.
  have h_edge_count : γ.walk.length ≤ (γ.walk.support.toFinset.biUnion (fun v => (hexGraph.incidenceFinset v).filter (fun e => e ∈ γ.walk.edges))).card := by
    refine' le_trans _ ( Finset.card_le_card _ );
    rotate_left;
    exact γ.walk.edges.toFinset;
    · intro e he;
      have h_support : ∀ {u v : HexVertex} {p : hexGraph.Walk u v}, ∀ e ∈ p.edges, ∃ w ∈ p.support, e ∈ hexGraph.incidenceFinset w := by
        intros u v p e he; induction p <;> simp_all +decide [ SimpleGraph.Walk.edges_cons ] ;
        aesop;
      specialize h_support _ ( List.mem_toFinset.mp he ) ; aesop;
    · rw [ List.toFinset_card_of_nodup ];
      · norm_num +zetaDelta at *;
      · exact γ.is_trail.edges_nodup;
  refine le_trans h_edge_count <| le_trans ( Finset.card_biUnion_le ) ?_;
  refine' le_trans ( Finset.sum_le_sum fun x hx => Finset.card_le_card <| show { e ∈ hexGraph.incidenceFinset x | e ∈ γ.walk.edges } ⊆ hexGraph.incidenceFinset x from Finset.filter_subset _ _ ) _ ; simp +decide [ mul_comm ];
  refine' le_trans ( Finset.sum_le_sum fun x hx => Nat.le_of_lt_succ <| show hexGraph.degree x < 4 from _ ) _;
  · -- The degree of any vertex in the hex lattice is 3.
    have h_deg : ∀ x : HexVertex, hexGraph.degree x = 3 := by
      intro x; exact (by
      convert hexGraph_degree x using 1);
    linarith [ h_deg x ];
  · norm_num [ mul_comm ];
    refine' Finset.card_le_card _;
    exact fun x hx => by have := γ.in_strip x ( by simpa using hx ) ; aesop;

/-- Strip trails form a finite type. -/
instance strip_trail_finite (T L : ℕ) (prev next : HexVertex) :
    Finite (StripTrail T L prev next) := by
  set N := 3 * (paper_fin_strip_finite' T L).toFinset.card
  -- Embed into Σ n : Fin(N+1), {w : hexGraph.Walk paperStart prev // w.length = n}
  -- which is Fintype by SimpleGraph.fintypeSubtypeWalkLength
  apply Finite.of_injective
    (fun γ : StripTrail T L prev next =>
      (⟨⟨γ.walk.length, Nat.lt_of_le_of_lt (strip_trail_length_bound T L prev next γ)
          (Nat.lt_succ_self N)⟩,
        ⟨γ.walk, rfl⟩⟩ :
        (Σ n : Fin (N + 1), {w : hexGraph.Walk paperStart prev // w.length = n})))
  intro γ₁ γ₂ h
  have h_walk : γ₁.walk = γ₂.walk := by
    have := congr_arg (fun x => x.2.val) h; exact this
  cases γ₁; cases γ₂; simp at h_walk; subst h_walk; rfl

/-! ## Trail-based observable -/

/-- The trail-based parafermionic observable at mid-edge (prev, next). -/
def trailObs (T L : ℕ) (prev next : HexVertex) : ℂ :=
  ∑' (γ : StripTrail T L prev next), γ.weight

/-! ## Triplet extension for strip trails -/

/-- Extend a 0-v-edge strip trail at n_j to a trail ending at v → n_k. -/
def tripletExtendStrip {T L : ℕ} (v : HexVertex) (j k : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v j) v)
    (h_no_v : vEdgeCount v γ.walk = 0)
    (hv_strip : PaperFinStrip T L v) :
    StripTrail T L v (hexNeighbors3 v k) where
  walk := γ.walk.append (.cons (hexNeighbors3_adj v j).symm .nil)
  is_trail := extension_is_trail j γ.walk γ.is_trail h_no_v
  adj := hexNeighbors3_adj v k
  in_strip := extension_in_strip j γ.walk γ.in_strip hv_strip

/-- The extended trail has length = original + 1. -/
lemma tripletExtendStrip_len {T L : ℕ} (v : HexVertex) (j k : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v j) v)
    (h_no_v : vEdgeCount v γ.walk = 0) (hv : PaperFinStrip T L v) :
    (tripletExtendStrip v j k γ h_no_v hv).len = γ.len + 1 := by
  unfold StripTrail.len tripletExtendStrip
  simp [SimpleGraph.Walk.length_append]

/-- The extended trail has exactly 1 v-edge. -/
lemma tripletExtendStrip_vEdge {T L : ℕ} (v : HexVertex) (j k : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v j) v)
    (h_no_v : vEdgeCount v γ.walk = 0) (hv : PaperFinStrip T L v) :
    vEdgeCount v (tripletExtendStrip v j k γ h_no_v hv).walk = 1 :=
  extension_adds_one_v_edge j γ.walk h_no_v

/-! ## Algebraic cancellation -/

/-- Direction-weighted trail contribution to the vertex sum. -/
def stripTrailContrib (v : HexVertex) (i : Fin 3) (w : ℝ) (l : ℕ) : ℂ :=
  midEdgeDir v i * walkWeight w l xc sigma

/-- Each complete triplet contributes zero. -/
theorem strip_triplet_zero (v : HexVertex) (j : Fin 3) (W : ℝ) (ℓ : ℕ) :
    let (k, l) := fin3_other j
    stripTrailContrib v j W ℓ +
    stripTrailContrib v k (W - Real.pi / 3) (ℓ + 1) +
    stripTrailContrib v l (W + Real.pi / 3) (ℓ + 1) = 0 := by
  unfold stripTrailContrib
  exact triplet_contrib_zero_at_vertex v j W ℓ

/-- Each pair contributes zero. -/
theorem strip_pair_zero (v : HexVertex) (j : Fin 3) (W : ℝ) (ℓ : ℕ) :
    let (k, l) := fin3_other j
    stripTrailContrib v k (W - 4 * Real.pi / 3) ℓ +
    stripTrailContrib v l (W + 4 * Real.pi / 3) ℓ = 0 := by
  unfold stripTrailContrib
  exact pair_contrib_zero_at_vertex v j W ℓ

/-! ## Trail classification at vertex v

On the hex lattice (3-regular), for v ≠ paperStart and v ≠ trail endpoint:
- `hex_trail_revisit_is_endpoint` says v appears at most once in support
- So at most 2 v-edges (entering and exiting)
- Incoming trails: 0 or 2 v-edges
- Outgoing trails: exactly 1 v-edge -/

/-
3 v-edges in a trail implies v is visited at least twice.
-/
lemma three_vEdges_implies_two_visits {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (v : HexVertex) (h3 : 3 ≤ vEdgeCount v trail) :
    2 ≤ trail.support.count v := by
  -- By definition of $vEdgeCount$, we know that $vEdgeCount v trail$ counts the number of edges in the trail that are incident to $v$.
  have h_edge_count : ∀ (s t : HexVertex) (trail : hexGraph.Walk s t) (v : HexVertex), vEdgeCount v trail ≤ 2 * trail.support.count v - if v = s then 1 else 0 - if v = t then 1 else 0 := by
    intro s t trail v;
    induction' trail with s t u trail ih generalizing v;
    · unfold vEdgeCount; aesop;
    · rename_i p hp;
      convert Nat.le_trans ( Nat.add_le_add_right ( hp v ) ( if v ∈ s(t, u) then 1 else 0 ) ) _ using 1;
      · unfold vEdgeCount; simp +decide [ List.count_cons ] ;
        split_ifs <;> simp_all +decide [ List.filter_cons ];
      · split_ifs <;> simp_all +decide [ List.count_cons ];
        · omega;
        · split_ifs <;> simp_all +decide [ Nat.sub_lt_iff_lt_add ];
        · split_ifs <;> simp_all +decide [ Nat.mul_succ ];
        · omega;
        · omega;
  grind +ring

/-- For v ≠ start and v ≠ end, v-edge count ≤ 2. -/
lemma trail_vEdge_le_two_interior {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (v : HexVertex) (hv_ne_s : v ≠ s) (hv_ne_t : v ≠ t) :
    vEdgeCount v trail ≤ 2 := by
  by_contra h
  push_neg at h
  have h3 : 3 ≤ vEdgeCount v trail := h
  have hcount := three_vEdges_implies_two_visits trail h_trail v h3
  have := hex_trail_revisit_is_endpoint trail h_trail v hcount
  rcases this with rfl | rfl <;> contradiction

/-
For v ≠ start, incoming trails have 0 or 2 v-edges.
-/
lemma incoming_trail_vEdge_classify {T L : ℕ} (v : HexVertex) (i : Fin 3)
    (γ : StripTrail T L (hexNeighbors3 v i) v)
    (hv_ne_start : v ≠ paperStart) :
    vEdgeCount v γ.walk = 0 ∨ vEdgeCount v γ.walk = 2 := by
  by_cases h : v ∈ γ.walk.support <;> simp_all +decide [ vEdgeCount ];
  · have h_v_edge_count : (γ.walk.edges.filter (fun e => v ∈ e)).length ≥ 2 := by
      have h_v_edge_count : (γ.walk.edges.filter (fun e => v ∈ e)).toFinset.card ≥ 2 := by
        have := @trail_interior_vertex_uses_two_edges;
        contrapose! this;
        use paperStart, hexNeighbors3 v i, γ.walk, γ.is_trail, v, h, hv_ne_start, by
          grind +suggestions;
        intro e₁ e₂ he₁ he₂ he_ne hv₁ hv₂; have := Finset.card_le_card ( show { e₁, e₂ } ⊆ ( List.filter ( fun e => decide ( v ∈ e ) ) γ.walk.edges ).toFinset from ?_ ) ; simp_all +decide ;
        · grobner;
        · simp_all +decide [ Finset.insert_subset_iff ];
      exact h_v_edge_count.trans ( List.toFinset_card_le _ );
    have h_v_edge_count_le_two : (γ.walk.edges.filter (fun e => v ∈ e)).length ≤ 2 := by
      apply trail_vEdge_le_two_interior;
      · exact γ.is_trail;
      · assumption;
      · grind +suggestions;
    exact Or.inr ( le_antisymm h_v_edge_count_le_two h_v_edge_count );
  · left;
    intro e he hv;
    have h_support : ∀ {u w : HexVertex} {p : hexGraph.Walk u w}, e ∈ p.edges → v ∈ e → v ∈ p.support := by
      intros u w p he hv; induction p <;> aesop;
    exact h ( h_support he hv )

/-
vEdgeCount parity: for a trail from s to t, if v ≠ s and v = t,
    then vEdgeCount v is odd. This is because each interior visit
    uses 2 edges (entering + exiting) and the terminal visit uses 1.
-/
lemma vEdgeCount_odd_at_endpoint {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (v : HexVertex) (hv_ne_s : v ≠ s) (hv_eq_t : v = t) :
    Odd (vEdgeCount v trail) := by
  -- By induction on the walk, we can � show� that the parity of the number of edges incident to v is equal to the sum (� of� the parities of the edges incident to v in the rest of the (� walk�.
  have h_ind : ∀ (s t : HexVertex) (trail : hexGraph.Walk s t) (v : HexVertex), (vEdgeCount v trail) % 2 = ((if v = s then 1 else 0) + (if v = t then 1 else 0)) % 2 := by
    intro s t trail v; induction trail; aesop;
    unfold vEdgeCount at *;
    by_cases h : v = ‹_› <;> simp_all +decide [ List.filter_cons ];
    · split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · rename_i k hk₁ hk₂ hk;
        split_ifs at hk₂ <;> simp_all +decide [ Nat.add_mod ];
      · omega;
    · split_ifs at * <;> simp_all +decide [ Nat.add_mod ];
  grind +qlia

/-- For v ≠ start, outgoing trails have 1 or 3 v-edges.
    - 1 v-edge: triplet extension (v visited once, at the end)
    - 3 v-edges: pair member (v visited twice, all edges used) -/
lemma outgoing_trail_vEdge_classify {T L : ℕ} (v : HexVertex) (k : Fin 3)
    (γ : StripTrail T L v (hexNeighbors3 v k))
    (hv_ne_start : v ≠ paperStart)
    (h_nonempty : 0 < γ.walk.length) :
    vEdgeCount v γ.walk = 1 ∨ vEdgeCount v γ.walk = 3 := by
  have h_le := hex_edges_incident_le_three γ.walk γ.is_trail v
  have h_odd := vEdgeCount_odd_at_endpoint γ.walk γ.is_trail v hv_ne_start rfl
  -- vEdgeCount is odd and ≤ 3, so it's 1 or 3
  rcases h_odd with ⟨m, hm⟩
  have hle3 : vEdgeCount v γ.walk ≤ 3 := h_le
  rw [hm] at hle3
  have : m ≤ 1 := by omega
  interval_cases m <;> simp_all [hm]

/-! ## The vertex relation

The vertex relation at v states that the sum of direction-weighted
trail contributions over all mid-edges at v is zero. This follows from
the walk partition into cancelling triplets and pairs. -/

/-- Trail-based vertex relation sum at v. -/
def trailVertexSum (T L : ℕ) (v : HexVertex) : ℂ :=
  ∑ i : Fin 3, midEdgeDir v i *
    (trailObs T L v (hexNeighbors3 v i) + trailObs T L (hexNeighbors3 v i) v)

/-- **Lemma 1** (Cancellation Identity / Vertex Relation).
    For every interior vertex v ≠ paperStart, the trail-based vertex sum is zero.

    **WARNING**: This uses `trailVertexSum` (based on `StripTrail`), which includes
    non-fresh trails where the half-edge was already traversed. The vertex relation
    may NOT hold for this observable. The correct statement uses `freshVertexSum`
    (based on `FreshTrail`), proved as `fresh_vertex_relation` in
    `SAWPairInvolutionProof.lean`.

    This sorry is a **dead branch** — not on the critical path for the main theorem.
    The infrastructure in this file (StripTrail, tripletExtendStrip, etc.) is still
    used by other files through the import chain. -/
theorem trail_vertex_relation (T L : ℕ) (v : HexVertex)
    (hv_strip : PaperFinStrip T L v)
    (hv_ne_start : v ≠ paperStart)
    (h_nbrs_strip : ∀ i : Fin 3, PaperFinStrip T L (hexNeighbors3 v i)) :
    trailVertexSum T L v = 0 := by
  sorry

/-! ## Summary of the Cancellation Identity Formalization

### Fully proved (sorry-free):

**Algebraic cancellations** (from SAW.lean, SAWObservable.lean):
- `pair_cancellation`: j · conj(λ)⁴ + conj(j) · λ⁴ = 0
- `triplet_cancellation`: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0

**Direction vectors** (from SAWObservable.lean, SAWCancellationProof.lean):
- `midEdgeDir_j_relation`: d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex

**Trail extension** (this file + SAWTripletInStrip.lean):
- `tripletExtendStrip`: extension in the strip is well-defined
- `tripletExtendStrip_len`: extended trail has length ℓ+1
- `tripletExtendStrip_vEdge`: extension has exactly 1 v-edge

**Trail classification** (this file):
- `strip_trail_length_bound`: trails have bounded length in finite strip
- `strip_trail_finite`: strip trails form a finite type
- `three_vEdges_implies_two_visits`: 3 v-edges → vertex visited ≥ 2 times
- `trail_vEdge_le_two_interior`: interior vertices have ≤ 2 v-edges
- `incoming_trail_vEdge_classify`: incoming trails: 0 or 2 v-edges
- `vEdgeCount_odd_at_endpoint`: parity of v-edges at endpoint is odd
- `outgoing_trail_vEdge_classify`: outgoing trails: 1 or 3 v-edges

**Group cancellation** (this file + SAWCancellationLemma1.lean):
- `strip_triplet_zero`: each triplet contributes zero
- `strip_pair_zero`: each pair contributes zero

### Remaining sorry:
- `trail_vertex_relation`: the full walk partition bijection.
  All algebraic and classification ingredients are proved.
  The gap is the combinatorial argument showing every trail
  belongs to exactly one cancelling group.
-/

end