/-
# Vertex Relation Proof (Lemma 1) — Fresh Trail Observable

Proves the cancellation identity for the fresh trail observable:
  freshVertexSum T L v = 0

for every interior vertex v of the strip domain.

## Proof structure

The vertex sum decomposes into:
- **Triplet part**: 0-v-edge incoming roots + 1-v-edge outgoing extensions → 0
- **Pair part**: 2-v-edge incoming pairs → 0

## Main results

* `freshVertexSum_triplet_part_zero` — the triplet part vanishes
* `freshVertexSum_pair_part_zero` — the pair part vanishes
* `fresh_vertex_relation` — the full vertex relation (Lemma 1)
-/

import Mathlib
import RequestProject.SAWPathVertexRelation
import RequestProject.SAWTrailVertexRelation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Hex neighbor is not self -/

/-- n_i ≠ v for any hex neighbor. -/
lemma hexNeighbors3_ne_self' (v : HexVertex) (i : Fin 3) :
    hexNeighbors3 v i ≠ v := by
  rcases v with ⟨x, y, b⟩
  cases b <;> fin_cases i <;>
    simp [hexNeighbors3, trueNeighbors, falseNeighbors, HexVertex] <;>
    omega

/-! ## Fresh trail subtypes by v-edge count -/

/-- A fresh incoming root: FreshTrail at (n_ji, v) with 0 v-edges. -/
def FreshIncomingRoot (T L : ℕ) (v : HexVertex) (ji : Fin 3) :=
  {γ : FreshTrail T L (hexNeighbors3 v ji) v // vEdgeCount v γ.walk = 0}

/-- A fresh outgoing extension: FreshTrail at (v, n_k) with 1 v-edge. -/
def FreshOutgoingExt (T L : ℕ) (v : HexVertex) (k : Fin 3) :=
  {γ : FreshTrail T L v (hexNeighbors3 v k) // vEdgeCount v γ.walk = 1}

/-- A fresh incoming pair: FreshTrail at (n_ji, v) with 2 v-edges. -/
def FreshIncomingPair (T L : ℕ) (v : HexVertex) (ji : Fin 3) :=
  {γ : FreshTrail T L (hexNeighbors3 v ji) v // vEdgeCount v γ.walk = 2}

instance (T L : ℕ) (v : HexVertex) (ji : Fin 3) :
    Finite (FreshIncomingRoot T L v ji) := Subtype.finite
instance (T L : ℕ) (v : HexVertex) (k : Fin 3) :
    Finite (FreshOutgoingExt T L v k) := Subtype.finite
instance (T L : ℕ) (v : HexVertex) (ji : Fin 3) :
    Finite (FreshIncomingPair T L v ji) := Subtype.finite

/-! ## v-edge count classification for fresh trails -/

/-
Excluding one edge at v, at most 2 v-edges remain.
-/
lemma vEdgeCount_le_two_excluding {s t : HexVertex} (v : HexVertex) (j : Fin 3)
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (h_excl : s(hexNeighbors3 v j, v) ∉ trail.edges) :
    vEdgeCount v trail ≤ 2 := by
  have h_deg : (trail.edges.filter (fun e => v ∈ e)).toFinset.card ≤ 3 := by
    refine' le_trans _ ( hexGraph_degree v |> le_of_eq );
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun e => e ) ( hexGraph.incidenceFinset v );
    · intro e he; simp_all +decide [ SimpleGraph.incidenceSet ] ;
      exact trail.edges_subset_edgeSet he.1;
    · simp +decide [ SimpleGraph.incidenceFinset ];
  convert Nat.le_of_lt_succ _;
  convert lt_of_le_of_ne h_deg _;
  · rw [ List.toFinset_card_of_nodup ];
    · rfl;
    · exact List.Nodup.filter _ ( h_trail.edges_nodup );
  · intro h_card
    have h_all_edges : ∀ e : Sym2 HexVertex, e ∈ hexGraph.incidenceFinset v → e ∈ trail.edges := by
      intro e he
      have h_edge : e ∈ (trail.edges.filter (fun e => v ∈ e)).toFinset := by
        have h_edge : (trail.edges.filter (fun e => v ∈ e)).toFinset = hexGraph.incidenceFinset v := by
          refine' Finset.eq_of_subset_of_card_le _ _ <;> simp_all +decide [ Finset.subset_iff ];
          · simp +contextual [ SimpleGraph.incidenceSet ];
            exact fun x hx hx' => by simpa using trail.edges_subset_edgeSet hx;
          · exact le_of_eq ( hexGraph_degree v )
        generalize_proofs at *;
        exact h_edge.symm ▸ he
      generalize_proofs at *;
      aesop
    generalize_proofs at *;
    contrapose! h_all_edges; simp_all +decide [ HexVertex, Sym2 ] ;
    use s(hexNeighbors3 v j, v);
    simp_all +decide [ SimpleGraph.incidenceSet ];
    exact hexNeighbors3_adj v j |> fun h => h.symm

/-- For v ≠ start, fresh outgoing trails have vEdgeCount = 1. -/
lemma fresh_outgoing_vEdgeCount_one {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (γ : FreshTrail T L v (hexNeighbors3 v k))
    (hv_ne_start : v ≠ paperStart)
    (h_nonempty : 0 < γ.walk.length) :
    vEdgeCount v γ.walk = 1 := by
  have h_odd := vEdgeCount_odd_at_endpoint γ.walk γ.is_trail v hv_ne_start rfl
  -- Fresh: s(v, n_k) ∉ walk.edges. By Sym2 symmetry, s(n_k, v) ∉ walk.edges.
  have h_fresh : s(hexNeighbors3 v k, v) ∉ γ.walk.edges := by
    rw [Sym2.eq_swap]; exact γ.fresh
  have h_le := vEdgeCount_le_two_excluding v k γ.walk γ.is_trail h_fresh
  rcases h_odd with ⟨m, hm⟩
  rw [hm] at h_le; have : m = 0 := by omega
  subst this; simp at hm; exact hm

/-
For v ≠ start, fresh incoming trails have vEdgeCount ∈ {0, 2}.
-/
lemma fresh_incoming_vEdgeCount_classify {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (γ : FreshTrail T L (hexNeighbors3 v ji) v)
    (hv_ne_start : v ≠ paperStart) :
    vEdgeCount v γ.walk = 0 ∨ vEdgeCount v γ.walk = 2 := by
  have h_fresh : s(hexNeighbors3 v ji, v) ∉ γ.walk.edges := γ.fresh
  have h_le := vEdgeCount_le_two_excluding v ji γ.walk γ.is_trail h_fresh
  -- v ≠ start and v ≠ endpoint (n_ji), so vEdgeCount is even
  have h_ne_end : v ≠ hexNeighbors3 v ji := (hexNeighbors3_ne_self' v ji).symm
  have h_even : Even (vEdgeCount v γ.walk) := by
    -- Since v is an interior vertex, the vEdgeCount is even.
    have h_interior : v ≠ paperStart ∧ v ≠ hexNeighbors3 v ji := by
      grind;
    obtain ⟨h_ne_start, h_ne_end⟩ := h_interior;
    have := @incoming_trail_vEdge_classify T L;
    specialize this v ji ⟨γ.walk, γ.is_trail, γ.adj, γ.in_strip⟩ h_ne_start; aesop;
  rcases h_even with ⟨m, hm⟩
  have hm_le : m ≤ 1 := by omega
  interval_cases m <;> simp_all

/-! ## Decomposition of fresh observable -/

/-
The fresh observable decomposes by v-edge count at incoming mid-edges.
-/
lemma fresh_incoming_decompose (T L : ℕ) (v : HexVertex) (ji : Fin 3)
    (hv_ne_start : v ≠ paperStart) :
    freshObs T L (hexNeighbors3 v ji) v =
    ∑' (γ : FreshIncomingRoot T L v ji), γ.1.weight +
    ∑' (γ : FreshIncomingPair T L v ji), γ.1.weight := by
  have h_split : ∀ γ : FreshTrail T L (hexNeighbors3 v ji) v, γ.weight = (if vEdgeCount v γ.walk = 0 then γ.weight else 0) + (if vEdgeCount v γ.walk = 2 then γ.weight else 0) := by
    intro γ; specialize hv_ne_start; have := fresh_incoming_vEdgeCount_classify γ hv_ne_start; aesop;
  convert ( tsum_congr h_split ) using 1;
  rw [ Summable.tsum_add ];
  · congr! 1;
    · convert ( tsum_subtype _ _ ) using 1;
      simp +decide [ Set.indicator ];
      congr! 3;
    · convert ( tsum_subtype _ _ ) using 1;
      simp +decide [ Set.indicator ];
      congr! 3;
  · refine' summable_of_finite_support _;
    exact Set.toFinite _;
  · refine' summable_of_finite_support _;
    exact Set.toFinite _

/-
The fresh observable at outgoing mid-edges is the outgoing ext sum.
-/
lemma fresh_outgoing_decompose (T L : ℕ) (v : HexVertex) (k : Fin 3)
    (hv_ne_start : v ≠ paperStart) :
    freshObs T L v (hexNeighbors3 v k) =
    ∑' (γ : FreshOutgoingExt T L v k), γ.1.weight := by
  convert ( tsum_subtype _ _ ) using 1;
  convert rfl;
  rotate_left;
  convert ( tsum_subtype _ _ ) using 1;
  rw [ tsum_subtype ];
  refine' tsum_congr fun γ => _;
  by_cases h : vEdgeCount v γ.walk = 1 <;> simp +decide [ h ];
  · exact fun h' => False.elim <| h' h;
  · exact fun _ => False.elim <| h <| fresh_outgoing_vEdgeCount_one γ hv_ne_start <| by
      grind +suggestions

/-! ## Extension map -/

/-- The extension map sends a fresh incoming root to a fresh outgoing ext. -/
def freshExtensionMap {T L : ℕ} {v : HexVertex} {ji : Fin 3} (k : Fin 3)
    (hk : k ≠ ji) (hv : PaperFinStrip T L v)
    (γ : FreshIncomingRoot T L v ji) : FreshOutgoingExt T L v k :=
  ⟨freshExtend k γ.1 γ.2 hk hv,
   extension_adds_one_v_edge ji γ.1.walk γ.2⟩

/-
The extension map is injective.
-/
lemma freshExtensionMap_injective {T L : ℕ} {v : HexVertex} {ji : Fin 3} (k : Fin 3)
    (hk : k ≠ ji) (hv : PaperFinStrip T L v) :
    Function.Injective (freshExtensionMap k hk hv : FreshIncomingRoot T L v ji → FreshOutgoingExt T L v k) := by
  intro γ₁ γ₂ h_eq;
  injection h_eq;
  rename_i h_eq
  have h_walk_eq : γ₁.1.walk = γ₂.1.walk := by
    injection h_eq;
    rename_i h; replace h := congr_arg ( fun x => x.support ) h; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
    have h_walk_eq : ∀ {s t : HexVertex} {w₁ w₂ : hexGraph.Walk s t}, w₁.IsTrail → w₂.IsTrail → w₁.support = w₂.support → w₁ = w₂ := by
      intros s t w₁ w₂ hw₁ hw₂ h_support_eq; exact (by
      apply_rules [ SimpleGraph.Walk.support_injective ]);
    exact h_walk_eq γ₁.1.is_trail γ₂.1.is_trail h
  exact Subtype.ext (by
  cases γ₁_1 : γ₁.1 ; cases γ₂_1 : γ₂.1 ; aesop ( simp_config := { singlePass := true } ) ;)

/-
Every fresh outgoing ext comes from a fresh incoming root.
-/
lemma fresh_outgoing_surj {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart)
    (γ : FreshOutgoingExt T L v k) :
    ∃ (ji : Fin 3) (hji : ji ≠ k) (root : FreshIncomingRoot T L v ji),
      freshExtensionMap k hji.symm hv root = γ := by
  obtain ⟨ u, prefix_walk, hadj, hw, hw', h ⟩ := walk_decompose_last_trail γ.val.walk γ.val.is_trail ( Nat.pos_of_ne_zero ( by
    intro h; have := γ.2; simp_all +decide [ vEdgeCount ] ;
    grind ) )
  have hu.hex : ∃ ji : Fin 3, u = hexNeighbors3 v ji := by
    have := hexNeighbors3_complete v u hadj.symm;
    grind +qlia
  obtain ⟨ ji, rfl ⟩ := hu.hex;
  refine' ⟨ ji, _, ⟨ ⟨ prefix_walk, hw', hadj, h, _ ⟩, _ ⟩, _ ⟩
  all_goals generalize_proofs at *;
  · intro H; have := γ.2; simp_all +decide [ vEdgeCount_append ] ;
    have := γ.1.fresh; simp_all +decide [ SimpleGraph.Walk.edges_append ] ;
  · exact fun u hu => γ.val.in_strip u <| by aesop;
  · have := γ.2; simp_all +decide [ vEdgeCount_append ] ;
    simp_all +decide [ vEdgeCount ];
  · unfold freshExtensionMap;
    unfold freshExtend;
    congr;
    exact hw.symm

/-- The extension weight at k1 = (fin3_other ji).1. -/
lemma freshExtensionMap_weight_k1 {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (hv : PaperFinStrip T L v) (γ : FreshIncomingRoot T L v ji) :
    (freshExtensionMap (fin3_other ji).1 (fin3_other_fst_ne ji) hv γ).1.weight =
    walkWeight (γ.1.winding - Real.pi / 3) (γ.1.len + 1) xc sigma := by
  unfold freshExtensionMap FreshTrail.weight
  rw [freshExtend_winding_k, freshExtend_len]

/-- The extension weight at k2 = (fin3_other ji).2. -/
lemma freshExtensionMap_weight_k2 {T L : ℕ} {v : HexVertex} {ji : Fin 3}
    (hv : PaperFinStrip T L v) (γ : FreshIncomingRoot T L v ji) :
    (freshExtensionMap (fin3_other ji).2 (fin3_other_snd_ne ji) hv γ).1.weight =
    walkWeight (γ.1.winding + Real.pi / 3) (γ.1.len + 1) xc sigma := by
  unfold freshExtensionMap FreshTrail.weight
  rw [freshExtend_winding_l, freshExtend_len]

/-- The triplet contribution of a single root. -/
def rootTripletContrib {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (hv : PaperFinStrip T L v)
    (γ : FreshIncomingRoot T L v ji) : ℂ :=
  midEdgeDir v ji * γ.1.weight +
  midEdgeDir v (fin3_other ji).1 *
    (freshExtensionMap (fin3_other ji).1 (fin3_other_fst_ne ji) hv γ).1.weight +
  midEdgeDir v (fin3_other ji).2 *
    (freshExtensionMap (fin3_other ji).2 (fin3_other_snd_ne ji) hv γ).1.weight

/-- Each root's triplet contribution is zero. -/
lemma rootTripletContrib_zero {T L : ℕ} (v : HexVertex) (ji : Fin 3)
    (hv : PaperFinStrip T L v)
    (γ : FreshIncomingRoot T L v ji) :
    rootTripletContrib v ji hv γ = 0 := by
  unfold rootTripletContrib
  exact fresh_triplet_cancel v ji γ.1 γ.2 hv

/-- fin3_other covers: for k ≠ ji, k is either (fin3_other ji).1 or .2. -/
lemma fin3_other_covers (ji k : Fin 3) (hk : k ≠ ji) :
    k = (fin3_other ji).1 ∨ k = (fin3_other ji).2 := by
  fin_cases ji <;> fin_cases k <;> simp_all [fin3_other]

/-- The root index of a FreshOutgoingExt: the predecessor's neighbor index. -/
noncomputable def rootIndexOf {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart)
    (γ : FreshOutgoingExt T L v k) : Fin 3 :=
  (fresh_outgoing_surj hv hv_ne_start γ).choose

/-- The root index is not k. -/
lemma rootIndexOf_ne {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart)
    (γ : FreshOutgoingExt T L v k) :
    rootIndexOf hv hv_ne_start γ ≠ k :=
  (fresh_outgoing_surj hv hv_ne_start γ).choose_spec.choose

/-- The root of a FreshOutgoingExt. -/
noncomputable def rootOf {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart)
    (γ : FreshOutgoingExt T L v k) :
    FreshIncomingRoot T L v (rootIndexOf hv hv_ne_start γ) :=
  (fresh_outgoing_surj hv hv_ne_start γ).choose_spec.choose_spec.choose

/-- The extension of the root recovers the original. -/
lemma rootOf_spec {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart)
    (γ : FreshOutgoingExt T L v k) :
    freshExtensionMap k (rootIndexOf_ne hv hv_ne_start γ).symm hv
      (rootOf hv hv_ne_start γ) = γ :=
  (fresh_outgoing_surj hv hv_ne_start γ).choose_spec.choose_spec.choose_spec

/-- The sigma forward map. -/
noncomputable def sigmaExtMap {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) :
    (Σ (ji : {j : Fin 3 // j ≠ k}), FreshIncomingRoot T L v ji) →
    FreshOutgoingExt T L v k :=
  fun p => freshExtensionMap k p.1.2.symm hv p.2

/-- The sigma backward map. -/
noncomputable def sigmaRetMap {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    FreshOutgoingExt T L v k →
    (Σ (ji : {j : Fin 3 // j ≠ k}), FreshIncomingRoot T L v ji) :=
  fun γ => ⟨⟨rootIndexOf hv hv_ne_start γ, rootIndexOf_ne hv hv_ne_start γ⟩,
           rootOf hv hv_ne_start γ⟩

/-- Forward ∘ backward = id. -/
lemma sigmaExtMap_retMap {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart)
    (γ : FreshOutgoingExt T L v k) :
    sigmaExtMap hv (sigmaRetMap hv hv_ne_start γ) = γ := by
  unfold sigmaExtMap sigmaRetMap
  exact rootOf_spec hv hv_ne_start γ

/-- The sigma ext map is surjective. -/
lemma sigmaExtMap_surj {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    Function.Surjective (sigmaExtMap hv : _ → FreshOutgoingExt T L v k) :=
  fun γ => ⟨sigmaRetMap hv hv_ne_start γ, sigmaExtMap_retMap hv hv_ne_start γ⟩

/-
The sigma ext map is injective.
-/
lemma sigmaExtMap_inj {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) :
    Function.Injective (sigmaExtMap hv : _ → FreshOutgoingExt T L v k) := by
  intro x y;
  rcases x with ⟨ ⟨ j₁, hj₁ ⟩, γ₁ ⟩ ; rcases y with ⟨ ⟨ j₂, hj₂ ⟩, γ₂ ⟩ ; simp_all +decide [ sigmaExtMap ] ;
  intro h_eq
  have h_walk : γ₁.1.walk.append (.cons (hexNeighbors3_adj v j₁).symm .nil) = γ₂.1.walk.append (.cons (hexNeighbors3_adj v j₂).symm .nil) := by
    convert congr_arg ( fun x : FreshOutgoingExt T L v k => x.1.walk ) h_eq using 1;
  have h_last_edge : hexNeighbors3 v j₁ = hexNeighbors3 v j₂ := by
    replace h_walk := congr_arg ( fun x => x.support ) h_walk ; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
    have := congr_arg List.getLast? h_walk; simp +decide [ List.getLast?_eq_getElem? ] at this;
    exact this;
  have h_j_eq : j₁ = j₂ := by
    exact hexNeighbors3_injective v h_last_edge;
  have := freshExtensionMap_injective k ( by tauto ) hv; aesop;

/-
The outgoing ext sum splits by root index.
-/
lemma outExt_sum_split {T L : ℕ} {v : HexVertex} (k : Fin 3)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    ∑' (γ : FreshOutgoingExt T L v k), γ.1.weight =
    ∑ ji : Fin 3, if h : ji ≠ k then
      ∑' (γ : FreshIncomingRoot T L v ji),
        (freshExtensionMap k h.symm hv γ).1.weight
    else 0 := by
  have h_bij : Function.Bijective (sigmaExtMap hv : (Σ (ji : {j : Fin 3 // j ≠ k}), FreshIncomingRoot T L v ji) → FreshOutgoingExt T L v k) := by
    exact ⟨ sigmaExtMap_inj hv, sigmaExtMap_surj hv hv_ne_start ⟩;
  obtain ⟨g, hg⟩ := h_bij;
  rw [ ← Equiv.tsum_eq ( Equiv.ofBijective _ ⟨ g, hg ⟩ ) ];
  erw [ Summable.tsum_sigma' ];
  · fin_cases k <;> simp +decide [ Fin.sum_univ_three ];
    · rw [ Finset.sum_eq_add ( ⟨ 1, by decide ⟩ : { j : Fin 3 // j ≠ 0 } ) ( ⟨ 2, by decide ⟩ : { j : Fin 3 // j ≠ 0 } ) ] <;> simp +decide [ Finset.sum_singleton ];
      · rfl;
      · exact fun a ha₁ ha₂ ha₃ => False.elim <| ha₃ <| by fin_cases a <;> trivial;
    · rw [ Finset.sum_eq_add ( ⟨ 0, by decide ⟩ : { j : Fin 3 // j ≠ 1 } ) ( ⟨ 2, by decide ⟩ : { j : Fin 3 // j ≠ 1 } ) ] <;> simp +decide [ Finset.sum_range_succ ];
      · rfl;
      · exact fun a ha₁ ha₂ ha₃ => False.elim <| ha₃ <| by fin_cases a <;> trivial;
    · rw [ Finset.sum_eq_add ( ⟨ 0, by decide ⟩ : { x : Fin 3 // x ≠ 2 } ) ( ⟨ 1, by decide ⟩ : { x : Fin 3 // x ≠ 2 } ) ] <;> simp +decide [ Finset.sum_singleton ];
      · rfl;
      · exact fun a ha₁ ha₂ ha₃ => False.elim <| ha₃ <| by fin_cases a <;> trivial;
  · intro b; exact (by
    refine' summable_of_finite_support _;
    exact Set.toFinite _);
  · refine' summable_of_finite_support _;
    exact Set.toFinite _

/-! ## The triplet part of the vertex sum vanishes -/

/-
The triplet part of the fresh vertex sum vanishes.
-/
theorem freshVertexSum_triplet_part_zero (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    (∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingRoot T L v ji), γ.1.weight) +
    (∑ k : Fin 3, midEdgeDir v k *
      ∑' (γ : FreshOutgoingExt T L v k), γ.1.weight) = 0 := by
  rw [ Fin.sum_univ_three, Fin.sum_univ_three ];
  rw [ outExt_sum_split 0 hv hv_ne_start, outExt_sum_split 1 hv hv_ne_start, outExt_sum_split 2 hv hv_ne_start ] ; norm_num [ Fin.sum_univ_three ] ; ring!;
  simp +decide [ ← mul_add, ← tsum_mul_left ];
  have h_sum_zero : ∀ (ji : Fin 3) (γ : FreshIncomingRoot T L v ji), rootTripletContrib v ji hv γ = 0 := by
    grind +suggestions;
  have h_sum_zero : ∀ (ji : Fin 3), ∑' (γ : FreshIncomingRoot T L v ji), rootTripletContrib v ji hv γ = 0 := by
    aesop;
  simp +decide [ rootTripletContrib ] at h_sum_zero;
  convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) ( h_sum_zero 0 ) ( h_sum_zero 1 ) ) ( h_sum_zero 2 ) using 1 ; ring!;
  · rw [ Summable.tsum_add, Summable.tsum_add, Summable.tsum_add, Summable.tsum_add, Summable.tsum_add, Summable.tsum_add ];
    any_goals exact Summable.of_finite;
    ring!;
  · norm_num

/-! ## The pair part and the full vertex relation

The pair part of the vertex sum vanishes by the pair involution
+ winding relation (proved in SAWPairCancellation.lean).
The full vertex relation (fresh_vertex_relation) follows from
the triplet part (proved above) and the pair part.

These results are assembled in SAWPairCancellation.lean, which
imports this file and has access to the pair involution machinery.

The proof chain:
  pair_winding_relation (sorry: turning number theorem)
  → pair_contrib_cancels (proved)
  → freshVertexSum_pair_part_zero_proof (needs involution structure)
  → fresh_vertex_relation (needs both triplet + pair parts)
-/

/-! ## The vertex sum decomposes into triplet and pair parts -/

lemma freshVertexSum_decompose (T L : ℕ) (v : HexVertex)
    (hv_ne_start : v ≠ paperStart) :
    freshVertexSum T L v =
    ((∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingRoot T L v ji), γ.1.weight) +
     (∑ k : Fin 3, midEdgeDir v k *
      ∑' (γ : FreshOutgoingExt T L v k), γ.1.weight)) +
    (∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingPair T L v ji), γ.1.weight) := by
  unfold freshVertexSum
  simp_rw [fresh_outgoing_decompose T L v _ hv_ne_start,
           fresh_incoming_decompose T L v _ hv_ne_start, mul_add,
           Finset.sum_add_distrib]
  ring

end