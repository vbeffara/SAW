/-
# Trail Structure on the Hexagonal Lattice

Key structural results about trails (edge-SAWs) on the 3-regular
hexagonal lattice, used in the proof of the cancellation identity.

## Main results

* `hex_trail_revisit_is_endpoint` — a trail revisiting v implies v ∈ {s, t}
* `hex_trail_interior_visit_bound` — interior vertex visited at most once
* `hex_edges_incident_le_three` — at most 3 incident edges in a trail
* `boundary_vertex_edge_bound` — boundary vertex has ≤ 2 trail edges
* `right_boundary_trail_is_path` — trail to right boundary in strip is a path
-/

import Mathlib
import RequestProject.SAWCancellationProof
import RequestProject.SAWWalkPartition

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Edge counting at a vertex on the hexagonal lattice -/

/-- The three edges at a hex vertex v are exactly the edges to its 3 neighbors. -/
lemma hex_edges_at_vertex (v : HexVertex) :
    ∀ w, hexGraph.Adj v w →
      w = hexNeighbors3 v 0 ∨ w = hexNeighbors3 v 1 ∨ w = hexNeighbors3 v 2 :=
  fun w h => hexNeighbors3_complete v w h

/-- Each vertex visit in a trail uses at least 2 incident edges
    (entering and leaving), except possibly the start/end vertex. -/
lemma trail_interior_vertex_uses_two_edges {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (v : HexVertex) (hv_supp : v ∈ trail.support)
    (hv_ne_s : v ≠ s) (hv_ne_t : v ≠ t) :
    ∃ e₁ e₂ : Sym2 HexVertex, e₁ ∈ trail.edges ∧ e₂ ∈ trail.edges ∧
      e₁ ≠ e₂ ∧ v ∈ e₁ ∧ v ∈ e₂ := by
  induction' trail with s t h w ih generalizing v
  · grind +suggestions
  · by_cases hv : v = h
    · cases ‹hexGraph.Walk h w› <;> simp_all +decide [SimpleGraph.Walk.isTrail_cons]
    · rename_i p hp
      specialize hp (by exact h_trail.of_cons) v
        (by cases hv_supp <;> aesop) hv hv_ne_t
      aesop

/-- An edge incident to v in a trail has v adjacent to the other endpoint. -/
lemma trail_edge_incident_adj {s t : HexVertex}
    (trail : hexGraph.Walk s t) (e : Sym2 HexVertex)
    (he : e ∈ trail.edges) (v : HexVertex) (hv : v ∈ e) :
    ∃ w, hexGraph.Adj v w ∧ e = s(v, w) := by
  grind +suggestions

/-- At most 3 edges incident to v appear in any trail. -/
lemma hex_edges_incident_le_three {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail) (v : HexVertex) :
    (trail.edges.filter (fun e => v ∈ e)).length ≤ 3 := by
  have h_sub : (List.filter (fun e => decide (v ∈ e)) trail.edges).toFinset ⊆
      Finset.image (fun n => s(v, n))
        ({hexNeighbors3 v 0, hexNeighbors3 v 1, hexNeighbors3 v 2} : Finset HexVertex) := by
    intro e he
    obtain ⟨w, hw⟩ : ∃ w, hexGraph.Adj v w ∧ e = s(v, w) := by
      have := trail_edge_incident_adj trail e (by aesop) v; aesop
    have := hex_edges_at_vertex v w hw.1; aesop
  convert Finset.card_le_card h_sub using 1
  · rw [List.toFinset_card_of_nodup]
    exact List.Nodup.filter _ h_trail.edges_nodup
  · rw [Finset.card_image_of_injOn] <;> norm_num [Function.Injective, hexNeighbors3]
    split_ifs <;> simp +decide [trueNeighbors, falseNeighbors]
    grind

/-! ## Main revisit theorem -/

/-
On the 3-regular hex lattice, if count(v) ≥ 2 in a trail, then v ∈ {s, t}.
-/
theorem hex_trail_revisit_is_endpoint {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (v : HexVertex) (h_count : 2 ≤ trail.support.count v) :
    v = s ∨ v = t := by
  by_contra h
  push_neg at h
  have := trail_interior_vertex_uses_two_edges trail h_trail v
    (by exact List.count_pos_iff.mp (by omega)) h.1 h.2
  obtain ⟨e₁, e₂, he₁, he₂, hne, hv₁, hv₂⟩ := this
  have h3 := hex_edges_incident_le_three trail h_trail v
  have h_degree : ∀ {u w : HexVertex} {p : hexGraph.Walk u w}, v ∈ p.support → (List.count v p.support) * 2 ≤ (List.filter (fun e => v ∈ e) p.edges).length + (if v = u then 1 else 0) + (if v = w then 1 else 0) := by
    intros u w p hp
    induction' p with u w p ih;
    · aesop;
    · by_cases hv : v = w <;> simp_all +decide [ List.count_cons ];
      · by_cases hw : w ∈ ( ‹hexGraph.Walk p ih› ).support <;> simp_all +decide [ List.count_eq_zero_of_not_mem ];
        · split_ifs at * <;> simp_all +decide [ SimpleGraph.Walk.edges ];
          · grind +qlia;
          · grind +splitIndPred;
        · grind;
      · grind;
  grind

/-- Interior vertices (v ≠ s, v ≠ t) are visited at most once by a trail. -/
lemma hex_trail_interior_visit_bound {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (v : HexVertex) (hv_ne_s : v ≠ s) (hv_ne_t : v ≠ t) :
    trail.support.count v ≤ 1 := by
  by_contra h
  push_neg at h
  rcases hex_trail_revisit_is_endpoint trail h_trail v (by omega) with rfl | rfl
  · exact absurd rfl hv_ne_s
  · exact absurd rfl hv_ne_t

/-! ## Retraction of outgoing trails -/

/-- Decompose a nonempty trail at its last edge. -/
lemma outgoing_trail_predecessor {s v : HexVertex}
    (trail : hexGraph.Walk s v) (h_trail : trail.IsTrail)
    (h_len : 0 < trail.length) :
    ∃ (w : HexVertex) (prefix_walk : hexGraph.Walk s w),
      prefix_walk.IsTrail ∧ hexGraph.Adj w v ∧
      trail.length = prefix_walk.length + 1 ∧
      s(w, v) ∉ prefix_walk.edges :=
  trail_to_v_has_predecessor trail h_trail h_len

/-- The predecessor is one of v's three named neighbors. -/
lemma outgoing_trail_predecessor_named {s v : HexVertex}
    (trail : hexGraph.Walk s v) (h_trail : trail.IsTrail)
    (h_len : 0 < trail.length) :
    ∃ (k : Fin 3) (prefix_walk : hexGraph.Walk s (hexNeighbors3 v k)),
      prefix_walk.IsTrail ∧
      trail.length = prefix_walk.length + 1 ∧
      s(hexNeighbors3 v k, v) ∉ prefix_walk.edges :=
  predecessor_is_named_neighbor trail h_trail h_len

/-! ## Strip boundary structure -/

/-- Right boundary exterior neighbor. -/
lemma right_boundary_exterior_neighbor (T : ℕ) (_ : 1 ≤ T)
    (x y : ℤ) (h_diag : x + y = -(T : ℤ)) :
    ¬ PaperInfStrip T (x, y, true) := by
  unfold PaperInfStrip; simp; omega

/-- Left boundary exterior neighbor. -/
lemma left_boundary_exterior_neighbor (T : ℕ) (_ : 1 ≤ T)
    (x y : ℤ) (h_diag : x + y = 0) :
    ¬ PaperInfStrip T (x, y, false) := by
  unfold PaperInfStrip; simp; omega

/-- If a trail stays in PaperInfStrip T, both endpoints of any edge are in the strip. -/
lemma trail_edge_endpoints_in_strip {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_stay : ∀ u ∈ trail.support, PaperInfStrip T u)
    {v w : HexVertex} (he : s(v, w) ∈ trail.edges) :
    PaperInfStrip T v ∧ PaperInfStrip T w := by
  grind +suggestions

/-
A boundary vertex (with exterior neighbor) has ≤ 2 edges in a strip trail.
-/
lemma boundary_vertex_edge_bound (T : ℕ) {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (h_stay : ∀ u ∈ trail.support, PaperInfStrip T u)
    (v : HexVertex) (w_ext : HexVertex)
    (h_adj : hexGraph.Adj v w_ext) (h_ext : ¬ PaperInfStrip T w_ext) :
    (trail.edges.filter (fun e => v ∈ e)).length ≤ 2 := by
  -- Each edge incident to v in the trail is of the form s(v, w) where w is adjacent to v and w ≠ w_ext.
  have h_edges_form : ∀ e ∈ trail.edges, v ∈ e → ∃ w, hexGraph.Adj v w ∧ e = s(v, w) ∧ w ≠ w_ext := by
    grind +suggestions;
  -- Since w is adjacent to v and w ≠ w_ext, w must be one of the remaining two neighbors of v.
  have h_edges_bound : ∀ e ∈ trail.edges, v ∈ e → e ∈ Finset.image (fun w => s(v, w)) (Finset.filter (fun w => hexGraph.Adj v w ∧ w ≠ w_ext) (Finset.image (fun k => hexNeighbors3 v k) (Finset.univ : Finset (Fin 3)))) := by
    intros e he hv; obtain ⟨ w, hw₁, rfl, hw₂ ⟩ := h_edges_form e he hv; simp_all +decide [ Finset.mem_image ] ;
    rcases hexNeighbors3_complete v w hw₁ with ( rfl | rfl | rfl ) <;> simp_all +decide [ Fin.exists_fin_succ ] ;
    · grind +qlia;
    · grind +splitImp;
    · grind +qlia;
  have h_edges_bound : (List.filter (fun e => v ∈ e) trail.edges).toFinset.card ≤ 2 := by
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun w => s(v, w) ) ( Finset.filter ( fun w => hexGraph.Adj v w ∧ w ≠ w_ext ) ( Finset.image ( fun k => hexNeighbors3 v k ) Finset.univ ) );
    · intro e he; aesop;
    · refine' Finset.card_image_le.trans _;
      refine' Nat.le_of_lt_succ ( lt_of_lt_of_le ( Finset.card_lt_card ( Finset.filter_ssubset.mpr _ ) ) _ ) <;> norm_num [ Finset.card_image_of_injective, hexNeighbors3_injective ];
      have := hex_edges_at_vertex v w_ext h_adj; aesop;
  rwa [ List.toFinset_card_of_nodup ] at h_edges_bound;
  exact List.Nodup.filter _ ( h_trail.edges_nodup )

/-! ## Boundary endpoint revisit bound -/

/-
A boundary endpoint (v = s or v = t, with s ≠ t) can't be revisited
    if it has an exterior neighbor: the trail needs ≥ 3 edges at v for
    count ≥ 2, but only 2 are available inside the strip.
-/
lemma boundary_endpoint_count_le_one (T : ℕ) {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (h_stay : ∀ u ∈ trail.support, PaperInfStrip T u)
    (h_st : s ≠ t)
    (v : HexVertex)
    (w_ext : HexVertex) (h_adj : hexGraph.Adj v w_ext)
    (h_ext : ¬ PaperInfStrip T w_ext)
    (h_ep : v = s ∨ v = t) :
    trail.support.count v ≤ 1 := by
  have h_count_le_three : (List.filter (fun e => v ∈ e) trail.edges).length ≤ 2 := by
    apply boundary_vertex_edge_bound T trail h_trail h_stay v w_ext h_adj h_ext;
  have h_count_le_three : (List.filter (fun e => v ∈ e) trail.edges).length = (List.count v (SimpleGraph.Walk.support trail)) * 2 - (if v = s then 1 else 0) - (if v = t then 1 else 0) := by
    have h_count_le_three : ∀ {u : HexVertex} {w : HexVertex} {p : SimpleGraph.Walk hexGraph u w}, p.IsTrail → (List.filter (fun e => v ∈ e) p.edges).length = (List.count v p.support * 2 - (if v = u then 1 else 0) - (if v = w then 1 else 0)) := by
      intros u w p hp_trail; induction' p with u w p ih <;> simp_all +decide [ SimpleGraph.Walk.support ] ;
      · grind;
      · by_cases hvw : v = w <;> by_cases hvp : v = p <;> simp_all +decide [ List.count_cons ];
        · split_ifs <;> simp_all +decide [ Nat.mul_succ ];
          · rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr _ ) ];
            simp_all +decide [ List.count_eq_zero ];
          · ring;
        · split_ifs <;> simp_all +decide [ List.count ];
          · rw [ Nat.sub_add_cancel ];
            refine' Nat.le_sub_one_of_lt ( Nat.le_trans _ ( Nat.mul_le_mul_right _ ( List.countP_pos_iff.mpr _ ) ) ) <;> norm_num;
          · rw [ Nat.sub_add_cancel ];
            exact Nat.mul_pos ( List.countP_pos_iff.mpr ⟨ p, by aesop ⟩ ) zero_lt_two;
        · grind;
    exact h_count_le_three h_trail;
  grind

/-
A trail between two boundary vertices (s ≠ t), staying in the strip, is a path.
-/
theorem strip_trail_boundary_endpoints_is_path (T : ℕ) {s t : HexVertex}
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (h_stay : ∀ u ∈ trail.support, PaperInfStrip T u)
    (h_st : s ≠ t)
    (ws_ext : HexVertex) (hs_adj : hexGraph.Adj s ws_ext)
    (hs_ext : ¬ PaperInfStrip T ws_ext)
    (wt_ext : HexVertex) (ht_adj : hexGraph.Adj t wt_ext)
    (ht_ext : ¬ PaperInfStrip T wt_ext) :
    trail.IsPath := by
  -- For any vertex v in the support of the trail, the count of v is at most 1.
  have h_count_le_one : ∀ v ∈ trail.support, trail.support.count v ≤ 1 := by
    intro v hv
    by_cases hv_eq_s : v = s
    by_cases hv_eq_t : v = t;
    · grind;
    · grind +suggestions;
    · grind +suggestions;
  grind +suggestions

/-
A trail from paperStart to a right boundary FALSE vertex in PaperInfStrip T
    (with T ≥ 1) is a path (no vertex revisited).
-/
theorem right_boundary_trail_is_path (T : ℕ) (hT : 1 ≤ T)
    (x y : ℤ) (h_diag : x + y = -(T : ℤ))
    (trail : hexGraph.Walk paperStart (x, y, false))
    (h_trail : trail.IsTrail)
    (h_stay : ∀ u ∈ trail.support, PaperInfStrip T u) :
    trail.IsPath := by
  convert strip_trail_boundary_endpoints_is_path T _ _ _ _;
  convert Iff.rfl;
  rotate_left;
  exact ( 0, 0, true );
  exact ( x, y, false );
  exact trail;
  · assumption;
  · assumption;
  · grind;
  · constructor <;> intro h <;> contrapose! h <;> simp_all +decide [ SimpleGraph.Walk.cons ];
    · refine' ⟨ 0, 0, Or.inl ⟨ _, _, _ ⟩ ⟩ <;> norm_num [ hexGraph ];
      · exact left_boundary_exterior_neighbor T hT 0 0 ( by norm_num );
      · exact ⟨ x, y, Or.inl ⟨ rfl, rfl ⟩, right_boundary_exterior_neighbor T hT x y h_diag ⟩;
    · grind

end