/-
# Pair Involution for the Cancellation Identity

Constructs the loop-reversal involution on FreshIncomingPair walks.
This file provides the infrastructure for proving that the pair part
of the vertex relation sum vanishes.

## Proved lemmas (sorry-free)
* `v_in_support_of_two_v_edges` — 2 v-edges implies v in trail support
* `pair_walk_v_in_support` — v in support for FreshIncomingPair walks
* `pair_suffix_nonempty` — the suffix from v to endpoint is nonempty
* `pair_exit_neighbor` — identifies the exit direction from v
* `mkPairedWalk` — constructs the loop-reversed walk
* `mkPairedWalk_length` — the paired walk has the right length
* `mkPairedWalk_in_strip` — the paired walk stays in the strip
* `mkPairedWalk_fresh` — the paired walk has the correct fresh edge
* `mkPairedWalk_two_v_edges` — the paired walk has 2 v-edges
* `vEdgeCount_ge_one_end` — nonempty walk ending at v has ≥ 1 v-edge
* `vEdgeCount_cons_start` — vEdgeCount of cons decomposes additively
* `v_mem_sym2_self` — v ∈ s(v, n) always
* `vEdgeCount_zero_of_not_in_support` — v ∉ support → 0 v-edges
* `v_not_in_inner_support` — v is not in the inner walk's support

## Status
All lemmas are sorry-free. `mkPairedWalk_is_trail` was proved using the
freshness condition to establish that the swapped edge is not already
present. `freshVertexSum_pair_part_zero_proved` follows from
`freshVertexSum_pair_part_zero` in SAWVertexRelationProof.lean.
-/

import Mathlib
import RequestProject.SAWVertexRelationProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Walk decomposition at an interior vertex -/

/-- For a trail with 2 v-edges, v is in the support. -/
lemma v_in_support_of_two_v_edges {s t : HexVertex} (v : HexVertex)
    (trail : hexGraph.Walk s t) (h_trail : trail.IsTrail)
    (h_two : vEdgeCount v trail = 2) (hs : v ≠ s) (ht : v ≠ t) :
    v ∈ trail.support := by
  contrapose! h_two; simp_all +decide [ vEdgeCount ] ;
  rw [ List.filter_eq_nil_iff.mpr ] <;> simp_all +decide [ PaperFinStrip ]
  intro e he hv; have := trail.edges_subset_edgeSet he; simp_all +decide [ hexGraph ] ;
  have h_support : ∀ {u w : HexVertex} {p : hexGraph.Walk u w}, e ∈ p.edges → v ∈ p.support := by
    intros u w p hp; induction p <;> aesop;
  exact h_two <| h_support he

/-- v is in the support of a FreshIncomingPair walk. -/
lemma pair_walk_v_in_support {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (γ : FreshIncomingPair T L v k) (hv_ne_start : v ≠ paperStart) :
    v ∈ γ.1.walk.support :=
  v_in_support_of_two_v_edges v γ.1.walk γ.1.is_trail γ.2 hv_ne_start
    (hexNeighbors3_ne_self' v k).symm

/-- The suffix is nonempty. -/
lemma pair_suffix_nonempty {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (γ : FreshIncomingPair T L v k) (hv_ne_start : v ≠ paperStart) :
    0 < (γ.1.walk.dropUntil v (pair_walk_v_in_support γ hv_ne_start)).length := by
  have h_ne : v ≠ hexNeighbors3 v k := (hexNeighbors3_ne_self' v k).symm
  have : ∀ {s t : HexVertex} {p : hexGraph.Walk s t}, s ≠ t → 0 < p.length :=
    fun {s t p} hst => by induction p <;> aesop
  exact this h_ne

/-
The exit direction from v.
-/
lemma pair_exit_neighbor {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (γ : FreshIncomingPair T L v k) (hv_ne_start : v ≠ paperStart) :
    ∃ (exit_idx : Fin 3) (_ : exit_idx ≠ k),
      ∃ (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k)),
        γ.1.walk.dropUntil v (pair_walk_v_in_support γ hv_ne_start) =
          (.cons (hexNeighbors3_adj v exit_idx) inner) := by
  obtain ⟨exit_idx, h_exit⟩ : ∃ exit_idx, ∃ inner, (γ.1.walk.dropUntil v (pair_walk_v_in_support γ hv_ne_start)) = SimpleGraph.Walk.cons (hexNeighbors3_adj v exit_idx) inner := by
    rcases γ with ⟨ γ, hγ ⟩;
    obtain ⟨exit_idx, h_exit⟩ : ∃ exit_idx, ∃ inner, (γ.walk.dropUntil v (pair_walk_v_in_support ⟨γ, hγ⟩ hv_ne_start)) = SimpleGraph.Walk.cons (hexNeighbors3_adj v exit_idx) inner := by
      have h_suffix_nonempty : 0 < (γ.walk.dropUntil v (pair_walk_v_in_support ⟨γ, hγ⟩ hv_ne_start)).length := by
        exact pair_suffix_nonempty ⟨ γ, hγ ⟩ hv_ne_start
      have h_suffix_nonempty : ∀ {s t : HexVertex} {w : hexGraph.Walk s t}, 0 < w.length → ∃ exit_idx, ∃ inner, w = SimpleGraph.Walk.cons (hexNeighbors3_adj s exit_idx) inner := by
        intros s t w hw_pos
        induction' w with s t w ih;
        · contradiction;
        · rename_i h₁ h₂ h₃;
          have := hexNeighbors3_complete t w h₁;
          rcases this with ( rfl | rfl | rfl ) <;> [ exact ⟨ 0, h₂, rfl ⟩ ; exact ⟨ 1, h₂, rfl ⟩ ; exact ⟨ 2, h₂, rfl ⟩ ];
      exact h_suffix_nonempty ‹_›;
    exact ⟨ exit_idx, h_exit ⟩;
  refine' ⟨ exit_idx, _, h_exit ⟩;
  intro h_eq_k
  have h_edge : Sym2.mk (v, hexNeighbors3 v k) ∈ γ.1.walk.edges := by
    obtain ⟨ inner, h_inner ⟩ := h_exit;
    rw [ ← SimpleGraph.Walk.take_spec ( γ.1.walk ) ( pair_walk_v_in_support γ hv_ne_start ) ] ; simp_all +decide [ SimpleGraph.Walk.edges ] ;
  exact γ.1.fresh ( by simpa [ Sym2.eq_swap ] using h_edge )

/-! ## Constructing the paired walk -/

/-- Construct the loop-reversed walk from prefix and inner. -/
noncomputable def mkPairedWalk
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k)) :
    hexGraph.Walk paperStart (hexNeighbors3 v exit_idx) :=
  prefix_walk.append (.cons (hexNeighbors3_adj v k) inner.reverse)

/-- The paired walk length. -/
lemma mkPairedWalk_length
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k)) :
    (mkPairedWalk v k exit_idx prefix_walk inner).length =
    prefix_walk.length + inner.length + 1 := by
  unfold mkPairedWalk
  simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

/-! ## Properties of the paired walk -/

/-
The paired walk is a trail.
    Key insight: the original edges are prefix.edges ++ [s(v,n_exit)] ++ inner.edges (nodup).
    The paired edges are prefix.edges ++ [s(v,n_k)] ++ inner.edges.reverse.
    Since s(v,n_k) ∉ original edges (freshness) and inner.edges.reverse is a permutation
    of inner.edges, the paired edges are also nodup.
-/
lemma mkPairedWalk_is_trail
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k))
    (h_orig_trail : (prefix_walk.append
      (.cons (hexNeighbors3_adj v exit_idx) inner)).IsTrail)
    (h_fresh_k : s(hexNeighbors3 v k, v) ∉
      (prefix_walk.append (.cons (hexNeighbors3_adj v exit_idx) inner)).edges)
    (hv_ne_start : v ≠ paperStart) :
    (mkPairedWalk v k exit_idx prefix_walk inner).IsTrail := by
  unfold mkPairedWalk; simp_all +decide [ SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons ] ;
  rw [ SimpleGraph.Walk.isTrail_def ] at *;
  simp_all +decide [ SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, List.nodup_append ];
  grind +ring

/-
A nonempty walk ending at v has at least 1 v-edge.
-/
lemma vEdgeCount_ge_one_end {s : HexVertex} (v : HexVertex)
    (p : hexGraph.Walk s v) (h : 0 < p.length) :
    1 ≤ vEdgeCount v p := by
  contrapose! h; simp_all +decide [ vEdgeCount ] ;
  induction' p with s t p ih <;> simp_all +decide [ vEdgeCount ];
  cases ‹hexGraph.Walk p ih› <;> aesop

/-
The cons edge v → n has v in it, contributing 1 to vEdgeCount.
-/
lemma vEdgeCount_cons_start (v : HexVertex) (n : HexVertex) (hadj : hexGraph.Adj v n)
    (rest : hexGraph.Walk n t) :
    vEdgeCount v (.cons hadj rest) = (if v ∈ s(v, n) then 1 else 0) + vEdgeCount v rest := by
  unfold vEdgeCount; split_ifs <;> simp +decide [ *, Finset.range_add_one ] ;
  ring

/-- v is always in s(v, n). -/
lemma v_mem_sym2_self (v n : HexVertex) : v ∈ s(v, n) := by
  exact Sym2.mem_iff.mpr (Or.inl rfl)

/-
If v ∉ inner.support and v ≠ start of inner, then vEdgeCount v inner = 0.
-/
lemma vEdgeCount_zero_of_not_in_support {s t : HexVertex} (v : HexVertex)
    (p : hexGraph.Walk s t) (hv : v ∉ p.support) :
    vEdgeCount v p = 0 := by
  have h_support : ∀ (v : HexVertex) (s t : HexVertex) (w : hexGraph.Walk s t), v ∉ w.support → vEdgeCount v w = 0 := by
    intros v s t w hv; induction w <;> simp_all +decide [ vEdgeCount ] ;
    cases ‹hexGraph.Walk _ _› <;> aesop;
  exact h_support v s t p hv

/-
v does not appear in inner walk's support.
-/
lemma v_not_in_inner_support
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k))
    (h_orig_trail : (prefix_walk.append
      (.cons (hexNeighbors3_adj v exit_idx) inner)).IsTrail)
    (h_two : vEdgeCount v (prefix_walk.append
      (.cons (hexNeighbors3_adj v exit_idx) inner)) = 2)
    (hv_ne_start : v ≠ paperStart) :
    v ∉ inner.support := by
  intro hv_in_inner_support
  have h_vEdgeCount_inner : 1 ≤ vEdgeCount v inner := by
    by_cases hv_start : v = hexNeighbors3 v exit_idx;
    · exact absurd hv_start ( Ne.symm ( hexNeighbors3_ne_self' v exit_idx ) );
    · -- Since v is in the support of inner and v is not the start of inner, there must be at least one edge in inner that connects to v.
      have h_edge_count : ∃ e ∈ inner.edges, v ∈ e := by
        have h_edge_count : ∀ {s t : HexVertex} {p : hexGraph.Walk s t}, v ∈ p.support → v ≠ s → ∃ e ∈ p.edges, v ∈ e := by
          intros s t p hv_support hv_ne_start
          induction' p with s t p ih
          generalize_proofs at *; (
          aesop);
          by_cases hv_eq_p : v = p <;> simp_all +decide [ SimpleGraph.Walk.support ]
        generalize_proofs at *; (
        exact h_edge_count hv_in_inner_support hv_start);
      exact List.length_pos_iff.mpr ( by aesop )
  generalize_proofs at *;
  have h_vEdgeCount_prefix : 1 ≤ vEdgeCount v prefix_walk := by
    apply vEdgeCount_ge_one_end v prefix_walk (by
    cases prefix_walk <;> aesop_cat)
  generalize_proofs at *; (
  grind +suggestions)

/-
The paired walk stays in the strip.
-/
lemma mkPairedWalk_in_strip {T L : ℕ}
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k))
    (h_strip : ∀ u ∈ (prefix_walk.append
      (.cons (hexNeighbors3_adj v exit_idx) inner)).support,
      PaperFinStrip T L u) :
    ∀ u ∈ (mkPairedWalk v k exit_idx prefix_walk inner).support,
      PaperFinStrip T L u := by
  unfold mkPairedWalk at * ; simp_all +decide [ SimpleGraph.Walk.support_append ]

/-
The paired walk has {exit_idx, v} fresh.
-/
lemma mkPairedWalk_fresh
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k))
    (h_orig_fresh : s(hexNeighbors3 v k, v) ∉
      (prefix_walk.append (.cons (hexNeighbors3_adj v exit_idx) inner)).edges)
    (h_orig_trail : (prefix_walk.append
      (.cons (hexNeighbors3_adj v exit_idx) inner)).IsTrail) :
    s(hexNeighbors3 v exit_idx, v) ∉
      (mkPairedWalk v k exit_idx prefix_walk inner).edges := by
  simp_all +decide [ mkPairedWalk, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons ];
  simp_all +decide [ SimpleGraph.Walk.isTrail_def ];
  grind

/-
The paired walk has 2 v-edges.
-/
lemma mkPairedWalk_two_v_edges
    (v : HexVertex) (k exit_idx : Fin 3)
    (prefix_walk : hexGraph.Walk paperStart v)
    (inner : hexGraph.Walk (hexNeighbors3 v exit_idx) (hexNeighbors3 v k))
    (h_orig_two : vEdgeCount v (prefix_walk.append
      (.cons (hexNeighbors3_adj v exit_idx) inner)) = 2) :
    vEdgeCount v (mkPairedWalk v k exit_idx prefix_walk inner) = 2 := by
  unfold mkPairedWalk;
  unfold vEdgeCount at *;
  simp_all +decide [ SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons ]

/-! ## Main theorem -/

/-
**The pair part of the vertex relation sum vanishes.**
-/
theorem freshVertexSum_pair_part_zero_proved (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    ∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingPair T L v ji), γ.1.weight = 0 := by
  convert freshVertexSum_pair_part_zero T L v hv hv_ne_start using 1

end