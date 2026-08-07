/-
# Edge counts at a vertex

Small additions to the `vEdgeCount` toolkit of `SAWWalkPartitionComplete.lean`
used by the two places where the local structure of a configuration at a vertex
of degree three has to be pinned down: the starting vertex (`SAWStartVertex.lean`)
and the loop of a pair (`SAWPairLoopOrientation.lean`).
-/

import Mathlib
import RequestProject.SAWVertexRelationProof

open Real Complex

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Only one edge at a vertex can survive two exclusions -/

/-- A trail avoiding two of the three edges at `v` uses at most one edge at
`v`. -/
lemma vEdgeCount_le_one_of_two_excluded {s t : HexVertex} {v : HexVertex} {i j : Fin 3}
    (hij : i ≠ j) (w : hexGraph.Walk s t) (hw : w.IsTrail)
    (hi : s(hexNeighbors3 v i, v) ∉ w.edges)
    (hj : s(hexNeighbors3 v j, v) ∉ w.edges) :
    vEdgeCount v w ≤ 1 := by
  classical
  obtain ⟨m, hmi, hmj⟩ :=
    (by decide : ∀ a b : Fin 3, a ≠ b → ∃ m : Fin 3, m ≠ a ∧ m ≠ b) i j hij
  have key : ∀ p : Fin 3, p ≠ i → p ≠ j → p = m :=
    (by decide : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b → ∀ p : Fin 3, p ≠ a → p ≠ b → p = c)
      i j m hij hmi hmj
  set l := w.edges.filter (fun e => v ∈ e) with hl
  have hnodup : l.Nodup := List.Nodup.filter _ hw.edges_nodup
  have hmem : ∀ e ∈ l, e = s(hexNeighbors3 v m, v) := by
    intro e he
    rw [hl, List.mem_filter] at he
    obtain ⟨he1, he2⟩ := he
    simp only [decide_eq_true_eq] at he2
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 he2
    have hadj : hexGraph.Adj v u := w.edges_subset_edgeSet he1
    obtain ⟨p, hp⟩ : ∃ p : Fin 3, u = hexNeighbors3 v p := by
      rcases hexNeighbors3_complete v u hadj with h | h | h
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
    subst hp
    have hpi : p ≠ i := by rintro rfl; exact hi (by rwa [Sym2.eq_swap])
    have hpj : p ≠ j := by rintro rfl; exact hj (by rwa [Sym2.eq_swap])
    rw [key p hpi hpj, Sym2.eq_swap]
  have hcard : l.toFinset ⊆ {s(hexNeighbors3 v m, v)} := by
    intro e he
    rw [List.mem_toFinset] at he
    simpa using hmem e he
  have hle := Finset.card_le_card hcard
  rw [List.toFinset_card_of_nodup hnodup, Finset.card_singleton] at hle
  exact hle

/-- A walk starting at `v` and using no edge at `v` is empty. -/
lemma walk_length_zero_of_vEdgeCount_zero {v t : HexVertex} (w : hexGraph.Walk v t)
    (h : vEdgeCount v w = 0) : w.length = 0 := by
  cases w with
  | nil => rfl
  | cons hadj q => simp [vEdgeCount] at h

/-- A walk visiting `v` away from its initial vertex uses an edge at `v`. -/
lemma vEdgeCount_pos_of_mem_support_ne_start :
    ∀ {s t : HexVertex} (p : hexGraph.Walk s t) (v : HexVertex),
      v ∈ p.support → v ≠ s → 0 < vEdgeCount v p := by
  intro s t p
  induction p with
  | nil =>
      intro v hv hne
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      exact absurd hv hne
  | @cons a b c h q ih =>
      intro v hv hne
      by_cases hvb : v = b
      · subst hvb
        simp [vEdgeCount]
      · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact absurd rfl hne
        · have := ih v hv hvb
          have hmono : vEdgeCount v q ≤ vEdgeCount v (SimpleGraph.Walk.cons h q) := by
            simp only [vEdgeCount, SimpleGraph.Walk.edges_cons, List.filter_cons]
            split <;> simp
          omega

/-- The number of edges of a walk incident to a vertex `v` has the parity of the
number of endpoints of the walk equal to `v`. -/
lemma vEdgeCount_parity : ∀ (s t : HexVertex) (w : hexGraph.Walk s t) (v : HexVertex),
    vEdgeCount v w % 2 = ((if v = s then 1 else 0) + (if v = t then 1 else 0)) % 2 := by
  intro s t trail v; induction trail; aesop
  unfold vEdgeCount at *
  by_cases h : v = ‹_› <;> simp_all +decide [List.filter_cons]
  · split_ifs <;> simp_all +decide [SimpleGraph.adj_comm]
    · rename_i k hk₁ hk₂ hk
      split_ifs at hk₂ <;> simp_all +decide [Nat.add_mod]
    · omega
  · split_ifs at * <;> simp_all +decide [Nat.add_mod]

end
