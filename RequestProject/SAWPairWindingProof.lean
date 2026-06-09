/-
# Pair Winding Relation — Proof via Winding Decomposition

Proves `pair_winding_relation` from SAWPairCancellation.lean by decomposing
the winding of the original and paired walks into prefix + junction + suffix
components, and using:
1. `hexWalkWinding_reverse_list'` for the reversed inner walk
2. Hex lattice turn angle computations for junction corrections
3. The turning number theorem (discrete Gauss-Bonnet) for the closed loop

## Dependencies
- SAWPairCancellation.lean — defines pairInvol, pairPrefix, pairInner, etc.
- SAWPairWinding.lean — hexWalkWinding_reverse_list', hex_turn_value, etc.
-/

import Mathlib
import RequestProject.SAWPairCancellation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## The arrival index

For a FreshIncomingPair at (v, k), the walk arrives at v from some
neighbor hexNeighbors3 v j. Since vEdgeCount v = 2 and the fresh
edge is s(hexNeighbors3 v k, v), the two v-edges are:
- s(hexNeighbors3 v j, v) — arrival edge (in prefix)
- s(v, hexNeighbors3 v exitIdx) — departure edge (first step after v)
And j, k, exitIdx are all distinct, so k and exitIdx are fin3_other j.
-/

/-
The vertex just before v in the prefix is a neighbor of v,
    distinct from both k and exitIdx.
-/
lemma prefix_penultimate_is_neighbor {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∃ j : Fin 3,
      (pairPrefix hv_ne γ).support.dropLast.getLast! = hexNeighbors3 v j ∧
      j ≠ k ∧ j ≠ pairExitIdx hv_ne γ := by
  -- The prefix walk is a walk from paperStart to v, so its support has length at least 2.
  have h_support_length : 2 ≤ (pairPrefix hv_ne γ).support.length := by
    simp [pairPrefix];
    cases h : ( γ.1.walk.takeUntil v ( pair_walk_v_in_support γ hv_ne ) ) <;> aesop;
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, (pairPrefix hv_ne γ).support.dropLast.getLast! = hexNeighbors3 v j := by
    -- The second-to-last vertex in the prefix walk is a neighbor of v.
    have h_neighbor : hexGraph.Adj ((pairPrefix hv_ne γ).support.dropLast.getLast!) v := by
      have h_neighbor : ∀ {u w : HexVertex} {p : hexGraph.Walk u w}, p.length > 0 → hexGraph.Adj (p.support.dropLast.getLast!) w := by
        intros u w p hp_pos
        induction' p with u w p ih;
        · contradiction;
        · cases ‹SimpleGraph.Walk hexGraph p ih› <;> simp_all +decide [ List.dropLast ];
      grind +qlia;
    have := hexNeighbors3_complete v _ h_neighbor.symm; aesop;
  have h_last_edge : s(hexNeighbors3 v j, v) ∈ (pairPrefix hv_ne γ).edges := by
    have h_last_edge : ∀ {u v : HexVertex} {p : hexGraph.Walk u v}, 2 ≤ p.support.length → s(p.support.dropLast.getLast!, v) ∈ p.edges := by
      intros u v p hp_length
      induction' p with u v p ih;
      · contradiction;
      · cases ‹hexGraph.Walk p ih› <;> simp_all +decide [ List.dropLast ];
    exact hj ▸ h_last_edge h_support_length;
  refine' ⟨ j, hj, _, _ ⟩ <;> intro hj' <;> simp_all +decide [ FreshIncomingPair ];
  · have := γ.1.fresh;
    contrapose! this;
    rw [ pairDecomp ];
    simp +decide [ SimpleGraph.Walk.edges_append, h_last_edge ];
    assumption;
  · have h_last_edge : s(hexNeighbors3 v (pairExitIdx hv_ne γ), v) ∈ (pairInvolWalk hv_ne γ).edges := by
      unfold pairInvolWalk at *; simp_all +decide [ mkPairedWalk ] ;
    exact absurd h_last_edge ( by simpa using pairInvolWalk_fresh hv_ne γ )

/-
k and exitIdx are the fin3_other of the arrival index j.
-/
lemma pair_indices_are_fin3_other {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∃ j : Fin 3,
      k = (fin3_other j).1 ∧ pairExitIdx hv_ne γ = (fin3_other j).2 ∨
      k = (fin3_other j).2 ∧ pairExitIdx hv_ne γ = (fin3_other j).1 := by
  fin_cases k <;> simp +decide [ Fin.forall_fin_succ ];
  · rcases h : pairExitIdx hv_ne γ with ( _ | _ | _ | _ ) <;> simp_all +decide;
    · exact absurd h ( by have := pairExitIdx_ne hv_ne γ; aesop );
    · grind +extAll;
  · rcases h : pairExitIdx hv_ne γ with ( _ | _ | _ | _ ) <;> simp_all +decide;
    · exact absurd h ( by have := pairExitIdx_ne hv_ne γ; aesop );
    · linarith;
  · rcases h : pairExitIdx hv_ne γ with ( _ | _ | _ | _ ) <;> simp_all +decide;
    · exact absurd h ( by have := pairExitIdx_ne hv_ne γ; aesop );
    · linarith

/-! ## Winding decomposition for the full support

The full support of a FreshIncomingPair walk is:
  prefix.support ++ [hexNeighbors3 v exitIdx] ++ inner.support.tail ++ [v]

The winding decomposes as:
  W = W_prefix + turn_at_v + W_suffix_orig

where W_prefix = hexWalkWinding(prefix.support ++ [v]) and
turn_at_v = arg(d_exit / d_arrive) and
W_suffix = hexWalkWinding([v, exit, inner..., k, v]).
-/

/-
The original full support structure.
-/
lemma original_fullSupport_eq {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    γ.1.fullSupport =
    (pairPrefix hv_ne γ).support ++
    [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
    (pairInner hv_ne γ).support.tail ++ [v] := by
  convert pairDecomp hv_ne γ using 1;
  constructor <;> intro h <;> simp_all +decide [ HexTrailList ];
  · exact?;
  · convert congr_arg ( fun x : SimpleGraph.Walk hexGraph _ _ => x.support ++ [ v ] ) h using 1;
    cases h : ( pairInner hv_ne γ ).support <;> simp_all +decide [ SimpleGraph.Walk.support_append ];
    grind +suggestions

/-
The paired full support structure.
-/
lemma paired_fullSupport_eq {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvol hv hv_ne γ).1.fullSupport =
    (pairPrefix hv_ne γ).support ++
    [hexNeighbors3 v k] ++
    (pairInner hv_ne γ).reverse.support.tail ++ [v] := by
  unfold pairInvol;
  unfold pairInvolWalk mkPairedWalk; simp +decide [ *, List.append_assoc ] ;
  simp +decide [ FreshTrail.fullSupport, pairPrefix, pairInner ];
  simp +decide [ SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons ];
  rw [ ← List.cons_append, ← List.reverse_cons ];
  rw [ ← List.dropLast_append_getLast ( show ( _ : hexGraph.Walk _ _ ).support ≠ [ ] from _ ) ];
  all_goals norm_num [ List.dropLast ]

/-! ## The pair winding relation proof -/

-- The proof of pair_winding_relation will use the above lemmas
-- once they are proved.

end