/-
# Helper Lemmas for Pair Involution

Key helpers for proving involutivity of the pair involution.
-/

import Mathlib
import RequestProject.SAWPairCancellation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## v appears exactly once in the paired walk's support -/

/-
v does not appear in the suffix of the paired walk (after the junction).
-/
lemma v_not_in_paired_suffix {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    v ∉ (SimpleGraph.Walk.cons (hexNeighbors3_adj v k) (pairInner hv_ne γ).reverse).support.tail := by
  simp +zetaDelta at *;
  convert v_not_in_inner_support v k ( pairExitIdx hv_ne γ ) ( pairPrefix hv_ne γ ) ( pairInner hv_ne γ ) _ _ hv_ne using 1;
  · convert γ.1.is_trail using 1;
    exact Eq.symm (pairDecomp hv_ne γ);
  · convert γ.2 using 1;
    rw [ ← pairDecomp hv_ne γ ]

/-
v appears exactly once in takeUntil(v, γ.walk).support: at the end.
-/
lemma v_count_one_in_prefix {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairPrefix hv_ne γ).support.count v = 1 := by
  unfold pairPrefix
  convert pair_walk_v_in_support γ hv_ne using 1;
  constructor <;> intro h <;> simp_all +decide [ List.count ];
  · exact pair_walk_v_in_support γ hv_ne;
  · have h_count : ∀ {u w : HexVertex} {p : hexGraph.Walk u w} {v : HexVertex} (h : v ∈ p.support), List.count v (p.takeUntil v h).support = 1 := by
      intros u w p v hv; induction p <;> simp_all +decide [ SimpleGraph.Walk.takeUntil ] ;
      · cases hv;
        · erw [ List.count_cons ] ; aesop;
        · contradiction;
      · cases eq_or_ne ‹_› v <;> aesop;
    convert h_count h using 1

/-- The paired walk's support decomposes as prefix.support ++ suffix_tail. -/
lemma pairInvolWalk_support_eq {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvolWalk hv_ne γ).support =
    (pairPrefix hv_ne γ).support ++
    (SimpleGraph.Walk.cons (hexNeighbors3_adj v k) (pairInner hv_ne γ).reverse).support.tail := by
  unfold pairInvolWalk mkPairedWalk
  exact SimpleGraph.Walk.support_append _ _

/-- v appears exactly once in the paired walk's support. -/
lemma v_count_one_in_pairInvolWalk {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvolWalk hv_ne γ).support.count v = 1 := by
  rw [pairInvolWalk_support_eq]
  rw [List.count_append]
  have h1 := v_count_one_in_prefix hv_ne γ
  have h2 : (SimpleGraph.Walk.cons (hexNeighbors3_adj v k)
      (pairInner hv_ne γ).reverse).support.tail.count v = 0 := by
    rw [List.count_eq_zero]
    exact v_not_in_paired_suffix hv_ne γ
  omega

end