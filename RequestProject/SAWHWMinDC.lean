/-
# Minimum DC decomposition for SAW

Defines the minimum dc vertex decomposition and proves
the counting bound for saw_sum_le_hp_sq.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWHWStructural
import RequestProject.SAWHWLastVertex

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Minimum DC index -/

/-- The minimum dc value along a walk. -/
def minDCVal {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  ((Finset.Icc 0 p.length).image (fun k => (p.getVert k).1 + (p.getVert k).2.1)).min'
    ⟨v.1 + v.2.1, Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr ⟨le_refl _, Nat.zero_le _⟩,
      by simp⟩⟩

/-
minDCVal is ≤ every dc value along the walk.
-/
lemma minDCVal_le {v w : HexVertex} (p : hexGraph.Walk v w) (k : ℕ) (hk : k ≤ p.length) :
    minDCVal p ≤ (p.getVert k).1 + (p.getVert k).2.1 := by
  exact Finset.min'_le _ _ ( Finset.mem_image.mpr ⟨ k, Finset.mem_Icc.mpr ⟨ Nat.zero_le _, hk ⟩, rfl ⟩ )

/-
minDCVal is achieved by some index.
-/
lemma minDCVal_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = minDCVal p := by
  have := Finset.min'_mem ( ( Finset.Icc 0 p.length ).image ( fun k => ( p.getVert k ).1 + ( p.getVert k ).2.1 ) ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Nat.zero_le _ ⟩ ) ⟩ ; aesop;

/-- The first index achieving the minimum dc. -/
def firstMinDCIdx {v w : HexVertex} (p : hexGraph.Walk v w) : ℕ :=
  ((Finset.Icc 0 p.length).filter (fun k =>
    (p.getVert k).1 + (p.getVert k).2.1 = minDCVal p)).min'
    (by obtain ⟨k, hk, hdc⟩ := minDCVal_achieved p
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩, hdc⟩⟩)

lemma firstMinDCIdx_le_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    firstMinDCIdx p ≤ p.length := by
  exact Finset.mem_Icc.mp ( Finset.min'_mem _ _ |> fun h => Finset.mem_filter.mp h |>.1 ) |>.2

lemma firstMinDCIdx_dc {v w : HexVertex} (p : hexGraph.Walk v w) :
    (p.getVert (firstMinDCIdx p)).1 + (p.getVert (firstMinDCIdx p)).2.1 = minDCVal p := by
  exact Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun k => ( p.getVert k ).1 + ( p.getVert k ).2.1 = minDCVal p ) ( Finset.Icc 0 p.length ) ) _ ) |>.2

/-
minDCVal from paperStart is ≤ 0.
-/
lemma minDCVal_paperStart_le {w : HexVertex} (p : hexGraph.Walk paperStart w) :
    minDCVal p ≤ 0 := by
  convert minDCVal_le p 0 ( Nat.zero_le _ ) using 1 ; simp +decide [ paperStart ] ;

/-
The "width" -minDCVal is at most the walk length.
-/
lemma neg_minDCVal_le_length {w : HexVertex} (p : hexGraph.Walk paperStart w) :
    -minDCVal p ≤ p.length := by
  have h_bound : minDCVal p ≥ (p.getVert (firstMinDCIdx p)).1 + (p.getVert (firstMinDCIdx p)).2.1 := by
    exact firstMinDCIdx_dc p ▸ le_rfl;
  have := hexGraph_walk_sum_bound_neg ( p.take ( firstMinDCIdx p ) ) ; simp_all +decide [ SimpleGraph.Walk.take ] ;
  norm_num [ paperStart ] at this; linarith;

/-
In a walk from paperStart with minDCVal < 0,
    the first vertex achieving minimum dc is FALSE.
    Proof: if it were TRUE at dc = minDCVal, then the previous step was
    FALSE→TRUE. The FALSE vertex had dc ≤ dc(TRUE) = minDCVal (by dc_step_from_false
    going up). Since dc(FALSE) ≥ minDCVal, we get dc(FALSE) = minDCVal.
    But this FALSE vertex appears before the TRUE one, contradicting "first".
-/
lemma firstMinDC_is_false {w : HexVertex}
    (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (h_neg : minDCVal p < 0) :
    (p.getVert (firstMinDCIdx p)).2.2 = false := by
  by_contra h_contra;
  -- Since `firstMinDCIdx p > 0`, we can consider the vertex at index `firstMinDCIdx p - 1`.
  obtain ⟨k, hk⟩ : ∃ k, k < firstMinDCIdx p ∧ (p.getVert k).1 + (p.getVert k).2.1 = minDCVal p := by
    have h_prev_false : (p.getVert (firstMinDCIdx p - 1)).2.2 = false := by
      have h_prev_false : hexGraph.Adj (p.getVert (firstMinDCIdx p - 1)) (p.getVert (firstMinDCIdx p)) := by
        rcases k : firstMinDCIdx p with ( _ | k ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
        · have := firstMinDCIdx_dc p; simp_all +decide [ paperStart ] ;
        · convert p.adj_getVert_succ _;
          linarith [ firstMinDCIdx_le_length p ];
      have := hex_adj_flip_bool h_prev_false; aesop;
    have h_prev_false : (p.getVert (firstMinDCIdx p - 1)).1 + (p.getVert (firstMinDCIdx p - 1)).2.1 ≤ minDCVal p := by
      have h_prev_dc_le_min : (p.getVert (firstMinDCIdx p)).1 + (p.getVert (firstMinDCIdx p)).2.1 ≥ (p.getVert (firstMinDCIdx p - 1)).1 + (p.getVert (firstMinDCIdx p - 1)).2.1 := by
        apply dc_step_from_false;
        · convert p.adj_getVert_succ _;
          · grind;
          · exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ) ( firstMinDCIdx_le_length p );
        · assumption;
      exact h_prev_dc_le_min.trans ( firstMinDCIdx_dc p |> le_of_eq );
    exact ⟨ firstMinDCIdx p - 1, Nat.pred_lt ( ne_bot_of_gt ( show 0 < firstMinDCIdx p from Nat.pos_of_ne_zero fun h => by simp_all +decide [ minDCVal ] ) ), le_antisymm h_prev_false ( minDCVal_le _ _ ( Nat.sub_le_of_le_add <| by linarith [ firstMinDCIdx_le_length p ] ) ) ⟩;
  exact not_le_of_gt hk.1 ( Finset.min'_le _ _ <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.zero_le _, by linarith [ firstMinDCIdx_le_length p ] ⟩, hk.2 ⟩ )

end