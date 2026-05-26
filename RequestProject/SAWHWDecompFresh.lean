/-
# The neg_dc injection proof

Proves saw_neg_dc_le_conv_nat using the decomposition infrastructure.
Strategy: partition by k = firstMinDCIdx, bound each part.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWHWStructural
import RequestProject.SAWHWMinDC
import RequestProject.SAWHWHalfPlane
import RequestProject.SAWHWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Type abbreviations -/

abbrev HPWalkSet (N k : ℕ) :=
  { s : SAW paperStart k //
    ∀ v ∈ s.p.1.support, -(N : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 }

/-- NEG DC SAWs with a fixed splitting index k. -/
def NegDCAtK (n k : ℕ) : Finset (SAW paperStart n) :=
  Finset.univ.filter (fun s : SAW paperStart n =>
    (∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0) ∧ firstMinDCIdx s.p.1 = k)

/-! ## Helper lemmas -/

private lemma minDCVal_neg' {n : ℕ} (s : SAW paperStart n)
    (h : ∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0) :
    minDCVal s.p.1 < 0 := by
  obtain ⟨v, hv, hvdc⟩ := h
  obtain ⟨k, hkv, hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  exact lt_of_le_of_lt (minDCVal_le s.p.1 k hk) (hkv ▸ hvdc)

/-! ## The injection for fixed k -/

/-- For a SAW s with firstMinDCIdx = k, construct the pair
    (prefix_transform, suffix_transform) in HPWalkSet(N,k) × HPWalkSet(N,n-k). -/
def negDCAtK_inject (N n k : ℕ) (hn : n ≤ N) (hk : k ≤ n)
    (s : SAW paperStart n)
    (hs_neg : ∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0)
    (hs_k : firstMinDCIdx s.p.1 = k) :
    HPWalkSet N k × HPWalkSet N (n - k) := by
  have hneg := minDCVal_neg' s hs_neg
  have hf : (s.p.1.getVert k).2.2 = false := hs_k ▸ firstMinDC_is_false s.p.1 s.p.2 hneg
  have hi : k ≤ s.p.1.length := by
    have := firstMinDCIdx_le_length s.p.1; rw [hs_k] at this; exact this
  have hmin : ∀ j, j ≤ s.p.1.length →
      (s.p.1.getVert k).1 + (s.p.1.getVert k).2.1 ≤
      (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 := by
    intro j hj; rw [← hs_k, firstMinDCIdx_dc]; exact minDCVal_le s.p.1 j hj
  have hlen_suff : (suffixTransform s.p.1 k hi hf).length = n - k := by
    rw [suffixTransform_length, s.l]
  exact (
    ⟨⟨_, ⟨prefixTransform s.p.1 k hi hf,
          prefixTransform_isPath s.p.1 s.p.2 k hi hf⟩,
     prefixTransform_length s.p.1 k hi hf⟩,
     prefixTransform_strip s.p.1 s.p.2 k hi hf hmin N (le_trans hk hn)⟩,
    ⟨⟨_, ⟨suffixTransform s.p.1 k hi hf,
          suffixTransform_isPath s.p.1 s.p.2 k hi hf⟩,
     hlen_suff⟩,
     suffixTransform_strip s.p.1 s.p.2 k hi hf hmin N (by rw [s.l]; exact Nat.sub_le_of_le_add (by linarith))⟩)

/-
The injection for fixed k is injective.
-/
lemma negDCAtK_inject_injective (N n k : ℕ) (hn : n ≤ N) (hk : k ≤ n)
    (s₁ s₂ : SAW paperStart n)
    (hs₁_neg : ∃ v ∈ s₁.p.1.support, v.1 + v.2.1 < 0)
    (hs₂_neg : ∃ v ∈ s₂.p.1.support, v.1 + v.2.1 < 0)
    (hs₁_k : firstMinDCIdx s₁.p.1 = k)
    (hs₂_k : firstMinDCIdx s₂.p.1 = k)
    (h_eq : negDCAtK_inject N n k hn hk s₁ hs₁_neg hs₁_k =
            negDCAtK_inject N n k hn hk s₂ hs₂_neg hs₂_k) :
    s₁ = s₂ := by
  have h_support : (s₁.p.1.take k).support = (s₂.p.1.take k).support ∧ (s₁.p.1.drop k).support = (s₂.p.1.drop k).support := by
    unfold negDCAtK_inject at h_eq;
    simp +zetaDelta at *;
    have h_support : (prefixTransform s₁.p.1 k (by
    exact hs₁_k ▸ firstMinDCIdx_le_length _ |> le_trans <| by simp +decide [ s₁.l ] ;) (by
    grind +qlia)).support = (prefixTransform s₂.p.1 k (by
    exact hs₂_k ▸ firstMinDCIdx_le_length _) (by
    grind)).support ∧ (suffixTransform s₁.p.1 k (by
    exact hs₁_k ▸ firstMinDCIdx_le_length _ |> le_trans <| by simp +decide [ s₁.l ] ;) (by
    grind +qlia)).support = (suffixTransform s₂.p.1 k (by
    exact hs₂_k ▸ firstMinDCIdx_le_length _) (by
    grind)).support := by
      grind
    generalize_proofs at *;
    simp_all +decide [ prefixTransform_support, suffixTransform_support ];
    simp_all +decide [ hexFlip, hexTranslate ];
    exact ⟨ List.map_injective_iff.mpr ( by intros a b; aesop ) h_support.1, List.map_injective_iff.mpr ( by intros a b; aesop ) h_support.2 ⟩;
  have h_support_eq : s₁.p.1.support = s₂.p.1.support := by
    have h_support_eq : (s₁.p.1.take k).support ++ (s₁.p.1.drop k).support.tail = s₁.p.1.support ∧ (s₂.p.1.take k).support ++ (s₂.p.1.drop k).support.tail = s₂.p.1.support := by
      have h_support_eq : ∀ {v w : HexVertex} {p : hexGraph.Walk v w} {k : ℕ}, k ≤ p.length → (p.take k).support ++ (p.drop k).support.tail = p.support := by
        intros v w p k hk; induction' p with v w p ih generalizing k; aesop;
        rcases k with ( _ | k ) <;> simp_all +decide [ SimpleGraph.Walk.take, SimpleGraph.Walk.drop ];
      exact ⟨ h_support_eq ( by linarith [ s₁.l ] ), h_support_eq ( by linarith [ s₂.l ] ) ⟩;
    grind;
  cases s₁ ; cases s₂;
  congr! 1;
  · rename_i w₁ p₁ l₁ w₂ p₂ l₂;
    have h_support_eq : ∀ {v w : HexVertex} {p : hexGraph.Walk v w}, p.IsPath → p.support.getLast? = some w := by
      intros v w p hp; induction p <;> simp_all +decide [ SimpleGraph.Walk.support ] ;
      grind;
    grind;
  · have h_walk_eq : ∀ {v w : HexVertex} {p q : hexGraph.Walk v w}, p.IsPath → q.IsPath → p.length = q.length → p.support = q.support → p = q := by
      exact?;
    grind

/-! ## Partition of saw_count_neg_dc -/

lemma saw_neg_dc_partition (n : ℕ) :
    Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
      ∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0)) =
    ∑ k ∈ Finset.range (n + 1), (NegDCAtK n k).card := by
  rw [ ← Finset.card_biUnion ];
  · congr with s ; simp +decide [ NegDCAtK ];
    exact fun x y h₁ h₂ => le_trans ( firstMinDCIdx_le_length _ ) ( by simp +decide [ s.l ] );
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hzx hzy => hxy <| by unfold NegDCAtK at *; aesop;

lemma neg_dc_at_k_bound (N n k : ℕ) (hn : n ≤ N) (hk : k ≤ n) :
    (NegDCAtK n k).card ≤ hp_walk_count N k * hp_walk_count N (n - k) := by
  convert Set.card_le_card ?_ using 1;
  rotate_left;
  rotate_left;
  exact ( HPWalkSet N k ) × ( HPWalkSet N ( n - k ) );
  exact Set.image ( fun s : NegDCAtK n k => negDCAtK_inject N n k hn hk s.1 ( by
    exact s.2 |> Finset.mem_filter.mp |>.2.1 ) ( by
    grind +locals ) ) ( Set.univ : Set ( NegDCAtK n k ) )
  all_goals generalize_proofs at *;
  exact Set.univ;
  exact Set.Finite.fintype ( Set.toFinite _ );
  exact?;
  · exact Set.image_subset_iff.mpr fun s _ => Set.mem_univ _;
  · rw [ Set.card_image_of_injective ];
    · rw [ Fintype.card_congr ( Equiv.Set.univ _ ) ] ; aesop;
    · intro s t h_eq_eq;
      exact Subtype.ext <| negDCAtK_inject_injective N n k hn hk _ _ _ _ _ _ h_eq_eq;
  · unfold hp_walk_count; simp +decide [ Fintype.card_subtype ] ;

/-- The main bound. -/
theorem saw_neg_dc_le_conv_nat (N n : ℕ) (hn : n ≤ N) :
    Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
      ∃ v ∈ s.p.1.support, v.1 + v.2.1 < 0)) ≤
    ∑ k ∈ Finset.range (n + 1), hp_walk_count N k * hp_walk_count N (n - k) := by
  rw [saw_neg_dc_partition]
  exact Finset.sum_le_sum fun k hk =>
    neg_dc_at_k_bound N n k hn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

end