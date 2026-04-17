/-
# Proof infrastructure for the cutting argument
-/

import Mathlib
import RequestProject.SAWCutting
import RequestProject.SAWCuttingHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walks staying in the narrower strip embed into A_inf(T) -/

def embed_in_strip {T : ℕ} (s : PaperSAW_A_inf (T + 1))
    (h : ∀ v ∈ s.walk.1.support, PaperInfStrip T v) : PaperSAW_A_inf T where
  end_v := s.end_v
  walk := s.walk
  end_left := s.end_left
  in_strip := h

lemma embed_in_strip_injective {T : ℕ}
    {s1 s2 : PaperSAW_A_inf (T + 1)}
    {h1 : ∀ v ∈ s1.walk.1.support, PaperInfStrip T v}
    {h2 : ∀ v ∈ s2.walk.1.support, PaperInfStrip T v}
    (heq : embed_in_strip s1 h1 = embed_in_strip s2 h2) :
    s1 = s2 := by
  cases s1; cases s2
  unfold embed_in_strip at heq
  simp at heq
  obtain ⟨h1, h2⟩ := heq
  subst h1; subst h2; rfl

/-
Summability of A_inf(T) from A_inf(T+1) via the widen injection.
-/
lemma A_inf_summable_of_succ {T : ℕ}
    (h : Summable (fun s : PaperSAW_A_inf (T + 1) => xc ^ (s.walk.1.length + 1))) :
    Summable (fun s : PaperSAW_A_inf T => xc ^ (s.walk.1.length + 1)) := by
  have h_inj : Function.Injective (fun s : PaperSAW_A_inf T => PaperSAW_A_inf_widen s) := by
    exact?;
  convert h.comp_injective h_inj using 1

/-
Partial sum over in-strip walks ≤ A_inf(T).
-/
lemma in_strip_sum_le {T : ℕ}
    (F : Finset (PaperSAW_A_inf (T + 1)))
    (hF : ∀ s ∈ F, ∀ v ∈ s.walk.1.support, PaperInfStrip T v)
    (h_summ : Summable (fun s : PaperSAW_A_inf T => xc ^ (s.walk.1.length + 1))) :
    ∑ s ∈ F, xc ^ (s.walk.1.length + 1) ≤
    ∑' (s : PaperSAW_A_inf T), xc ^ (s.walk.1.length + 1) := by
  -- Consider the function $g : F \to \text{PaperSAW\_A\_inf } T$ defined by $g(s) = \text{embed\_in\_strip } s (hF s hs)$.
  set g : F → PaperSAW_A_inf T := fun s => embed_in_strip s.val (hF s.val s.property);
  -- Since $g$ is injective, the image of $F$ under $g$ is a finite subset of $\text{PaperSAW\_A\_inf } T$.
  have h_image_finite : Set.Finite (Set.range g) := by
    exact Set.toFinite _;
  convert Summable.sum_le_tsum ( h_image_finite.toFinset ) ( fun _ _ => ?_ ) ( h_summ ) using 1;
  · refine' Finset.sum_bij ( fun s hs => g ⟨ s, hs ⟩ ) _ _ _ _ <;> simp +decide [ Finset.mem_image, Finset.mem_range ];
    · exact fun s₁ hs₁ s₂ hs₂ h => by simpa using embed_in_strip_injective h;
    · aesop;
  · exact pow_nonneg ( show 0 ≤ xc by exact le_of_lt ( xc_pos ) ) _

/-- Each extra walk decomposes into a pair of bridges with matching total length. -/
lemma extra_walk_decomp {T : ℕ} (hT : 1 ≤ T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    ∃ (b1 b2 : PaperBridge (T + 1)),
      s.walk.1.length = b1.walk.1.length + b2.walk.1.length := by
  have hT' : 0 < T := by omega
  obtain ⟨v, hv_mem, hv_diag, hv_false⟩ := A_inf_diff_reaches_boundary hT' s h_not
  obtain ⟨b1, hb1⟩ := prefix_gives_bridge s.walk.1 s.walk.2 v hv_mem hv_diag hv_false s.in_strip
  obtain ⟨b2, hb2⟩ := suffix_reversed_shifted_gives_bridge s.end_v v
    s.end_left.1 s.end_left.2.1 hv_diag hv_false
    (s.walk.1.dropUntil v hv_mem) (s.walk.2.dropUntil hv_mem)
    (fun u hu => s.in_strip u (s.walk.1.support_dropUntil_subset hv_mem hu))
  refine ⟨b1, b2, ?_⟩
  have := walk_split_lengths s.walk.1 hv_mem
  omega

/-- Sum over extra walks ≤ xc · B(T+1)². -/
lemma extra_walk_sum_le {T : ℕ} (hT : 1 ≤ T)
    (F : Finset (PaperSAW_A_inf (T + 1)))
    (hF : ∀ s ∈ F, ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    ∑ s ∈ F, xc ^ (s.walk.1.length + 1) ≤
    xc * paper_bridge_partition (T + 1) xc ^ 2 := by
  sorry

/-! ## Main cutting argument -/

theorem cutting_argument_proved (T : ℕ) (hT : 1 ≤ T) :
    A_inf (T + 1) xc - A_inf T xc ≤
    xc * paper_bridge_partition (T + 1) xc ^ 2 := by
  by_cases h_summ : Summable (fun s : PaperSAW_A_inf (T + 1) => xc ^ (s.walk.1.length + 1))
  · have h_summ_T := A_inf_summable_of_succ h_summ
    have h_bound : A_inf (T + 1) xc ≤
        A_inf T xc + xc * paper_bridge_partition (T + 1) xc ^ 2 := by
      unfold A_inf at *
      apply Real.tsum_le_of_sum_le (fun s => pow_nonneg xc_pos.le _)
      intro F
      classical
      set F_in := F.filter (fun s : PaperSAW_A_inf (T + 1) =>
        ∀ v ∈ s.walk.1.support, PaperInfStrip T v)
      set F_out := F.filter (fun s : PaperSAW_A_inf (T + 1) =>
        ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v)
      have hF_split : F = F_in ∪ F_out :=
        (Finset.filter_union_filter_neg_eq (p := fun s : PaperSAW_A_inf (T + 1) =>
          ∀ v ∈ s.walk.1.support, PaperInfStrip T v) F).symm
      have hF_disj : Disjoint F_in F_out :=
        Finset.disjoint_filter_filter_neg F _ _
      rw [hF_split, Finset.sum_union hF_disj]
      exact add_le_add
        (in_strip_sum_le F_in (fun s hs => (Finset.mem_filter.mp hs).2) h_summ_T)
        (extra_walk_sum_le hT F_out (fun s hs => (Finset.mem_filter.mp hs).2))
    linarith
  · have : A_inf (T + 1) xc = 0 := by simp [A_inf, tsum_eq_zero_of_not_summable h_summ]
    rw [this]
    linarith [A_inf_nonneg T xc xc_pos.le,
              mul_nonneg xc_pos.le (sq_nonneg (paper_bridge_partition (T + 1) xc))]

end