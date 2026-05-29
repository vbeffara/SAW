/-
# Fiber counting proof for extra_at_k_le_prod_lt
-/

import Mathlib
import RequestProject.SAWHWStepHelpers
import RequestProject.SAWHWConvBoundBase

open Real Complex ComplexConjugate Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 8000000

def extraPrefix (W n k : ℕ) (s : SAW paperStart n) (hk_le : k ≤ n) : SAW paperStart k :=
  ⟨s.p.1.getVert k,
   ⟨s.p.1.take k, walk_take_isPath s.p.1 s.p.2 k⟩,
   by rw [SimpleGraph.Walk.take_length]; simp [s.l, min_eq_left hk_le]⟩

lemma extraPrefix_in_bridge (W n k : ℕ) (s : SAW paperStart n)
    (hs_strip : ∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_exists : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ))
    (hk_eq : lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists = k) (hk_le : k ≤ n) :
    let b := extraPrefix W n k s hk_le
    b.w.1 + b.w.2.1 = -(↑(W + 1) : ℤ) ∧
    ∀ v ∈ b.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 := by
  unfold extraPrefix
  refine' ⟨ _, fun v hv => _ ⟩
  · grind +suggestions
  · exact hs_strip v (by convert List.mem_append_left _ hv using 1; convert walk_support_take_drop s.p.1 k (by linarith [s.l]) using 1)

lemma extraVertex_false (W n k : ℕ) (s : SAW paperStart n)
    (hs_strip : ∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_exists : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ))
    (hk_eq : lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists = k) (hk_lt : k < n) :
    (s.p.1.getVert k).2.2 = false ∧ (s.p.1.getVert k).1 + (s.p.1.getVert k).2.1 = -(↑(W + 1) : ℤ) := by
  convert lastDCIndex_is_false' s.p.1 s.p.2 W hs_strip h_exists ?_
  · rw [← hk_eq, lastDCIndex_dc]; norm_num
  · linarith [s.l]

lemma support_eq_implies_endpoint_eq {v : HexVertex} {k : ℕ}
    (b₁ b₂ : SAW v k) (h : b₁.p.1.support = b₂.p.1.support) : b₁.w = b₂.w := by
  have h_support_last : ∀ (v w : HexVertex) (p : hexGraph.Walk v w), (p.support.getLast? = some w) := by
    intros v w p; induction p <;> simp +decide [*]; grind
  grind

lemma take_support_eq_endpoint (n k : ℕ) (s : SAW paperStart n) (b : SAW paperStart k)
    (hk_le : k ≤ n) (h_eq : (s.p.1.take k).support = b.p.1.support) :
    s.p.1.getVert k = b.w := by
  convert support_eq_implies_endpoint_eq _ _ _
  rotate_left
  exact ⟨s.p.1.getVert k, ⟨s.p.1.take k, walk_take_isPath s.p.1 s.p.2 k⟩,
    by rw [SimpleGraph.Walk.take_length]; simp [s.l, min_eq_left hk_le]⟩
  · exact h_eq
  · rfl

def relaxed_suffix_count (W : ℕ) (v : HexVertex) (s : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun t : SAW v s =>
    ∀ j ∈ Finset.Icc 1 s,
      (-(↑W : ℤ) ≤ (t.p.1.getVert j).1 + (t.p.1.getVert j).2.1 ∧
      (t.p.1.getVert j).1 + (t.p.1.getVert j).2.1 ≤ 0)))

lemma relaxed_suffix_le_narrow (W : ℕ) (v : HexVertex)
    (hv_false : v.2.2 = false) (hv_dc : v.1 + v.2.1 = -(↑(W + 1) : ℤ)) (s : ℕ) :
    relaxed_suffix_count W v s ≤ narrow_suffix_count W s := by
  convert suffix_saw_count_le W s v hv_false hv_dc using 1
  exact congr_arg Finset.card (Finset.ext fun t => by aesop)

lemma extra_drop_relaxed (W n k : ℕ) (s : SAW paperStart n)
    (hs_strip : ∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_exists : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ))
    (hk_eq : lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists = k) (hk_lt : k < n)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (n - k)) :
    (-(↑W : ℤ) ≤ ((s.p.1.drop k).getVert j).1 + ((s.p.1.drop k).getVert j).2.1 ∧
    ((s.p.1.drop k).getVert j).1 + ((s.p.1.drop k).getVert j).2.1 ≤ 0) := by
  convert suffix_drop_narrow W n k s hs_strip h_exists hk_eq hk_lt j _ _ using 1 <;> aesop

def dropToSuffix (n k : ℕ) (b : SAW paperStart k) (s : SAW paperStart n) (hk_le : k ≤ n)
    (h_take_eq : (s.p.1.take k).support = b.p.1.support) : SAW b.w (n - k) :=
  ⟨s.w,
   ⟨(s.p.1.drop k).copy (take_support_eq_endpoint n k s b hk_le h_take_eq) rfl,
    walk_copy_isPath _ _ rfl (walk_drop_isPath s.p.1 s.p.2 k)⟩,
   by simp [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length, s.l]⟩

lemma dropToSuffix_injective (n k : ℕ) (b : SAW paperStart k) (s₁ s₂ : SAW paperStart n)
    (hk_le : k ≤ n) (h1 : (s₁.p.1.take k).support = b.p.1.support)
    (h2 : (s₂.p.1.take k).support = b.p.1.support)
    (h_eq : dropToSuffix n k b s₁ hk_le h1 = dropToSuffix n k b s₂ hk_le h2) : s₁ = s₂ := by
  contrapose! h_eq; simp_all +decide [Finset.ext_iff]
  have h_support : (s₁.p.1.drop k).support = (s₂.p.1.drop k).support → False := by
    intro h; exact h_eq (suffix_fiber_injective n k s₁ s₂ (by simp [s₁.l, hk_le]) (by simp [s₂.l, hk_le]) (by aesop) (by aesop))
  intro h; have := congr_arg (fun x => x.p.1.support) h; simp_all +decide [SimpleGraph.Walk.support_copy]
  exact h_support (by simpa [dropToSuffix] using this)

lemma dropToSuffix_relaxed (W n k : ℕ) (b : SAW paperStart k) (s : SAW paperStart n)
    (hs_strip : ∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0)
    (h_exists : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ))
    (hk_eq : lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h_exists = k) (hk_lt : k < n)
    (hk_le : k ≤ n) (h_take_eq : (s.p.1.take k).support = b.p.1.support) :
    ∀ j ∈ Finset.Icc 1 (n - k),
      (-(↑W : ℤ) ≤ ((dropToSuffix n k b s hk_le h_take_eq).p.1.getVert j).1 +
        ((dropToSuffix n k b s hk_le h_take_eq).p.1.getVert j).2.1 ∧
      ((dropToSuffix n k b s hk_le h_take_eq).p.1.getVert j).1 +
        ((dropToSuffix n k b s hk_le h_take_eq).p.1.getVert j).2.1 ≤ 0) := by
  convert extra_drop_relaxed W n k s hs_strip h_exists hk_eq hk_lt using 1
  unfold dropToSuffix; aesop

/-! ## Fiber bound -/

lemma fiber_bound (W n k : ℕ) (hk_lt : k < n)
    (b : SAW paperStart k) (hb_false : b.w.2.2 = false)
    (hb_dc : b.w.1 + b.w.2.1 = -(↑(W + 1) : ℤ)) :
    Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
      (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
      (∃ h : ∃ j, j ≤ s.p.1.length ∧ (s.p.1.getVert j).1 + (s.p.1.getVert j).2.1 = -(↑(W + 1) : ℤ),
        lastDCIndex s.p.1 (-(↑(W + 1) : ℤ)) h = k) ∧
      (s.p.1.take k).support = b.p.1.support)) ≤
    narrow_suffix_count W (n - k) := by
  by_contra h_contra;
  convert Set.nonempty_of_encard_ne_zero _;
  rotate_left;
  exact Fin 0;
  exact { };
  · exact absurd h_contra ( by
      by_cases h : ∃ s : SAW paperStart n, ( ∀ v ∈ s.p.1.support, - ( W + 1 : ℤ ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 ) ∧ ( ∃ h : ∃ j ≤ s.p.1.length, ( s.p.1.getVert j ).1 + ( s.p.1.getVert j ).2.1 = - ( W + 1 : ℤ ), lastDCIndex s.p.1 ( - ( W + 1 : ℤ ) ) h = k ) ∧ ( s.p.1.take k ).support = b.p.1.support;
      · obtain ⟨s₀, hs₀⟩ := h;
        refine' not_not.mpr ( le_trans _ ( relaxed_suffix_le_narrow W b.w hb_false hb_dc _ ) );
        refine' Finset.card_le_card_of_injOn _ _ _;
        use fun s => if h : ( s.p.1.take k ).support = b.p.1.support then dropToSuffix n k b s ( by linarith ) h else dropToSuffix n k b s₀ ( by linarith ) hs₀.2.2;
        · intro s hs; simp_all +decide [ Set.MapsTo ] ;
          convert dropToSuffix_relaxed W n k b s _ _ _ _ _ using 1;
          all_goals norm_num [ hs.2.2 ];
          all_goals try linarith;
          exact hs.1;
          exact hs.2.1.choose;
          exact hs.2.1.choose_spec;
        · intro s hs t ht h_eq;
          simp +zetaDelta at *;
          split_ifs at h_eq ; simp_all +decide [ dropToSuffix_injective ];
          · exact dropToSuffix_injective n k b s t ( by linarith ) ( by tauto ) ( by tauto ) h_eq;
          · tauto;
          · tauto;
          · tauto;
      · simp +zetaDelta at *;
        rw [ Finset.card_eq_zero.mpr ];
        · exact Nat.zero_le _;
        · grind );
  · simp +decide [ Set.Nonempty ]

end