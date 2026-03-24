/-
# Finiteness of self-avoiding walks in finite strips

This file establishes that SAWs restricted to finite strip domains are finite,
which ensures the partition functions A_{T,L}, B_{T,L}, E_{T,L} are well-defined
finite sums. This is important infrastructure for the strip identity (Lemma 2).

## Reference

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. The finite strip FiniteStrip T L has finitely many vertices
2. SAWs in the finite strip have bounded length
3. The partition functions A_TL, B_TL, E_TL are finite sums
4. Summability of the partition function terms
-/

import RequestProject.SAWFiniteStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Finite strip has finitely many vertices -/

/-- The set of vertices in FiniteStrip T L is finite. -/
lemma finiteStrip_finite (T L : ℕ) : Set.Finite {v : HexVertex | FiniteStrip T L v} := by
  have : {v : HexVertex | FiniteStrip T L v} ⊆
    (Set.Icc (0 : ℤ) T) ×ˢ ((Set.Icc (-(L : ℤ) - T) (L + T)) ×ˢ (Set.univ : Set Bool)) := by
    intro ⟨x, y, b⟩ ⟨hx1, hx2, habs⟩
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true]
    refine ⟨⟨hx1, by exact_mod_cast hx2⟩, ?_, ?_⟩
    · have := (abs_le.mp habs).1; linarith
    · have := (abs_le.mp habs).2; linarith
  exact Set.Finite.subset (Set.Finite.prod
    (Set.finite_Icc _ _) (Set.Finite.prod (Set.finite_Icc _ _) Set.finite_univ)) this

/-! ## SAW length bound in finite strips

A SAW in FiniteStrip T L visits each vertex at most once.
Since FiniteStrip T L is finite, the length of any such SAW is bounded.
-/

/-- Any SAW in the finite strip has length bounded by the number of vertices. -/
lemma saw_length_bound_in_strip (T L : ℕ) {n : ℕ} (s : SAW hexOrigin n)
    (hin : ∀ v ∈ s.p.1.support, FiniteStrip T L v) :
    n < (finiteStrip_finite T L).toFinset.card + 1 := by
  have h_support := s.p.2.support_nodup
  have h_len : s.p.1.support.length = n + 1 := by
    rw [SimpleGraph.Walk.length_support]; exact congrArg (· + 1) s.l
  have h_sub : s.p.1.support.toFinset ⊆ (finiteStrip_finite T L).toFinset := by
    intro v hv
    rw [Set.Finite.mem_toFinset]
    exact hin v (List.mem_toFinset.mp hv)
  have h_nodup : s.p.1.support.toFinset.card = n + 1 := by
    rw [List.toFinset_card_of_nodup h_support, h_len]
  linarith [Finset.card_le_card h_sub]

/-! ## The partition functions are finite sums -/

/-
PROBLEM
The terms of B_TL are summable (each walk has bounded length).

PROVIDED SOLUTION
Show that StripSAW_B T L is a Finite type. The set of lengths is bounded above by the number of vertices in the strip (by saw_length_bound_in_strip). Then inject StripSAW_B T L into Σ n : Fin (M+1), {s : SAW hexOrigin n | ...conditions...}. Since SAW hexOrigin n is Fintype and the conditions are decidable, this sigma type is Finite. Then use the fact that any function on a Finite type is summable.

Follow the exact same proof structure as A_TL_summable (which was proved): use h_finite_lengths with M = (finiteStrip_finite T L).toFinset.card, inject into a finite sigma type, then use the fact that any function on a Finite type is summable.
-/
lemma B_TL_summable (T L : ℕ) (x : ℝ) :
    Summable (fun s : StripSAW_B T L => x ^ s.len) := by
  have h_finite : Finite (StripSAW_B T L) := by
    have h_finite_lengths : ∃ M : ℕ, ∀ s : StripSAW_B T L, s.len ≤ M := by
      exact ⟨ ( finiteStrip_finite T L ).toFinset.card, fun s => by have := saw_length_bound_in_strip T L s.saw s.in_strip; aesop ⟩
    generalize_proofs at *; (
    choose M hM using h_finite_lengths;
    have h_finite_union : Finite (Σ n : Fin (M + 1), {s : SAW hexOrigin n | (∀ v ∈ s.p.1.support, FiniteStrip T L v) ∧ s.w.1 = T}) := by
      exact Finite.instSigma
    exact h_finite_union.of_injective (fun s => ⟨ ⟨ s.len, Nat.lt_succ_of_le ( hM s ) ⟩, ⟨ s.saw, s.in_strip, s.end_right ⟩ ⟩) (fun s t h => by cases s; cases t; aesop;));
  haveI := Fintype.ofFinite ( StripSAW_B T L ) ; exact ⟨ _, hasSum_fintype _ ⟩ ;

/-
PROBLEM
The terms of A_TL are summable.

PROVIDED SOLUTION
Same as B_TL_summable: every StripSAW_A T L has len bounded by (finiteStrip_finite T L).toFinset.card (by saw_length_bound_in_strip). The type is finite. A function on a finite set is summable.
-/
lemma A_TL_summable (T L : ℕ) (x : ℝ) :
    Summable (fun s : StripSAW_A T L => x ^ s.len) := by
  -- The type is finite.
  have h_finite : Finite (StripSAW_A T L) := by
    -- The set of lengths is finite since it is bounded above by the number of vertices in the finite strip.
    have h_finite_lengths : ∃ M : ℕ, ∀ s : StripSAW_A T L, s.len ≤ M := by
      exact ⟨ ( finiteStrip_finite T L ).toFinset.card, fun s => by
        have := saw_length_bound_in_strip T L s.saw s.in_strip; aesop; ⟩;
    choose M hM using h_finite_lengths;
    have h_finite_union : Finite (Σ n : Fin (M + 1), {s : SAW hexOrigin n | (∀ v ∈ s.p.1.support, FiniteStrip T L v) ∧ s.w.1 = 0 ∧ s.w ≠ hexOrigin}) := by
      exact Finite.instSigma;
    refine' h_finite_union.of_injective _ _;
    exact fun s => ⟨ ⟨ s.len, Nat.lt_succ_of_le ( hM s ) ⟩, ⟨ s.saw, s.in_strip, s.end_left ⟩ ⟩
    generalize_proofs at *;
    intro s t h; cases s; cases t; aesop;
  -- Since the type is finite, any function on it is summable.
  have h_summable : ∀ (f : StripSAW_A T L → ℝ), Summable f := by
    exact fun f => Summable.of_finite;
  exact h_summable _

/-
PROBLEM
The terms of E_TL are summable.

PROVIDED SOLUTION
Same approach as A_TL_summable. Show StripSAW_E T L is Finite by bounding len and injecting into a finite sigma type. Then any function on a Finite type is summable.
-/
lemma E_TL_summable (T L : ℕ) (x : ℝ) :
    Summable (fun s : StripSAW_E T L => x ^ s.len) := by
  have h_finite : Finite (StripSAW_E T L) := by
    have h_finite : ∀ n : ℕ, Set.Finite {s : SAW hexOrigin n | ∀ v ∈ s.p.1.support, FiniteStrip T L v} := by
      intro n
      have h_finite : Set.Finite {v : HexVertex | FiniteStrip T L v} := by
        exact finiteStrip_finite T L |> Set.Finite.subset <| by aesop_cat;
      generalize_proofs at *; (
      exact Set.toFinite _);
    have h_finite : Set.Finite {s : Σ n, SAW hexOrigin n | ∀ v ∈ s.2.p.1.support, FiniteStrip T L v} := by
      have h_finite : ∀ n : ℕ, Set.Finite {s : Σ n, SAW hexOrigin n | s.1 = n ∧ ∀ v ∈ s.2.p.1.support, FiniteStrip T L v} := by
        intro n; specialize h_finite n; exact Set.Finite.subset ( h_finite.image fun s => ⟨ n, s ⟩ ) fun s hs => by aesop;
      generalize_proofs at *; (
      refine' Set.Finite.subset ( Set.Finite.biUnion ( Set.finite_Ico 0 ( ( finiteStrip_finite T L ).toFinset.card + 1 ) ) fun n hn => h_finite n ) _;
      intro s hs; exact Set.mem_iUnion₂.mpr ⟨ s.fst, ⟨ Nat.zero_le _, Nat.lt_succ_of_le ( Nat.le_of_lt_succ <| by
        have := saw_length_bound_in_strip T L s.2 hs; aesop; ) ⟩, rfl, hs ⟩ ;)
    generalize_proofs at *; (
    have h_inj : Function.Injective (fun s : StripSAW_E T L => ⟨s.len, s.saw⟩ : StripSAW_E T L → Σ n, SAW hexOrigin n) := by
      intro s t h_eq; cases s; cases t; aesop;
    generalize_proofs at *; (
    have h_finite : Set.Finite {s : StripSAW_E T L | ∀ v ∈ s.saw.p.1.support, FiniteStrip T L v} := by
      exact Set.Finite.subset ( h_finite.preimage fun s => by tauto ) fun s hs => hs |> fun hs' => by tauto;
    generalize_proofs at *; (
    convert h_finite using 1
    generalize_proofs at *; (
    exact iff_of_true ( by exact Set.finite_univ_iff.mp ( Set.Finite.subset ( h_finite ) fun s _ => by exact s.in_strip ) ) h_finite;))))
  generalize_proofs at *; (
  exact summable_of_finite_support ( Set.toFinite _ ) |> fun h => h.congr ( by aesop ) ;)

/-! ## Partition function monotonicity -/

/-
PROBLEM
A_TL is monotone in L: enlarging the strip gives more walks.

PROVIDED SOLUTION
A_TL T L1 x ≤ A_TL T L2 x when L1 ≤ L2. Every StripSAW_A T L1 can be turned into a StripSAW_A T L2 by noting that FiniteStrip T L1 ⊆ FiniteStrip T L2 (from finite_strip_monotone). The tsum over a larger type is ≥ the tsum over a smaller type (when terms are non-negative). Use tsum comparison: inject StripSAW_A T L1 into StripSAW_A T L2 and compare the sums.
-/
lemma A_TL_mono (T : ℕ) (x : ℝ) (hx : 0 ≤ x) : Monotone (fun L => A_TL T L x) := by
  intro L₁ L₂ hL₁₂;
  have h_sum_le : ∑' (s : StripSAW_A T L₁), x ^ s.len ≤ ∑' (s : StripSAW_A T L₂), x ^ s.len := by
    have h_inj : Function.Injective (fun s : StripSAW_A T L₁ => ⟨s.len, s.saw, s.end_left, fun v hv => finite_strip_monotone hL₁₂ v (s.in_strip v hv)⟩ : StripSAW_A T L₁ → StripSAW_A T L₂) := by
      intro s₁ s₂ h; cases s₁; cases s₂; aesop;
    have h_sum_le : ∑' (s : StripSAW_A T L₁), x ^ s.len ≤ ∑' (s : Set.range (fun s : StripSAW_A T L₁ => ⟨s.len, s.saw, s.end_left, fun v hv => finite_strip_monotone hL₁₂ v (s.in_strip v hv)⟩ : StripSAW_A T L₁ → StripSAW_A T L₂)), x ^ s.val.len := by
      rw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ h_inj ) ] ; aesop;
    refine le_trans h_sum_le ?_;
    have h_sum_le : ∀ {f : StripSAW_A T L₂ → ℝ}, (∀ s, 0 ≤ f s) → Summable f → ∑' (s : Set.range (fun s : StripSAW_A T L₁ => ⟨s.len, s.saw, s.end_left, fun v hv => finite_strip_monotone hL₁₂ v (s.in_strip v hv)⟩ : StripSAW_A T L₁ → StripSAW_A T L₂)), f s.val ≤ ∑' (s : StripSAW_A T L₂), f s := by
      intros f hf_nonneg hf_summable;
      rw [ tsum_subtype ];
      apply_rules [ Summable.tsum_le_tsum ];
      · intro s; by_cases hs : s ∈ Set.range ( fun s : StripSAW_A T L₁ => ⟨ s.len, s.saw, s.end_left, fun v hv => finite_strip_monotone hL₁₂ v ( s.in_strip v hv ) ⟩ : StripSAW_A T L₁ → StripSAW_A T L₂ ) <;> simp +decide [ hs, hf_nonneg ] ;
      · exact hf_summable.indicator _;
    exact h_sum_le ( fun _ => pow_nonneg hx _ ) ( A_TL_summable T L₂ x );
  exact h_sum_le

/-
PROBLEM
B_TL is monotone in L: enlarging the strip gives more walks.

PROVIDED SOLUTION
Same approach as A_TL_mono. Every StripSAW_B T L1 embeds into StripSAW_B T L2 when L1 ≤ L2 via finite_strip_monotone. Compare the tsums using the injection and non-negativity of terms.
-/
lemma B_TL_mono (T : ℕ) (x : ℝ) (hx : 0 ≤ x) : Monotone (fun L => B_TL T L x) := by
  intros L1 L2 hL;
  unfold B_TL;
  by_cases h : Summable ( fun s : StripSAW_B T L1 => x ^ s.len ) <;> by_cases h' : Summable ( fun s : StripSAW_B T L2 => x ^ s.len ) <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
  · have h_inj : Function.Injective (fun s : StripSAW_B T L1 => ⟨s.len, s.saw, s.end_right, fun v hv => finite_strip_monotone hL v (s.in_strip v hv)⟩ : StripSAW_B T L1 → StripSAW_B T L2) := by
      intro s t h_eq; cases s; cases t; aesop;
    have h_sum_le : ∑' s : StripSAW_B T L1, x ^ s.len ≤ ∑' s : StripSAW_B T L2, x ^ s.len := by
      have h_sum_le : ∑' s : StripSAW_B T L1, x ^ s.len = ∑' s : Set.range (fun s : StripSAW_B T L1 => ⟨s.len, s.saw, s.end_right, fun v hv => finite_strip_monotone hL v (s.in_strip v hv)⟩ : StripSAW_B T L1 → StripSAW_B T L2), x ^ s.val.len := by
        rw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ h_inj ) ] ; aesop
      convert Summable.tsum_subtype_le _ _ using 1;
      rotate_left;
      exact StripSAW_B T L2;
      exact ℝ;
      all_goals try infer_instance;
      use fun s => x ^ s.len;
      exact Set.range ( fun s : StripSAW_B T L1 => ⟨ s.len, s.saw, s.end_right, fun v hv => finite_strip_monotone hL v ( s.in_strip v hv ) ⟩ : StripSAW_B T L1 → StripSAW_B T L2 );
      aesop;
    exact h_sum_le;
  · exact False.elim <| h' <| B_TL_summable T L2 x;
  · exact tsum_nonneg fun _ => pow_nonneg hx _

end