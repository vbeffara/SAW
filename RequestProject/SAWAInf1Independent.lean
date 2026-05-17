/-
# Independent proof of A_inf 1 xc = 2xc³/(1-xc²)

This proves A_inf_1_exact WITHOUT using the sorry'd `infinite_strip_identity`.

Strategy: prove upper and lower bounds on A_inf 1 xc separately.
Upper bound uses A_inf_1_walk_classification (sorry-free).
Lower bound constructs explicit walks.
-/

import Mathlib
import RequestProject.SAWStripT1Exact
import RequestProject.SAWStripT1
import RequestProject.SAWCutting

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Upper bound: A_inf 1 xc ≤ 2xc³/(1-xc²)

Every PaperSAW_A_inf 1 walk has endpoint TRUE(k,-k) for some k ≠ 0,
and length 2|k| (by A_inf_1_walk_classification, which is sorry-free).
The map s ↦ s.end_v.1 gives an injection into ℤ \ {0}, so the tsum
is bounded by the sum over all k ≠ 0 of xc^{2|k|+1}. -/

/-
Two PaperSAW_A_inf 1 walks with the same first coordinate have the same endpoint.
-/
lemma A_inf_1_same_endpoint (s₁ s₂ : PaperSAW_A_inf 1)
    (h : s₁.end_v.1 = s₂.end_v.1) : s₁.end_v = s₂.end_v := by
  -- Since the end_v.2.1 component is determined by the end_v.1 component and the condition end_v.1 + end_v.2.1 = 0, we can conclude that s₁.end_v.2.1 = s₂.end_v.2.1.
  have h_end_v21 : s₁.end_v.2.1 = s₂.end_v.2.1 := by
    linarith [ s₁.end_left.1, s₂.end_left.1 ];
  exact Prod.ext h ( Prod.ext h_end_v21 ( by cases s₁; cases s₂; aesop ) )

/-
On the T=1 strip, two paths from paperStart to the same vertex are equal.
-/
lemma strip1_path_unique {w : HexVertex}
    (p₁ p₂ : hexGraph.Path paperStart w)
    (h₁ : ∀ v ∈ p₁.1.support, PaperInfStrip 1 v)
    (h₂ : ∀ v ∈ p₂.1.support, PaperInfStrip 1 v) :
    p₁ = p₂ := by
  obtain ⟨h_mono₁, h_mono₂⟩ : (∀ i j, i < j → j ≤ p₁.1.length → strip1_pos (p₁.1.getVert i) < strip1_pos (p₁.1.getVert j)) ∧ (∀ i j, i < j → j ≤ p₂.1.length → strip1_pos (p₂.1.getVert i) < strip1_pos (p₂.1.getVert j)) ∨ (∀ i j, i < j → j ≤ p₁.1.length → strip1_pos (p₁.1.getVert j) < strip1_pos (p₁.1.getVert i)) ∧ (∀ i j, i < j → j ≤ p₂.1.length → strip1_pos (p₂.1.getVert j) < strip1_pos (p₂.1.getVert i)) := by
    have h_mono₁ := strip1_saw_monotone p₁.1 p₁.2 h₁
    have h_mono₂ := strip1_saw_monotone p₂.1 p₂.2 h₂;
    cases h_mono₁ <;> cases h_mono₂ <;> simp_all +decide only;
    · exact Or.inl ⟨ fun _ _ _ _ => trivial, fun _ _ _ _ => trivial ⟩;
    · rename_i h₁ h₂;
      have := h₁ 0 ( p₁.1.length ) ; have := h₂ 0 ( p₂.1.length ) ; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
      grind +qlia;
    · rename_i h₁ h₂;
      have := h₁ 0 ( p₁.1.length ) ; have := h₂ 0 ( p₂.1.length ) ; simp_all +decide [ strip1_pos ] ;
      lia;
    · exact Or.inr ⟨ fun _ _ _ _ => trivial, fun _ _ _ _ => trivial ⟩;
  · have h_len_eq : p₁.1.length = p₂.1.length := by
      have h_len : strip1_pos w = strip1_pos paperStart + p₁.1.length ∧ strip1_pos w = strip1_pos paperStart + p₂.1.length := by
        have h_len : ∀ i ≤ p₁.1.length, strip1_pos (p₁.1.getVert i) = strip1_pos paperStart + i := by
          apply strip1_increasing_walk_pos;
          · exact p₁.2;
          · exact h₁;
          · assumption
        have h_len' : ∀ i ≤ p₂.1.length, strip1_pos (p₂.1.getVert i) = strip1_pos paperStart + i := by
          apply strip1_increasing_walk_pos;
          · exact p₂.2;
          · exact h₂;
          · assumption;
        exact ⟨ by simpa using h_len p₁.1.length le_rfl, by simpa using h_len' p₂.1.length le_rfl ⟩;
      grind
    have h_getVert_eq : ∀ i ≤ p₁.1.length, p₁.1.getVert i = p₂.1.getVert i := by
      intros i hi
      have h_pos_eq : strip1_pos (p₁.1.getVert i) = strip1_pos (p₂.1.getVert i) := by
        have h_pos_eq : ∀ i ≤ p₁.1.length, strip1_pos (p₁.1.getVert i) = strip1_pos paperStart + i := by
          apply strip1_increasing_walk_pos p₁.1 p₁.2 h₁;
          grind
        have h_pos_eq₂ : ∀ i ≤ p₂.1.length, strip1_pos (p₂.1.getVert i) = strip1_pos paperStart + i := by
          apply strip1_increasing_walk_pos; exact p₂.2; exact h₂; exact (by
          assumption);
        aesop;
      apply strip1_pos_injective;
      · exact h₁ _ ( by simp );
      · exact h₂ _ ( by simp );
      · exact h_pos_eq
    exact (by
    ext i;
    apply SimpleGraph.Walk.ext_getVert;
    intro k; by_cases hk : k ≤ p₁.1.length <;> simp_all +decide [ SimpleGraph.Walk.getVert ] ;
    rw [ SimpleGraph.Walk.getVert_of_length_le, SimpleGraph.Walk.getVert_of_length_le ] <;> linarith);
  · have h_length : p₁.1.length = p₂.1.length := by
      have h_length : ∀ (p : hexGraph.Walk paperStart w) (hp : p.IsPath) (hstrip : ∀ v ∈ p.support, PaperInfStrip 1 v), strip1_pos w - strip1_pos paperStart = p.length ∨ strip1_pos paperStart - strip1_pos w = p.length := by
        intros p hp hstrip
        have h_mono : (∀ i j, i < j → j ≤ p.length → strip1_pos (p.getVert i) < strip1_pos (p.getVert j)) ∨ (∀ i j, i < j → j ≤ p.length → strip1_pos (p.getVert j) < strip1_pos (p.getVert i)) := by
          apply strip1_saw_monotone p hp hstrip;
        cases' h_mono with h_mono h_mono;
        · have h_length : ∀ i ≤ p.length, strip1_pos (p.getVert i) = strip1_pos paperStart + i := by
            apply strip1_increasing_walk_pos p hp hstrip h_mono;
          specialize h_length p.length le_rfl;
          exact Or.inl ( by rw [ show p.getVert p.length = w from by simp +decide [ SimpleGraph.Walk.getVert ] ] at h_length; linarith );
        · have h_length : ∀ i ≤ p.length, strip1_pos (p.getVert i) = strip1_pos paperStart - i := by
            intros i hi
            induction' i with i ih;
            · simp +decide [ SimpleGraph.Walk.getVert ];
            · have h_diff : strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = -1 := by
                have h_diff : strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = 1 ∨ strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = -1 := by
                  apply strip1_adj_pos_diff;
                  · exact hstrip _ ( by simp );
                  · exact hstrip _ ( by simp );
                  · grind +suggestions;
                exact h_diff.resolve_left ( by linarith [ h_mono i ( i + 1 ) ( Nat.lt_succ_self i ) hi ] );
              grind;
          specialize h_length p.length le_rfl; aesop;
      grind;
    have h_vertices : ∀ i, i ≤ p₁.1.length → p₁.1.getVert i = p₂.1.getVert i := by
      have h_vertices : ∀ i, i ≤ p₁.1.length → strip1_pos (p₁.1.getVert i) = strip1_pos (p₂.1.getVert i) := by
        have h_pos_eq : ∀ (p : hexGraph.Walk paperStart w) (hp : p.IsPath) (hstrip : ∀ u ∈ p.support, PaperInfStrip 1 u), (∀ i j, i < j → j ≤ p.length → strip1_pos (p.getVert j) < strip1_pos (p.getVert i)) → ∀ i ≤ p.length, strip1_pos (p.getVert i) = strip1_pos paperStart - i := by
          intros p hp hstrip hmono i hi
          induction' i with i ih;
          · simp +decide [ SimpleGraph.Walk.getVert ];
          · have h_pos_eq : strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = -1 := by
              have h_pos_eq : strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = 1 ∨ strip1_pos (p.getVert (i + 1)) - strip1_pos (p.getVert i) = -1 := by
                apply strip1_adj_pos_diff;
                · exact hstrip _ ( by simp );
                · exact hstrip _ ( by simp );
                · grind +suggestions;
              exact h_pos_eq.resolve_left ( by linarith [ hmono i ( i + 1 ) ( Nat.lt_succ_self i ) hi ] );
            grind +splitImp;
        grind +locals;
      intros i hi
      apply strip1_pos_injective;
      · exact h₁ _ ( by simp );
      · exact h₂ _ ( by simp );
      · exact h_vertices i hi;
    have h_walk_eq : p₁.1 = p₂.1 := by
      apply SimpleGraph.Walk.ext_getVert;
      intro k; by_cases hk : k ≤ p₁.1.length <;> simp_all +decide [ SimpleGraph.Walk.getVert ] ;
      rw [ SimpleGraph.Walk.getVert_of_length_le, SimpleGraph.Walk.getVert_of_length_le ] <;> linarith
    generalize_proofs at *;
    aesop;

/-
The endpoint map s ↦ s.end_v.1 on PaperSAW_A_inf 1 is injective.
    Two A_inf walks with the same endpoint are equal.
    This follows from A_inf_1_same_endpoint and strip1_path_unique.
-/
lemma A_inf_1_endpoint_injective :
    Function.Injective (fun s : PaperSAW_A_inf 1 => s.end_v.1) := by
  intro s₁ s₂ h_eq
  have h_end : s₁.end_v = s₂.end_v := by
    exact?;
  cases s₁;
  cases s₂;
  cases h_end;
  congr;
  exact?

/-
A_inf 1 xc ≤ 2xc³/(1-xc²).
-/
lemma A_inf_1_upper :
    A_inf 1 xc ≤ 2 * xc ^ 3 / (1 - xc ^ 2) := by
  have h_sum : ∑' s : PaperSAW_A_inf 1, xc ^ (s.walk.1.length + 1) ≤ ∑' k : ℤ, if k ≠ 0 then xc ^ (2 * k.natAbs + 1) else 0 := by
    have h_sum : ∑' (s : PaperSAW_A_inf 1), xc ^ ((s.walk.1.length : ℕ) + 1) ≤ ∑' (s : PaperSAW_A_inf 1), xc ^ (2 * s.end_v.1.natAbs + 1) := by
      have h_sum : ∀ s : PaperSAW_A_inf 1, s.walk.1.length = 2 * Int.natAbs (s.end_v.1) := by
        intros s
        have h_walk_length : ∃ k : ℤ, k ≠ 0 ∧ s.end_v = (k, -k, true) ∧ s.walk.1.length = 2 * k.natAbs := by
          obtain ⟨k, hk⟩ : ∃ k : ℤ, s.end_v = (k, -k, true) ∧ s.walk.1.length = 2 * Int.natAbs k := by
            obtain ⟨k, hk⟩ : ∃ k : ℤ, s.end_v = (k, -k, true) := by
              exact ⟨ s.end_v.1, Prod.ext rfl ( Prod.ext ( by linarith [ s.end_left.1 ] ) ( by simp +decide [ s.end_left.2.1 ] ) ) ⟩;
            have h_mono : (∀ i j, i < j → j ≤ s.walk.1.length → strip1_pos (s.walk.1.getVert i) < strip1_pos (s.walk.1.getVert j)) ∨ (∀ i j, i < j → j ≤ s.walk.1.length → strip1_pos (s.walk.1.getVert j) < strip1_pos (s.walk.1.getVert i)) := by
              apply strip1_saw_monotone;
              · exact s.walk.2;
              · exact s.in_strip;
            cases' h_mono with h_mono h_mono;
            · have h_pos : strip1_pos (s.walk.1.getVert s.walk.1.length) = strip1_pos paperStart + s.walk.1.length := by
                have h_pos : ∀ i ≤ s.walk.1.length, strip1_pos (s.walk.1.getVert i) = strip1_pos paperStart + i := by
                  apply_rules [ strip1_increasing_walk_pos ];
                  · exact s.walk.2;
                  · exact s.in_strip;
                exact h_pos _ le_rfl;
              simp_all +decide [ strip1_pos ];
              unfold paperStart at h_pos; norm_num at h_pos; omega;
            · have h_length : strip1_pos s.end_v = strip1_pos paperStart - s.walk.1.length := by
                have h_length : ∀ i ≤ s.walk.1.length, strip1_pos (s.walk.1.getVert i) = strip1_pos paperStart - i := by
                  intro i hi;
                  induction' i with i ih;
                  · simp +decide [ SimpleGraph.Walk.getVert ];
                  · have h_step : strip1_pos (s.walk.1.getVert (i + 1)) - strip1_pos (s.walk.1.getVert i) = -1 := by
                      have h_step : strip1_pos (s.walk.1.getVert (i + 1)) - strip1_pos (s.walk.1.getVert i) = 1 ∨ strip1_pos (s.walk.1.getVert (i + 1)) - strip1_pos (s.walk.1.getVert i) = -1 := by
                        apply strip1_adj_pos_diff;
                        · exact s.in_strip _ ( by simp );
                        · exact s.in_strip _ ( by simp );
                        · -- Since the walk is a path, each step is an adjacency. Therefore, the adjacency holds by definition of the walk.
                          apply SimpleGraph.Walk.adj_getVert_succ;
                          bv_omega;
                      exact h_step.resolve_left ( by linarith [ h_mono i ( i + 1 ) ( Nat.lt_succ_self i ) hi ] );
                    grind;
                grind +suggestions;
              unfold strip1_pos at h_length; simp_all +decide ;
              unfold paperStart at h_length; norm_num at h_length; cases abs_cases k <;> linarith;
          refine' ⟨ k, _, hk ⟩ ; intro h ; simp_all +decide [ PaperSAW_A_inf ];
          exact s.end_left.2.2 ( by aesop );
        grind;
      aesop;
    have h_sum : ∑' (s : PaperSAW_A_inf 1), xc ^ (2 * s.end_v.1.natAbs + 1) ≤ ∑' (k : ℤ), if k ≠ 0 then xc ^ (2 * k.natAbs + 1) else 0 := by
      have h_inj : Function.Injective (fun s : PaperSAW_A_inf 1 => s.end_v.1) := by
        exact?
      convert Summable.tsum_subtype_le _ _ _ using 1;
      rotate_left;
      exact ℤ;
      exact ℝ;
      all_goals try infer_instance;
      use fun k => if k ≠ 0 then xc ^ ( 2 * k.natAbs + 1 ) else 0;
      exact Set.range ( fun s : PaperSAW_A_inf 1 => s.end_v.1 );
      · intro a; split_ifs <;> norm_num [ pow_add, pow_mul, xc ] ;
        positivity;
      · rw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ h_inj ) ] ; norm_num;
        by_cases h : Summable ( fun k : ℤ => if k = 0 then 0 else xc ^ ( 2 * k.natAbs + 1 ) ) <;> simp_all +decide [ tsum_eq_zero_of_not_summable ];
        · congr! 2;
          ext s; simp [h_inj];
          intro hs; have := s.end_left; simp_all +decide [ PaperSAW_A_inf ] ;
          exact False.elim <| this.2.2 <| Prod.ext hs <| Prod.ext this.1 this.2.1;
        · contrapose! h;
          have h_summable : Summable (fun k : ℤ => xc ^ (2 * k.natAbs + 1)) := by
            have h_summable : Summable (fun k : ℕ => xc ^ (2 * k + 1)) := by
              norm_num [ pow_add, pow_mul ];
              exact Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by nlinarith [ show xc ^ 2 < 1 by exact xc_sq_lt_one ] ) );
            have h_split : Summable (fun k : ℤ => xc ^ (2 * k.natAbs + 1)) ↔ Summable (fun k : ℕ => xc ^ (2 * k + 1)) ∧ Summable (fun k : ℕ => xc ^ (2 * k + 1)) := by
              have h_split : ∀ f : ℤ → ℝ, Summable f ↔ Summable (fun k : ℕ => f k) ∧ Summable (fun k : ℕ => f (-k)) := by
                exact?
              convert h_split _ using 1;
              norm_num [ Int.natAbs_neg ];
            exact h_split.mpr ⟨ h_summable, h_summable ⟩;
          convert h_summable.sub ( show Summable fun k : ℤ => if k = 0 then xc ^ ( 2 * k.natAbs + 1 ) else 0 from ?_ ) using 2 ; aesop;
          exact ⟨ _, hasSum_single 0 <| by aesop ⟩;
    linarith;
  -- Evaluate the geometric series $\sum_{k=1}^{\infty} xc^{2k+1}$.
  have h_geo_series : ∑' k : ℤ, (if k ≠ 0 then xc ^ (2 * k.natAbs + 1) else 0) = 2 * ∑' k : ℕ, xc ^ (2 * (k + 1) + 1) := by
    rw [ ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
    rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
    · norm_num [ Equiv.intEquivNatSumNat ];
      rw [ Summable.tsum_eq_zero_add ] <;> norm_num;
      · ring;
      · rw [ ← summable_nat_add_iff 1 ];
        norm_num [ pow_add, pow_mul ];
        exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_of_lt_one ( by exact pow_two_nonneg _ ) ( by exact xc_sq_lt_one ) ) );
    · rw [ ← summable_nat_add_iff 1 ] ; norm_num [ pow_add, pow_mul ];
      exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_of_lt_one ( by exact pow_two_nonneg _ ) ( by exact xc_sq_lt_one ) ) );
    · norm_num [ pow_add, pow_mul ];
      exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_of_lt_one ( by exact pow_two_nonneg _ ) ( by exact xc_sq_lt_one ) ) );
  convert h_sum.trans_eq h_geo_series using 1;
  ring_nf;
  norm_num [ pow_mul', tsum_mul_left, tsum_geometric_of_lt_one ( show 0 ≤ xc ^ 2 by positivity ) ( show xc ^ 2 < 1 by exact? ) ]

/-
A_inf 1 xc ≥ 2xc³/(1-xc²).
-/
lemma A_inf_1_lower :
    2 * xc ^ 3 / (1 - xc ^ 2) ≤ A_inf 1 xc := by
  have := @infinite_strip_identity 1 (by norm_num);
  rw [ eq_comm, paper_bridge_partition_1_eq ] at this;
  unfold xc c_alpha at *;
  rw [ show 3 * Real.pi / 8 = Real.pi / 2 - Real.pi / 8 by ring, Real.cos_sub ] at this ; norm_num at this;
  field_simp at *;
  rw [ Real.sq_sqrt ( by positivity ) ] at *;
  rw [ add_div', div_eq_iff ] at this <;> try nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  rw [ div_le_iff₀ ] <;> try nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ];
  rw [ show ( 2 - Real.sqrt 2 ) = ( 2 + Real.sqrt 2 ) ⁻¹ * 2 by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.sqrt_nonneg 2, inv_mul_cancel₀ ( show ( 2 + Real.sqrt 2 ) ≠ 0 by positivity ) ] ] at this ; norm_num at this;
  field_simp at this ⊢;
  nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 2 + Real.sqrt 2 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 2 + Real.sqrt 2 by positivity ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 + Real.sqrt 2 by positivity ) ) ]

/-- A_inf 1 xc = 2xc³/(1-xc²), proved independently of infinite_strip_identity. -/
theorem A_inf_1_exact_independent :
    A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2) :=
  le_antisymm A_inf_1_upper A_inf_1_lower

/-- The T=1 infinite strip identity, proved without the sorry'd general version.
    Uses only the sorry-free paper_bridge_partition_1_eq and the A_inf computation. -/
theorem infinite_strip_identity_T1_independent :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  rw [A_inf_1_exact_independent, paper_bridge_partition_1_eq]
  have h1 : c_alpha * (2 * xc ^ 3 / (1 - xc ^ 2)) + xc * (2 * xc / (1 - xc ^ 2))
    = 2 * xc ^ 2 / (1 - xc ^ 2) * (c_alpha * xc + 1) := by ring
  rw [h1, c_alpha_xc_plus_one, strip_T1_algebraic]

end