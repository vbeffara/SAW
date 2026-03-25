/-
# Elementary lower bound on SAW counts

From Section 1 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the hexagonal lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

The paper states: "Elementary bounds on c_n (for instance √2^n ≤ c_n ≤ 3·2^{n-1})
guarantee that c_n grows exponentially fast."

## Content

This file proves:
1. saw_count 2 ≥ 6 (by explicit construction)
2. saw_count 2 = 6 (combined with upper bound)
3. The connective constant is at least √2
-/

import RequestProject.SAWZigzag

open Real

noncomputable section

/-! ## Adjacency lemmas -/

/-- Adjacency: (k, y, false) → (k+1, y, true). -/
lemma hex_adj_right (k y : ℤ) : hexGraph.Adj (k, y, false) (k + 1, y, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩

/-- Adjacency: (k, y, true) → (k, y, false). -/
lemma hex_adj_same (k y : ℤ) : hexGraph.Adj (k, y, true) (k, y, false) := by
  right; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Adjacency: (k, y, true) → (k, y-1, false). -/
lemma hex_adj_down (k y : ℤ) : hexGraph.Adj (k, y, true) (k, y - 1, false) := by
  right; refine ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩; simp

/-- Adjacency: (k, y, false) → (k, y, true). -/
lemma hex_adj_same' (k y : ℤ) : hexGraph.Adj (k, y, false) (k, y, true) := by
  left; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Adjacency: (k, y, true) → (k-1, y, false). -/
lemma hex_adj_left (k y : ℤ) : hexGraph.Adj (k, y, true) (k - 1, y, false) := by
  right; refine ⟨rfl, rfl, Or.inr (Or.inl ⟨?_, rfl⟩)⟩; omega

/-! ## Construction of 6 explicit 2-step SAWs

We construct all 6 two-step SAWs from hexOrigin to prove saw_count 2 ≥ 6.
-/

/-
PROBLEM
saw_count 2 ≥ 6: there are at least 6 two-step SAWs from the origin.

PROVIDED SOLUTION
Construct 6 distinct SAW hexOrigin 2 elements. Each is constructed as a Walk.cons adj1 (Walk.cons adj2 Walk.nil) wrapped in a path and SAW.

The 6 endpoints are: (-1,0,F), (0,-1,F), (1,0,F), (1,-1,F), (0,1,F), (-1,1,F). All distinct.

For each walk, the support has 3 vertices: hexOrigin = (0,0,F), an intermediate true vertex, and the endpoint false vertex. These 3 are always distinct (different coordinates/Bool), so each walk is a path.

Approach: construct a Finset of SAW hexOrigin 2 with 6 elements, then 6 ≤ card univ.

Or simpler: use Fintype.six_le_card or show that there exist s1 s2 s3 s4 s5 s6 : SAW hexOrigin 2 that are pairwise different, then card ≥ 6.

Actually simplest: construct 6 elements, prove they're pairwise distinct by comparing endpoints (the w field), then use a cardinality argument.
-/
lemma saw_count_two_ge : 6 ≤ saw_count 2 := by
  -- Let's construct the six distinct SAWs from the origin to the points (-1,0), (0,-1), (1,0), (1,-1), (0,1), and (-1,1).
  have h_walks : ∃ s1 s2 s3 s4 s5 s6 : SAW hexOrigin 2,
    s1.w = (-1, 0, false) ∧
    s2.w = (0, -1, false) ∧
    s3.w = (1, 0, false) ∧
    s4.w = (1, -1, false) ∧
    s5.w = (0, 1, false) ∧
    s6.w = (-1, 1, false) := by
      simp +zetaDelta at *;
      refine' ⟨ _, _, _, _, _ ⟩;
      · refine' ⟨ ⟨ _, _, _ ⟩, rfl ⟩;
        constructor;
        rotate_left;
        exact SimpleGraph.Walk.cons ( hex_adj_same' 0 0 ) ( SimpleGraph.Walk.cons ( hex_adj_left 0 0 ) SimpleGraph.Walk.nil );
        simp +zetaDelta at *;
        simp +decide [ SimpleGraph.Walk.isPath_def ];
      · refine' ⟨ ⟨ _, _, _ ⟩, rfl ⟩;
        constructor;
        rotate_left;
        exact SimpleGraph.Walk.cons ( hex_adj_same' 0 0 ) ( SimpleGraph.Walk.cons ( hex_adj_down 0 0 ) SimpleGraph.Walk.nil );
        exact SimpleGraph.Walk.length_cons (hex_adj_same' 0 0)
          (SimpleGraph.Walk.cons (hex_adj_down 0 0) SimpleGraph.Walk.nil);
        simp +decide [SimpleGraph.Walk.isPath_def];
      · refine' ⟨ ⟨ _, _, _ ⟩, rfl ⟩;
        constructor;
        rotate_left;
        exact SimpleGraph.Walk.cons ( hex_adj_right 0 0 ) ( SimpleGraph.Walk.cons ( hex_adj_same 1 0 ) SimpleGraph.Walk.nil );
        exact SimpleGraph.Walk.length_cons (hex_adj_right 0 0)
          (SimpleGraph.Walk.cons (hex_adj_same 1 0) SimpleGraph.Walk.nil);
        simp +decide [SimpleGraph.Walk.isPath_def];
      · refine' ⟨ ⟨ _, _, _ ⟩, rfl ⟩;
        exact ⟨ SimpleGraph.Walk.cons ( hex_adj_right 0 0 ) ( SimpleGraph.Walk.cons ( hex_adj_down 1 0 ) SimpleGraph.Walk.nil ), by simp +decide ⟩;
        rfl;
      · constructor;
        · refine' ⟨ ⟨ ( 0, 1, false ), _, _ ⟩, rfl ⟩ <;> norm_num [ hexGraph ];
          refine' ⟨ SimpleGraph.Walk.cons _ ( SimpleGraph.Walk.cons _ SimpleGraph.Walk.nil ), _ ⟩ <;> norm_num [ hexGraph ];
          rotate_left;
          exact ( 0, 1, true );
          all_goals norm_num [ hexOrigin ];
        · refine' ⟨ ⟨ _, _, _ ⟩, rfl ⟩;
          constructor;
          rotate_left;
          refine' SimpleGraph.Walk.cons _ ( SimpleGraph.Walk.cons _ SimpleGraph.Walk.nil );
          rotate_left;
          exact ( 0, 1, true );
          all_goals norm_num [ hexGraph ];
          all_goals norm_num [ hexOrigin ];
  obtain ⟨ s1, s2, s3, s4, s5, s6, h1, h2, h3, h4, h5, h6 ⟩ := h_walks;
  have h_distinct : s1 ≠ s2 ∧ s1 ≠ s3 ∧ s1 ≠ s4 ∧ s1 ≠ s5 ∧ s1 ≠ s6 ∧ s2 ≠ s3 ∧ s2 ≠ s4 ∧ s2 ≠ s5 ∧ s2 ≠ s6 ∧ s3 ≠ s4 ∧ s3 ≠ s5 ∧ s3 ≠ s6 ∧ s4 ≠ s5 ∧ s4 ≠ s6 ∧ s5 ≠ s6 := by
    aesop;
  have h_card : Finset.card ({s1, s2, s3, s4, s5, s6} : Finset (SAW hexOrigin 2)) = 6 := by
    simp +decide [ h_distinct ];
  exact h_card ▸ Finset.card_le_univ _

/-- saw_count 2 = 6: there are exactly 6 two-step SAWs from the origin. -/
lemma saw_count_two : saw_count 2 = 6 := by
  have h_le : saw_count 2 ≤ 6 := by
    calc saw_count 2 ≤ 2 * saw_count 1 := saw_count_step_le_mul_two 1 (by omega)
      _ = 2 * 3 := by rw [saw_count_one]
      _ = 6 := by ring
  have h_ge := saw_count_two_ge
  omega

/-- For n ≥ 1, 2^n ≤ c_n^2. This is used to show c_n^{1/n} ≥ √2.
    The proof uses c_2 = 6 ≥ 4 = 2^2 and submultiplicativity. -/
lemma saw_count_sq_ge_two_pow (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ saw_count n ^ 2 :=
  saw_count_sq_ge_two_pow' n hn

/-
PROBLEM
The connective constant satisfies μ ≥ √2.
    This uses the infimum definition and the bound c_n^{1/n} ≥ √2 for all n ≥ 1.

PROVIDED SOLUTION
Use le_csInf to show that √2 is a lower bound of the set { c_n^{1/n} | n ≥ 1 }.

For this, we need: the set is nonempty (take n=1), and for all n ≥ 1, √2 ≤ c_n^{1/n}, i.e., c_n ≥ (√2)^n, i.e., c_n^2 ≥ 2^n.

Use saw_count_sq_ge_two_pow for the bound c_n^2 ≥ 2^n.

Then √2 ≤ c_n^{1/n} follows from: (√2)^n ≤ c_n, i.e., 2^{n/2} ≤ c_n.

Actually, since saw_count_sq_ge_two_pow gives 2^n ≤ c_n^2, we get c_n ≥ √(2^n) = (√2)^n. Then c_n^{1/n} ≥ √2.

In terms of Real.rpow: (saw_count n : ℝ) ^ (1/(n:ℝ)) ≥ √2.

For the connective_constant definition: connective_constant = sInf ((fun n => (saw_count n : ℝ) ^ (1/(n:ℝ))) '' Set.Ici 1).

Use le_csInf with:
- nonempty: ⟨(saw_count 1 : ℝ)^(1/1), 1, le_refl 1, rfl⟩
- bound: for x in the image set, x = c_n^{1/n} for some n ≥ 1, and c_n^{1/n} ≥ √2.
-/
theorem connective_constant_ge_sqrt_two :
    Real.sqrt 2 ≤ connective_constant := by
  refine' le_csInf _ _ <;> norm_num;
  -- Use the lemma saw_count_sq_ge_two_pow to show that saw_count a ^ 2 ≥ 2 ^ a.
  have h_sq : ∀ a : ℕ, 1 ≤ a → (saw_count a : ℝ) ^ 2 ≥ 2 ^ a := by
    exact_mod_cast saw_count_sq_ge_two_pow;
  -- Taking the a-th root of both sides of the inequality (saw_count a : ℝ) ^ 2 ≥ 2 ^ a, we get (saw_count a : ℝ) ^ (2/a) ≥ 2.
  have h_root : ∀ a : ℕ, 1 ≤ a → (saw_count a : ℝ) ^ (2 / a : ℝ) ≥ 2 := by
    intros a ha
    have h_root : ((saw_count a : ℝ) ^ 2) ^ (1 / a : ℝ) ≥ 2 := by
      exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) ( h_sq a ha ) ( by positivity ) );
    convert h_root using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
  intro a ha; specialize h_root a ha; rw [ Real.sqrt_eq_rpow ] ; convert Real.rpow_le_rpow ( by positivity ) h_root ( by positivity : ( 0 : ℝ ) ≤ 1 / 2 ) using 1 ; rw [ ← Real.rpow_mul ( by positivity ) ] ; ring_nf;

end
