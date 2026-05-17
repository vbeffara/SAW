/-
# Independent lower bound for A_inf 1 xc

Constructs explicit PaperSAW_A_inf 1 walks to prove
A_inf 1 xc ≥ 2xc³/(1-xc²) WITHOUT using infinite_strip_identity.
-/

import Mathlib
import RequestProject.SAWAInf1Independent

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Walk construction on the T=1 strip -/

/-- Walk on hex graph from paperStart to (m,-m,true) of length 2m. -/
def strip1_walk_to_pos : (m : ℕ) → hexGraph.Walk paperStart (↑m, -(↑m : ℤ), true)
  | 0 => SimpleGraph.Walk.nil
  | m + 1 =>
    have hadj1 : hexGraph.Adj ((↑m : ℤ), -(↑m : ℤ), true) ((↑m : ℤ), -(↑m : ℤ) - 1, false) := by
      show _ ∨ _; right; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, by push_cast; omega⟩)⟩
    have hadj2 : hexGraph.Adj ((↑m : ℤ), -(↑m : ℤ) - 1, false) ((↑m + 1 : ℤ), -(↑m : ℤ) - 1, true) := by
      show _ ∨ _; left; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by push_cast; ring, rfl⟩)⟩
    have heq : ((↑m + 1 : ℤ), -(↑m : ℤ) - 1, true) = ((↑(m+1) : ℤ), -(↑(m+1) : ℤ), true) := by
      push_cast; ring_nf
    heq ▸ ((strip1_walk_to_pos m).append
      (SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil)))

/-- Walk on hex graph from paperStart to (-m,m,true) of length 2m. -/
def strip1_walk_to_neg : (m : ℕ) → hexGraph.Walk paperStart (-(↑m : ℤ), ↑m, true)
  | 0 => SimpleGraph.Walk.nil
  | m + 1 =>
    have hadj1 : hexGraph.Adj (-(↑m : ℤ), (↑m : ℤ), true) (-(↑m : ℤ) - 1, (↑m : ℤ), false) := by
      show _ ∨ _; right; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by push_cast; ring, rfl⟩)⟩
    have hadj2 : hexGraph.Adj (-(↑m : ℤ) - 1, (↑m : ℤ), false) (-(↑m : ℤ) - 1, (↑m : ℤ) + 1, true) := by
      show _ ∨ _; left; exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, by push_cast; ring⟩)⟩
    have heq : (-(↑m : ℤ) - 1, (↑m : ℤ) + 1, true) = (-(↑(m+1) : ℤ), (↑(m+1) : ℤ), true) := by
      push_cast; ring_nf
    heq ▸ ((strip1_walk_to_neg m).append
      (SimpleGraph.Walk.cons hadj1 (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil)))

/-! ## Properties of constructed walks -/

lemma strip1_walk_to_pos_length (m : ℕ) :
    (strip1_walk_to_pos m).length = 2 * m := by
  unfold strip1_walk_to_pos;
  cases m <;> simp +arith +decide [ * ];
  rename_i n;
  induction n <;> simp +arith +decide [ * ] at *;
  convert ‹_› using 1

lemma strip1_walk_to_neg_length (m : ℕ) :
    (strip1_walk_to_neg m).length = 2 * m := by
  induction' m with m ih;
  · rfl;
  · simp +arith +decide [ *, strip1_walk_to_neg ];
    cases m <;> simp +arith +decide [ ih ]

lemma strip1_walk_to_pos_in_strip (m : ℕ) :
    ∀ v ∈ (strip1_walk_to_pos m).support, PaperInfStrip 1 v := by
  induction' m with m ih;
  · simp +decide [ strip1_walk_to_pos ];
  · unfold PaperInfStrip at *;
    unfold strip1_walk_to_pos at *; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
    cases m <;> simp_all +decide [ SimpleGraph.Walk.support_append ];
    · unfold strip1_walk_to_pos; simp +decide [ SimpleGraph.Walk.support ] ;
      unfold paperStart; aesop;
    · unfold strip1_walk_to_pos; simp +decide [ SimpleGraph.Walk.support_append ] ;
      grind

lemma strip1_walk_to_neg_in_strip (m : ℕ) :
    ∀ v ∈ (strip1_walk_to_neg m).support, PaperInfStrip 1 v := by
  induction' m with m ih;
  · simp +decide [ strip1_walk_to_neg ];
  · unfold PaperInfStrip at *;
    unfold strip1_walk_to_neg at *; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
    cases m <;> simp_all +decide [ SimpleGraph.Walk.support_append ];
    · unfold strip1_walk_to_neg; simp +decide [ SimpleGraph.Walk.support ] ;
      unfold paperStart; aesop;
    · unfold strip1_walk_to_neg; simp +decide [ SimpleGraph.Walk.support_append ] ;
      grind

/-
strip1_pos of vertices in the positive walk's support are bounded.
-/
lemma strip1_walk_to_pos_support_pos_bound (m : ℕ) :
    ∀ v ∈ (strip1_walk_to_pos m).support,
      0 ≤ strip1_pos v ∧ strip1_pos v ≤ 2 * m := by
  intro v hv;
  induction' m with m ih generalizing v <;> simp_all +decide [ Nat.mul_succ, List.range_succ ];
  · cases hv ; aesop;
    contradiction;
  · rw [ show strip1_walk_to_pos ( m + 1 ) = ( strip1_walk_to_pos m ).append ( SimpleGraph.Walk.cons _ ( SimpleGraph.Walk.cons _ SimpleGraph.Walk.nil ) ) from ?_ ] at hv;
    rotate_left;
    exact ( m, -m - 1, false );
    all_goals norm_num [ hexGraph ];
    grind;
    · grind +locals;
    · simp_all +decide [ SimpleGraph.Walk.support_append ];
      rcases hv with ( hv | rfl | rfl ) <;> simp_all +decide [ strip1_pos ];
      · grind;
      · linarith;
      · linarith

/-
The positive walk is a path.
-/
lemma strip1_walk_to_pos_isPath (m : ℕ) :
    (strip1_walk_to_pos m).IsPath := by
  induction' m with m ih;
  · exact?;
  · have := strip1_walk_to_pos_support_pos_bound ( m + 1 );
    unfold strip1_walk_to_pos at *; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
    rcases m with ( _ | m ) <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    simp_all +decide [ SimpleGraph.Walk.support_append, List.nodup_append ];
    constructor;
    · convert ih using 1;
    · intro a a_1; specialize this a a_1; constructor <;> intros <;> simp_all +decide [ strip1_pos ] ;
      · have := strip1_walk_to_pos_support_pos_bound ( m + 1 ) ( ( m + 1, a_1, false ) ) ; simp_all +decide [ strip1_pos ];
      · have := strip1_walk_to_pos_support_pos_bound ( m + 1 ) ( ↑m + 1 + 1, a_1, true ) ‹_›; simp_all +decide [ strip1_pos ] ;

/-
strip1_pos of vertices in the negative walk's support are bounded.
-/
lemma strip1_walk_to_neg_support_pos_bound (m : ℕ) :
    ∀ v ∈ (strip1_walk_to_neg m).support,
      -(2 * (m : ℤ)) ≤ strip1_pos v ∧ strip1_pos v ≤ 0 := by
  induction m <;> simp_all +decide [ Nat.cast_add, Nat.cast_one, add_assoc ];
  unfold strip1_walk_to_neg at * ; simp_all +decide [ SimpleGraph.Walk.support_append ];
  rename_i k hk;
  intro a b; specialize hk a b; rcases k with ( _ | k ) <;> simp_all +decide [ SimpleGraph.Walk.support_append ] ;
  · unfold strip1_walk_to_neg; simp +decide [ strip1_pos ] ;
    unfold paperStart; aesop;
  · unfold strip1_walk_to_neg; simp +decide [ SimpleGraph.Walk.support_append ] ;
    constructor <;> intro h <;> rcases h with ( h | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ strip1_pos ];
    · linarith;
    · grind;
    · grind;
    · constructor <;> linarith

/-
The negative walk is a path.
-/
lemma strip1_walk_to_neg_isPath (m : ℕ) :
    (strip1_walk_to_neg m).IsPath := by
  have h_support_neg : ∀ m : ℕ, ∀ v ∈ (strip1_walk_to_neg m).support, -(2 * (m : ℤ)) ≤ strip1_pos v ∧ strip1_pos v ≤ 0 := by
    exact?;
  induction' m with m ih;
  · exact?;
  · -- The new vertices are not in the support of the walk to m, so the extended walk has no repeats.
    have h_new_vertices_not_in_support : ¬(-(m + 1 : ℤ), (m : ℤ), false) ∈ (strip1_walk_to_neg m).support ∧ ¬(-(m + 1 : ℤ), (m + 1 : ℤ), true) ∈ (strip1_walk_to_neg m).support := by
      constructor <;> intro h <;> specialize h_support_neg m _ h <;> norm_num [ strip1_pos ] at h_support_neg <;> omega;
    unfold strip1_walk_to_neg; simp +decide [ *, SimpleGraph.Walk.cons_isPath_iff ] ;
    cases m <;> simp_all +decide [ SimpleGraph.Walk.isPath_def ];
    simp_all +decide [ SimpleGraph.Walk.support_append, List.nodup_append ];
    lia

/-! ## Converting walks to PaperSAW_A_inf 1 elements -/

/-- For each m ≥ 1, there exists a PaperSAW_A_inf 1 walk to (m, -m, true). -/
lemma exists_A_inf_1_walk_pos (m : ℕ) (hm : 1 ≤ m) :
    ∃ s : PaperSAW_A_inf 1, s.end_v = (↑m, -(↑m : ℤ), true) ∧
      s.walk.1.length = 2 * m := by
  exact ⟨⟨_, ⟨_, strip1_walk_to_pos_isPath m⟩,
    ⟨by simp, rfl, by simp [paperStart]; omega⟩,
    strip1_walk_to_pos_in_strip m⟩,
    rfl, strip1_walk_to_pos_length m⟩

/-- For each m ≥ 1, there exists a PaperSAW_A_inf 1 walk to (-m, m, true). -/
lemma exists_A_inf_1_walk_neg (m : ℕ) (hm : 1 ≤ m) :
    ∃ s : PaperSAW_A_inf 1, s.end_v = (-(↑m : ℤ), ↑m, true) ∧
      s.walk.1.length = 2 * m := by
  exact ⟨⟨_, ⟨_, strip1_walk_to_neg_isPath m⟩,
    ⟨by simp, rfl, by simp [paperStart]; omega⟩,
    strip1_walk_to_neg_in_strip m⟩,
    rfl, strip1_walk_to_neg_length m⟩

/-
For each nonzero integer k, there exists a PaperSAW_A_inf 1 walk.
-/
lemma exists_A_inf_1_walk (k : ℤ) (hk : k ≠ 0) :
    ∃ s : PaperSAW_A_inf 1, s.end_v = (k, -k, true) ∧
      s.walk.1.length = 2 * k.natAbs := by
  cases' lt_or_gt_of_ne hk with hk hk;
  · obtain ⟨ s, hs ⟩ := exists_A_inf_1_walk_neg ( Int.natAbs k ) ( by omega );
    grind;
  · convert exists_A_inf_1_walk_pos k.natAbs ( by linarith [ abs_of_pos hk ] ) using 1 ; norm_num [ abs_of_pos hk ]

/-
Independent lower bound: A_inf 1 xc ≥ 2xc³/(1-xc²).
-/
/-- The injection from {k : ℤ | k ≠ 0} into PaperSAW_A_inf 1 via exists_A_inf_1_walk.  -/
def A_inf_1_walk_of_nonzero (k : {k : ℤ // k ≠ 0}) : PaperSAW_A_inf 1 :=
  (exists_A_inf_1_walk k.1 k.2).choose

lemma A_inf_1_walk_of_nonzero_spec (k : {k : ℤ // k ≠ 0}) :
    (A_inf_1_walk_of_nonzero k).end_v = (k.1, -k.1, true) ∧
    (A_inf_1_walk_of_nonzero k).walk.1.length = 2 * k.1.natAbs := by
  exact (exists_A_inf_1_walk k.1 k.2).choose_spec

lemma A_inf_1_walk_of_nonzero_injective :
    Function.Injective A_inf_1_walk_of_nonzero := by
  -- To prove injectivity, assume two different inputs map to the same walk. Then their endpoints must be equal, leading to the inputs being equal.
  intro k₁ k₂ h_eq
  have h_endpoints : (k₁.1, -k₁.1, true) = (k₂.1, -k₂.1, true) := by
    have := A_inf_1_walk_of_nonzero_spec k₁; have := A_inf_1_walk_of_nonzero_spec k₂; aesop;
  exact Subtype.ext <| by injection h_endpoints;

/-
The endpoint map gives a bijection PaperSAW_A_inf 1 ≃ {k : ℤ // k ≠ 0}.
-/
private lemma A_inf_1_end_ne_zero (s : PaperSAW_A_inf 1) : s.end_v.1 ≠ 0 := by
  by_contra h_contra
  have h_eq : s.end_v = paperStart := by
    have := s.end_left; simp_all +decide [ PaperSAW_A_inf ] ;
    exact this.2.2 ( Prod.ext h_contra ( Prod.ext this.1 this.2.1 ) )
  exact s.end_left.2.2 h_eq

def A_inf_1_equiv : PaperSAW_A_inf 1 ≃ {k : ℤ // k ≠ 0} where
  toFun s := ⟨s.end_v.1, A_inf_1_end_ne_zero s⟩
  invFun k := A_inf_1_walk_of_nonzero k
  left_inv s := by
    apply A_inf_1_endpoint_injective;
    exact ( A_inf_1_walk_of_nonzero_spec _ ).1 |> fun h => congr_arg ( fun x => x.1 ) h
  right_inv k := by
    grind +suggestions

lemma A_inf_1_equiv_length (k : {k : ℤ // k ≠ 0}) :
    (A_inf_1_equiv.symm k).walk.1.length = 2 * k.1.natAbs := by
  exact A_inf_1_walk_of_nonzero_spec k |>.2

/-
The sum over nonzero integers of xc^(2|k|+1) equals 2xc³/(1-xc²).
-/
lemma nonzero_int_xc_sum_eq :
    ∑' (k : {k : ℤ // k ≠ 0}), xc ^ (2 * k.1.natAbs + 1) =
    2 * xc ^ 3 / (1 - xc ^ 2) := by
  -- Split the sum into two parts: one over positive integers and one over negative integers.
  have h_split : ∑' (k : {k : ℤ // k ≠ 0}), xc ^ (2 * (k : ℤ).natAbs + 1) = (∑' (k : ℕ), xc ^ (2 * (k + 1) + 1)) + (∑' (k : ℕ), xc ^ (2 * (k + 1) + 1)) := by
    have h_split : ∑' (k : {k : ℤ // k ≠ 0}), xc ^ (2 * (k : ℤ).natAbs + 1) = ∑' (k : ℤ), if k ≠ 0 then xc ^ (2 * (k : ℤ).natAbs + 1) else 0 := by
      rw [ tsum_eq_tsum_of_ne_zero_bij ];
      use fun x => ⟨ x, by
        exact fun h => x.2 <| by simp +decide [ h ] ; ⟩
      all_goals generalize_proofs at *;
      · exact fun x y h => by aesop;
      · intro x hx; aesop;
      · aesop;
    rw [ h_split, ← Equiv.tsum_eq ( Equiv.intEquivNat.symm ) ];
    rw [ ← tsum_even_add_odd ] <;> norm_num [ Equiv.intEquivNat ];
    · norm_num [ Equiv.intEquivNatSumNat ];
      rw [ Summable.tsum_eq_zero_add ] <;> norm_num;
      rw [ ← summable_nat_add_iff 1 ] ; norm_num [ pow_add, pow_mul ];
      exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by nlinarith [ show xc ^ 2 < 1 by exact xc_sq_lt_one ] ) ) );
    · erw [ ← summable_nat_add_iff 1 ] ; norm_num [ pow_add, pow_mul ];
      exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by nlinarith [ show xc ^ 2 < 1 by exact xc_sq_lt_one ] ) ) );
    · norm_num [ pow_add, pow_mul ];
      exact Summable.mul_right _ ( Summable.mul_right _ ( summable_geometric_of_lt_one ( by exact pow_two_nonneg _ ) ( by exact xc_sq_lt_one ) ) );
  convert h_split using 1;
  ring_nf;
  norm_num [ pow_mul', tsum_mul_left, tsum_geometric_of_lt_one ( show 0 ≤ xc ^ 2 by positivity ) ( show xc ^ 2 < 1 by exact? ) ]

/-
NOTE: We deliberately avoid using A_inf_1_lower (it depends on infinite_strip_identity)
-/
lemma A_inf_1_lower_independent :
    2 * xc ^ 3 / (1 - xc ^ 2) ≤ A_inf 1 xc := by
  -- Use the equivalence to rewrite A_inf
  have h_eq : A_inf 1 xc = ∑' (k : {k : ℤ // k ≠ 0}), xc ^ (2 * k.1.natAbs + 1) := by
    unfold A_inf
    rw [← Equiv.tsum_eq A_inf_1_equiv.symm]
    congr 1; ext k
    simp only [A_inf_1_equiv_length]
  rw [h_eq]; exact nonzero_int_xc_sum_eq.ge

/-- A_inf 1 xc = 2xc³/(1-xc²), proved truly independently of infinite_strip_identity. -/
theorem A_inf_1_exact_truly_independent :
    A_inf 1 xc = 2 * xc ^ 3 / (1 - xc ^ 2) :=
  le_antisymm A_inf_1_upper A_inf_1_lower_independent

/-- The T=1 infinite strip identity, proved truly independently. -/
theorem infinite_strip_identity_T1 :
    1 = c_alpha * A_inf 1 xc + xc * paper_bridge_partition 1 xc := by
  rw [A_inf_1_exact_truly_independent, paper_bridge_partition_1_eq]
  have h1 : c_alpha * (2 * xc ^ 3 / (1 - xc ^ 2)) + xc * (2 * xc / (1 - xc ^ 2))
    = 2 * xc ^ 2 / (1 - xc ^ 2) * (c_alpha * xc + 1) := by ring
  rw [h1, c_alpha_xc_plus_one, strip_T1_algebraic]

end