/-
# Half-Plane Walk Partition Function — Definitions and Base Case

Defines hp_walk_count and hp_sum, and proves the base case (width 0).
The inductive step and downstream theorems are in SAWHWStepHelpers.lean
and SAWHWSawBound.lean to avoid circular imports.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWBound
import RequestProject.SAWHWLastVertex

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Half-plane walk count using raw dc constraint -/

/-- The number of SAWs of length n from paperStart staying in dc ∈ [-W, 0]. -/
def hp_walk_count (W n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0))

/-- The finite partial sum of the half-plane walk partition function. -/
def hp_sum (W N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (hp_walk_count W n : ℝ) * x ^ n

/-- hp_sum is nonneg for x ≥ 0. -/
lemma hp_sum_nonneg (W N : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ hp_sum W N x :=
  Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

/-! ## Base case: width 0 -/

/-- No SAW of length ≥ 2 from paperStart stays at dc = 0. -/
lemma hp_walk_count_zero_ge2 (n : ℕ) (hn : 2 ≤ n) : hp_walk_count 0 n = 0 := by
  refine' Finset.card_eq_zero.mpr _
  ext s
  rcases s with ⟨ w, ⟨ p, hp ⟩, hn ⟩ ; rcases p with ( _ | ⟨ u, _ | ⟨ v, p ⟩ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons ] ;
  · cases hn ; contradiction;
  · cases hn ; aesop;
  · rename_i k hk ; simp_all +decide [ hexGraph ];
    rcases k with ⟨ k₁, k₂, k₃ ⟩ ; rcases hk with ⟨ hk₁, hk₂, hk₃ ⟩ ; simp_all +decide [ hexGraph ] ;
    rcases u with ( ⟨ ⟩ | ⟨ ⟩ ) <;> rcases v with ( ⟨ ⟩ | ⟨ ⟩ ) <;> simp_all +decide [ hexGraph ];
    rcases ‹k₃ = false ∧ _› with ⟨ rfl, h | h | h ⟩ <;> simp_all +decide [ paperStart ];
    · rcases ‹hk₃ = true ∧ _› with ⟨ rfl, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ⟩ <;> simp_all +decide [ hexGraph ];
      · rcases p with ( _ | ⟨ u, p ⟩ ) <;> simp_all +decide [ hexGraph ];
        grind;
      · rcases p with ( _ | ⟨ u, p ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons ];
        rcases u with ( ⟨ ⟩ | ⟨ ⟩ ) <;> simp_all +decide [ hexGraph ];
        grind;
    · omega;
    · omega

/-
At most 1 walk of length 0 stays at dc=0: the trivial walk.
-/
lemma hp_walk_count_zero_zero_le : hp_walk_count 0 0 ≤ 1 := by
  unfold hp_walk_count;
  simp +decide [ Finset.card_le_one ];
  rintro ⟨ a, ⟨ b, c ⟩, d ⟩ e ⟨ f, ⟨ g, h ⟩, i ⟩ j;
  cases b <;> cases g <;> aesop

/-
At most 1 walk of length 1 stays at dc=0.
-/
lemma hp_walk_count_zero_one_le : hp_walk_count 0 1 ≤ 1 := by
  refine' Finset.card_le_one.mpr _;
  intros a ha b hb
  have h_step : a.p.1.getVert 1 = (0, 0, false) ∧ b.p.1.getVert 1 = (0, 0, false) := by
    rcases a with ⟨ w, ⟨ p, hp ⟩, hl ⟩ ; rcases b with ⟨ w', ⟨ p', hp' ⟩, hl' ⟩ ; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
    rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> rcases p' with ( _ | ⟨ _, _, p' ⟩ ) <;> norm_num at *;
    rcases w with ⟨ x, y, b ⟩ ; rcases w' with ⟨ x', y', b' ⟩ ; simp_all +decide [ hexGraph ] ;
    unfold hexGraph at *; simp_all +decide [ paperStart ] ;
    omega;
  rcases a with ⟨ w₁, ⟨ p₁, hp₁ ⟩, l₁ ⟩ ; rcases b with ⟨ w₂, ⟨ p₂, hp₂ ⟩, l₂ ⟩ ; simp_all +decide [ SAW ];
  rcases p₁ with ( _ | ⟨ _, _, p₁ ⟩ ) <;> rcases p₂ with ( _ | ⟨ _, _, p₂ ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ] ;
  grind +locals

/-- hp_sum at width 0 is at most 1 + x. -/
lemma hp_sum_zero_le (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    hp_sum 0 N x ≤ 1 + x := by
  unfold hp_sum
  have h2 : ∀ n ≥ 2, (hp_walk_count 0 n : ℝ) * x ^ n = 0 := by
    intro n hn; rw [hp_walk_count_zero_ge2 n hn]; simp
  have h0 : (hp_walk_count 0 0 : ℝ) * x ^ 0 ≤ 1 := by
    simp; exact_mod_cast hp_walk_count_zero_zero_le
  have h1 : (hp_walk_count 0 1 : ℝ) * x ^ 1 ≤ x := by
    simp; exact mul_le_of_le_one_left hx (by exact_mod_cast hp_walk_count_zero_one_le)
  calc ∑ n ∈ Finset.range (N + 1), (hp_walk_count 0 n : ℝ) * x ^ n
      ≤ ∑ n ∈ Finset.range 2, (hp_walk_count 0 n : ℝ) * x ^ n := by
        by_cases hN : N ≤ 1
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (by omega)
          · intros; exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
        · rw [← Finset.sum_range_add_sum_Ico
            (f := fun n => (hp_walk_count 0 n : ℝ) * x ^ n) (by omega : 2 ≤ N + 1)]
          have : ∑ n ∈ Finset.Ico 2 (N + 1), (hp_walk_count 0 n : ℝ) * x ^ n = 0 :=
            Finset.sum_eq_zero fun n hn => h2 n (Finset.mem_Ico.mp hn).1
          linarith
    _ = (hp_walk_count 0 0 : ℝ) * x ^ 0 + (hp_walk_count 0 1 : ℝ) * x ^ 1 := by
        simp [Finset.sum_range_succ]
    _ ≤ 1 + x := add_le_add h0 h1

end
