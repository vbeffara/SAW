/-
# Half-Plane Walk Partition Function and Hammersley-Welsh Bound

## Key insight: use raw dc ∈ [-W, 0] constraint

Using PaperInfStrip W fails for induction because PaperInfStrip 0 is empty.
Using raw dc ∈ [-W, 0] works: at W=0, the walks at dc=0 give
hp_sum_raw(0) = 1 + x (trivial walk + one step to (0,0,false)).
The induction step uses bridge extraction and gives:
  hp_sum(W) ≤ (1+x) × ∏_{T=1}^W (1 + paper_bridge_partition(T, x))
Squaring and multiplying by 2 gives:
  ∑ c_n x^n ≤ 2(1+x)² × (∏(1+B_T))² ≤ 8 × (∏(1+B_T))²

The downstream proof (hw_summable_corrected) only needs a finite bound,
so the constant 8 (vs 2 in the paper) makes no difference.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWBound

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

/-- hp_sum at width 0 is at most 1 + x.
    At dc ∈ [0,0]: only paperStart and (0,0,false) have dc=0.
    Length 0: trivial walk. Length 1: paperStart → (0,0,false).
    Length ≥ 2: impossible (from (0,0,false), all TRUE neighbors
    have dc=0 or dc=1; dc=1 violates dc≤0; dc=0 gives paperStart
    which is already visited). -/
lemma hp_sum_zero_le (N : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    hp_sum 0 N x ≤ 1 + x := by
  sorry

/-! ## Inductive step -/

/-- **Key inductive step**: hp_sum(W+1) ≤ (1 + B_{W+1}) · hp_sum(W).
    Walks in dc ∈ [-(W+1), 0] split into:
    - walks in dc ∈ [-W, 0]: contribute hp_sum(W)
    - walks reaching dc -(W+1): decompose into a PaperBridge of width W+1
      and a remaining walk of width ≤ W, contributing ≤ B_{W+1} · hp_sum(W). -/
lemma hp_sum_step {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (W N : ℕ) :
    hp_sum (W + 1) N x ≤
    (1 + paper_bridge_partition (W + 1) x) * hp_sum W N x := by
  sorry

/-! ## The inductive bound -/

/-- Half-plane walk bound: hp_sum(W) ≤ (1+x) × ∏(1+B_T).
    By induction on W using hp_sum_step. -/
theorem hp_sum_le_prod {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (W N : ℕ) :
    hp_sum W N x ≤
    (1 + x) * ∏ T ∈ Finset.range W, (1 + paper_bridge_partition (T + 1) x) := by
  induction W with
  | zero =>
    simp
    exact hp_sum_zero_le N x hx.le hx1.le
  | succ W ih =>
    rw [Finset.prod_range_succ]
    calc hp_sum (W + 1) N x
        ≤ (1 + paper_bridge_partition (W + 1) x) * hp_sum W N x :=
          hp_sum_step hx hx1 W N
      _ ≤ (1 + paper_bridge_partition (W + 1) x) *
          ((1 + x) * ∏ T ∈ Finset.range W, (1 + paper_bridge_partition (T + 1) x)) := by
          apply mul_le_mul_of_nonneg_left ih
          exact add_nonneg (by norm_num) (tsum_nonneg fun _ => pow_nonneg hx.le _)
      _ = (1 + x) * ((∏ T ∈ Finset.range W, (1 + paper_bridge_partition (T + 1) x)) *
          (1 + paper_bridge_partition (W + 1) x)) := by ring

/-! ## SAW to half-plane walk reduction -/

/-- Each n-step SAW from hexOrigin decomposes into two half-plane walks. -/
theorem saw_sum_le_hp_sq {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (hp_sum N N x) ^ 2 := by
  sorry

/-! ## Combined bound -/

/-- The Hammersley-Welsh bridge decomposition inequality.
    The constant 8 (vs 2 in the paper) comes from the vertex formulation:
    the paper uses mid-edges where the width-0 strip is trivial,
    while our vertex formulation has hp_sum(0) = 1+x ≤ 2. -/
theorem hw_injection_bound_correct {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    8 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 := by
  calc ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n
      ≤ 2 * (hp_sum N N x) ^ 2 := saw_sum_le_hp_sq hx hx1 N
    _ ≤ 2 * ((1 + x) * ∏ T ∈ Finset.range N,
          (1 + paper_bridge_partition (T + 1) x)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        exact pow_le_pow_left₀ (hp_sum_nonneg N N x hx.le)
          (hp_sum_le_prod hx hx1 N N) 2
    _ ≤ 8 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 := by
        rw [mul_pow]
        have h1x : (1 + x) ^ 2 ≤ 4 := by nlinarith
        have hprod_nn : (0 : ℝ) ≤ (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 :=
          sq_nonneg _
        nlinarith

end
