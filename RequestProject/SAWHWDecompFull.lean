/-
# Full Hammersley-Welsh Bridge Decomposition

Proof infrastructure for the bridge decomposition inequality:
  ∑_{n≤N} c_n x^n ≤ 2 · (∏_{T=1}^{N} (1 + B_{T}(x)))²
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWDecompHelper

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Key weight inequality for HW decomposition

For the bridge decomposition, the walk weight x^n is bounded by the
product of bridge weights x^{w_i} whenever the sum of bridge widths
≤ n and 0 < x < 1. This is because x^n is decreasing in n. -/

/-- Walk weight ≤ bridge product: if sum of widths ≤ n and 0 < x < 1,
    then x^n ≤ ∏ x^{w_i}. -/
lemma saw_weight_le_bridge_product {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    {n : ℕ} {widths : List ℕ} (h_sum : widths.sum ≤ n) :
    x ^ n ≤ (widths.map (fun T => x ^ T)).prod := by
  -- Since $x < 1$, we have $x^n \leq x^{\text{sum of widths}}$.
  have h_pow_le : x ^ n ≤ x ^ widths.sum := by
    exact pow_le_pow_of_le_one hx.le hx1.le h_sum;
  convert h_pow_le using 1;
  induction widths <;> simp +decide [ *, pow_add ];
  exact Or.inl <| by rename_i k hk ih; exact ih ( by simpa using h_sum.trans' <| by simp +arith +decide ) ( by exact pow_le_pow_of_le_one ( by positivity ) hx1.le <| by simpa using h_sum.trans' <| by simp +arith +decide ) ;

/-! ## Powerset product identity

The sum over subsets of products equals the product of (1 + a_i).
This is already in Mathlib as Finset.prod_one_add or similar. -/

/-
The powerset-product identity: ∑_{S ⊆ F} ∏_{i ∈ S} a(i) = ∏_{i ∈ F} (1 + a(i)).
-/
lemma powerset_prod_eq {F : Finset ℕ} {a : ℕ → ℝ} :
    ∑ S ∈ F.powerset, ∏ i ∈ S, a i = ∏ i ∈ F, (1 + a i) := by
  simp +decide [ add_comm, Finset.prod_add ]

/-! ## Bridge decomposition upper bound (the main sorry)

The Hammersley-Welsh counting inequality relates SAW counts to bridge
partition function products. This is proved by:
1. Splitting each SAW at its minimum diagCoord vertex
2. Decomposing each half-plane walk into bridges of decreasing width
3. Using injectivity of the decomposition (given first vertex choice)
4. Applying the weight bound saw_weight_le_bridge_product -/

/-- The Hammersley-Welsh counting inequality. -/
theorem hw_counting_ineq {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end