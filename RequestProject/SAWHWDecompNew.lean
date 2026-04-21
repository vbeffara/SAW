/-
# Hammersley-Welsh Bridge Decomposition: Walk Splitting

This file formalizes the walk splitting step of the Hammersley-Welsh
bridge decomposition from Section 3 of Duminil-Copin & Smirnov (2012).

The key result: each SAW from paperStart can be split at its first vertex
of minimal diagCoord into two "half-plane" walks. Each half-plane walk
decomposes into bridges of decreasing width.

## Reference
  Duminil-Copin, H. and Smirnov, S.,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012, Section 3.
-/

import Mathlib
import RequestProject.SAWHWPaperProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Minimum diagCoord in a walk -/

/-- The minimum diagCoord value among vertices in a walk's support. -/
def walkMinDiagCoord {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoord).foldl min (diagCoord v)

/-
Every vertex in the walk has diagCoord ≥ walkMinDiagCoord.
-/
lemma walkMinDiagCoord_le {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walkMinDiagCoord p ≤ diagCoord u := by
  unfold walkMinDiagCoord; have h_foldl_le : ∀ (l : List ℤ), (∀ x ∈ l, List.foldl min (diagCoord v) l ≤ x) := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_foldl_le _ _ ( List.mem_map.mpr ⟨ u, hu, rfl ⟩ )

/-
The minimum is achieved by some vertex in the support.
-/
lemma walkMinDiagCoord_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoord u = walkMinDiagCoord p := by
  induction p <;> simp_all +decide [ walkMinDiagCoord ];
  induction' ‹hexGraph.Walk _ _› using SimpleGraph.Walk.recOn with _ _ _ _ ih <;> simp_all +decide [ List.foldl_append ];
  · cases min_choice ( diagCoord _ ) ( diagCoord _ ) <;> aesop;
  · cases min_cases ( diagCoord ‹_› ) ( diagCoord ‹_› ) <;> simp_all +decide [ List.foldl_assoc ];
    grind

/-! ## Half-plane walks

A half-plane walk is a SAW where the starting vertex has the minimal
diagCoord among all vertices. This means the walk "goes upward" in diagCoord. -/

/-- A half-plane SAW from vertex v: all vertices have diagCoord ≥ diagCoord v. -/
structure HalfPlaneSAW (v : HexVertex) where
  endpoint : HexVertex
  walk : hexGraph.Path v endpoint
  half_plane : ∀ u ∈ walk.1.support, diagCoord v ≤ diagCoord u

/-! ## Walk splitting at a vertex -/

/-- Splitting a walk preserves total length. -/
lemma walk_split_length' {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    (p.takeUntil u hu).length + (p.dropUntil u hu).length = p.length := by
  have h := SimpleGraph.Walk.take_spec p hu
  conv_rhs => rw [← h]
  exact (SimpleGraph.Walk.length_append _ _).symm

/-! ## SAW splitting into two half-plane walks

For any SAW γ from paperStart of length n:
1. Find the first vertex u* with minimal diagCoord D
2. Split γ at u* into prefix γ₁ (from paperStart to u*) and suffix γ₂ (from u*)
3. γ₁ reversed is a half-plane walk (start = u* has min diagCoord)
4. γ₂ is a half-plane walk (start = u* has min diagCoord among suffix vertices) -/

/-- Split a SAW at the first vertex of minimal diagCoord. The suffix
    forms a half-plane walk (start has minimal diagCoord among suffix vertices). -/
lemma saw_suffix_half_plane {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support)
    (h_min : ∀ v ∈ s.p.1.support, diagCoord u ≤ diagCoord v) :
    ∀ v ∈ (s.p.1.dropUntil u hu).support, diagCoord u ≤ diagCoord v := by
  intro v hv
  exact h_min v (s.p.1.support_dropUntil_subset hu hv)

/-! ## Bridge weight bound

For 0 < x ≤ 1 and bridge lengths summing to at most n,
the product of x^{bridge_length} ≥ x^n. -/

/-
Weight monotonicity: if total bridge length ≤ walk length and 0 < x ≤ 1,
    then x^{walk_length} ≤ ∏ x^{bridge_length}.
-/
lemma bridge_weight_le_walk_weight {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {n : ℕ} {bridge_lengths : List ℕ}
    (h_sum : bridge_lengths.sum ≤ n) :
    x ^ n ≤ (bridge_lengths.map (x ^ ·)).prod := by
  induction' bridge_lengths with bridge_lengths ih generalizing n;
  · exact pow_le_one₀ hx.le hx1;
  · -- By the induction hypothesis, we have x^(n - bridge_lengths) ≤ (ih.map (x^·)).prod.
    have h_ind : x ^ (n - bridge_lengths) ≤ (ih.map (x ^ ·)).prod := by
      grind;
    convert mul_le_mul_of_nonneg_left h_ind ( pow_nonneg hx.le bridge_lengths ) using 1;
    rw [ ← pow_add, Nat.add_sub_of_le ( by simpa using h_sum.trans' ( Nat.le_add_right _ _ ) ) ]

/-! ## Counting inequality: partial sums bounded

Each n-step SAW from paperStart produces (via bridge decomposition)
a pair of subsets of {1, ..., n}. The walk weight x^n is bounded
by the product of bridge partition function values. -/

/-- For 0 < x and x < xc, the partial sum of Z(x) is bounded by
    2 times the square of the powerset product of bridge partition functions.
    This is the Hammersley-Welsh counting inequality. -/
theorem hw_counting_inequality {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end