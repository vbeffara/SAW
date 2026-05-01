/-
# Hammersley-Welsh Upper Bound: Z(x) < ∞ for x < xc

This file provides helper lemmas toward the bridge decomposition
counting inequality:
  ∑_{n≤N} c_n x^n ≤ 2 · (∏_{T=1}^N (1 + B_T(x)))²

The proof follows Hammersley-Welsh (1962) as presented in
Duminil-Copin & Smirnov (2012), Section 3.
-/

import Mathlib
import RequestProject.SAWPaperChain
import RequestProject.SAWBridgeDecompCore

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## SAW width bound -/

/-
An n-step SAW from paperStart has dc in [-n, n] for all vertices.
-/
lemma saw_dc_bound {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support) :
    |hexDiagCoord u| ≤ n := by
  obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hu;
  -- By induction on $k$, we can show that the absolute value of the diagonal coordinate of the $k$-th vertex in the walk is at most $k$.
  have h_ind : ∀ k : Fin (s.p.1.support.length), |hexDiagCoord (s.p.1.support.get k)| ≤ k.val := by
    intro ⟨ k, hk ⟩ ; induction' k with k ih <;> simp_all +decide [ Fin.add_def, Fin.last ] ;
    have h_adj : hexGraph.Adj (s.p.1.support[k]) (s.p.1.support[k + 1]) := by
      have h_adj : ∀ {v w : HexVertex} {p : SimpleGraph.Walk hexGraph v w}, ∀ k : ℕ, k + 1 < p.support.length → hexGraph.Adj (p.support[k]!) (p.support[k + 1]!) := by
        intros v w p k hk; induction' p with v w p ih generalizing k; aesop;
        rcases k with ( _ | k ) <;> simp_all +decide [ SimpleGraph.Walk.support_cons ];
      grind;
    have h_adj_bound : |hexDiagCoord (s.p.1.support[k + 1]) - hexDiagCoord (s.p.1.support[k])| ≤ 1 := by
      exact?;
    grind +splitIndPred;
  grind +suggestions

/- Note: An n-step SAW from paperStart does NOT necessarily fit in PaperInfStrip n.
   A SAW can go in any direction on the full lattice. Only walks staying in the
   strip are counted by A_paper, B_paper, E_paper. -/

/-! ## Powerset product lower bounds -/

/-
The powerset product is always ≥ 1 (since the empty set contributes 1).
-/
lemma powerset_prod_ge_one {N : ℕ} {f : ℕ → ℝ} (hf : ∀ i ∈ Finset.range N, 0 ≤ f i) :
    1 ≤ ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, f T := by
  exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun S _ => Finset.prod_nonneg fun T hT => hf T <| Finset.mem_range.mpr <| Finset.mem_range.mp <| Finset.mem_powerset.mp ‹_› hT ) ( Finset.mem_powerset.mpr <| Finset.empty_subset _ ) )

/-
c_0 = 1.
-/
lemma saw_count_zero' : saw_count 0 = 1 := by
  -- The only SAW of length 0 is the walk that stays at the origin.
  have h_saw_zero : ∀ s : SAW hexOrigin 0, s = ⟨hexOrigin, ⟨SimpleGraph.Walk.nil, by simp⟩, rfl⟩ := by
    rintro ⟨ w, p, l ⟩;
    rcases p with ⟨ _ | ⟨ _, _ ⟩, _ ⟩ ; simp_all +decide;
    cases l;
  exact Fintype.card_eq_one_iff.mpr ⟨ _, h_saw_zero ⟩

/-! ## Base case of HW inequality -/

/-
HW inequality for N=0: c_0 = 1 ≤ 2.
-/
lemma hw_base_case {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range 1, (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range 0).powerset, ∏ T ∈ S,
      paper_bridge_partition (T + 1) x) ^ 2 := by
  norm_num [ saw_count_zero' ]

end