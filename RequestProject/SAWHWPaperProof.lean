/-
# Hammersley-Welsh Bridge Decomposition for Paper Bridges

This file provides infrastructure for the bridge decomposition counting
inequality (paper_bridge_decomp_injection).

## Key results

- `powerset_prod_identity`: ∑_{S ⊆ range N} ∏_{T∈S} f(T) = ∏_{T∈range N} (1 + f(T))
- `diagCoord` and walk depth analysis
- Half-plane walk splitting
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Diagonal coordinate -/

/-- The diagonal coordinate of a hex vertex. -/
def diagCoord (v : HexVertex) : ℤ := v.1 + v.2.1

@[simp] lemma diagCoord_paperStart : diagCoord paperStart = 0 := by
  simp [diagCoord, paperStart]

/-- Each hex step changes diagCoord by at most 1. -/
lemma diagCoord_step_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    |diagCoord w - diagCoord v| ≤ 1 := by
  unfold diagCoord
  have := hexGraph_adj_sum_bound h
  exact abs_le.mpr ⟨by omega, by omega⟩

/-! ## Powerset product identity -/

/-- The powerset product identity (from Mathlib):
    ∏_{T ∈ range N} (1 + f(T)) = ∑_{S ⊆ range N} ∏_{T ∈ S} f(T) -/
lemma powerset_prod_identity {R : Type*} [CommSemiring R]
    (f : ℕ → R) (N : ℕ) :
    ∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, f T =
    ∏ T ∈ Finset.range N, (1 + f T) := by
  exact (Finset.prod_one_add (Finset.range N)).symm

/-- The RHS of paper_bridge_decomp_injection can be rewritten as a product. -/
lemma hw_rhs_eq_prod (f : ℕ → ℝ) (N : ℕ) :
    (∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, f (T + 1)) ^ 2 =
    (∏ T ∈ Finset.range N, (1 + f (T + 1))) ^ 2 := by
  congr 1
  exact powerset_prod_identity (fun T => f (T + 1)) N

/-! ## SAW depth and splitting -/

/-- In a SAW from paperStart, every vertex has diagCoord ≤ walk length. -/
lemma saw_diagCoord_le_length {n : ℕ} (s : SAW paperStart n)
    (v : HexVertex) (hv : v ∈ s.p.1.support) :
    -(n : ℤ) ≤ diagCoord v := by
  have h := hexGraph_walk_sum_bound_neg (s.p.1.takeUntil v hv)
  have hlen := s.p.1.length_takeUntil_le hv
  simp [diagCoord, paperStart] at h ⊢
  linarith [s.l]

/-- In a SAW from paperStart, every vertex has diagCoord ≤ 0 + walk_length. -/
lemma saw_diagCoord_upper {n : ℕ} (s : SAW paperStart n)
    (v : HexVertex) (hv : v ∈ s.p.1.support) :
    diagCoord v ≤ n := by
  have h := hexGraph_walk_sum_bound_pos (s.p.1.takeUntil v hv)
  have hlen := s.p.1.length_takeUntil_le hv
  simp [diagCoord, paperStart] at h ⊢
  linarith [s.l]

end
