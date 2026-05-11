/-
# Hammersley-Welsh Bridge Decomposition — Infrastructure

Additional infrastructure for the HW bridge decomposition argument.
Connects the existing walk splitting lemmas to the bridge decomposition.
-/

import Mathlib
import RequestProject.SAWHWCore
import RequestProject.SAWBridgeDecompNew

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## SAW diagCoord range bounds -/

/-- For SAWs from paperStart, vertices have diagCoordZ in [-n, n]. -/
lemma saw_dc_bounded {n : ℕ} (s : SAW paperStart n)
    (v : HexVertex) (hv : v ∈ s.p.1.support) :
    -(n : ℤ) ≤ diagCoordZ v ∧ diagCoordZ v ≤ n := by
  have hb := walk_diagCoordZ_bound s.p.1 v hv
  simp [diagCoordZ_paperStart] at hb
  constructor <;> linarith [hb.1, hb.2, s.l]

/-- The "strip width" of a SAW is at most n. -/
lemma saw_width_le_length {n : ℕ} (s : SAW paperStart n) :
    walkMinDiagCoord s.p.1 ≥ -(n : ℤ) := by
  have hmin := walkMinDiagCoord_achieved s.p.1
  obtain ⟨u, hu, hueq⟩ := hmin
  rw [← hueq]
  exact (saw_dc_bounded s u hu).1

/-! ## The powerset product identity -/

/-- ∑_{S ⊆ range(N)} ∏_{T ∈ S} f(T) = ∏_{T ∈ range(N)} (1 + f(T)). -/
lemma powerset_prod_identity' (N : ℕ) (f : ℕ → ℝ) :
    ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, f T =
    ∏ T ∈ Finset.range N, (1 + f T) :=
  Finset.sum_powerset_prod_eq_prod_add_one _ _

/-! ## Bridge partition bounds -/

/-- Bridge partition function is nonneg for positive x. -/
lemma bridge_partition_nonneg' (T : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ paper_bridge_partition T x :=
  tsum_nonneg fun _ => pow_nonneg hx.le _

end
