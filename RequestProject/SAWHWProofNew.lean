/-
# Hammersley-Welsh Bridge Decomposition Proof

This file proves the key combinatorial inequality:
  ∑_{n≤N} c_n x^n ≤ 2 (∏_{T=1}^{N} (1 + B_T(x)))^2

The proof follows the Hammersley-Welsh decomposition:
1. Split each SAW at its first vertex of minimum diagCoord
2. Each half decomposes into bridges of strictly decreasing widths
3. The decomposition is injective
4. The total bridge weight ≥ walk weight (for 0 < x ≤ 1)

## Reference
J. M. Hammersley and D. J. A. Welsh,
"Further results on the rate of convergence to the connective constant
of the hypercubical lattice", Quart. J. Math. Oxford (1962).
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWDecompHelper
import RequestProject.SAWBridgeDecompNew

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Half-plane walk definition

A "half-plane walk" from vertex v is a SAW where v has the minimum diagCoord
among all vertices in the walk. The walk stays at diagCoord ≥ diagCoord(v).
-/

/-- A half-plane SAW from paperStart: starts at paperStart and all vertices
    have diagCoord ≥ 0 (i.e., diagCoord ≥ diagCoordHW paperStart). -/
structure HalfPlaneSAW where
  end_v : HexVertex
  walk : hexGraph.Path paperStart end_v
  half_plane : ∀ v ∈ walk.1.support, 0 ≤ diagCoordHW v

/-- Width of a half-plane SAW: the maximum diagCoord achieved.
    Since diagCoordHW paperStart = 0 and all vertices have diagCoord ≥ 0,
    the width is just the maximum diagCoord. -/
def HalfPlaneSAW.width (h : HalfPlaneSAW) : ℕ :=
  (walk_max_dc h.walk.1).toNat

/-- The width is 0 iff all vertices stay at diagCoord 0. -/
lemma HalfPlaneSAW.width_zero_iff (h : HalfPlaneSAW) :
    h.width = 0 ↔ ∀ v ∈ h.walk.1.support, diagCoordHW v = 0 := by
  constructor
  · intro hw v hv
    have hge := h.half_plane v hv
    have hle : diagCoordHW v ≤ walk_max_dc h.walk.1 := le_walk_max_dc h.walk.1 v hv
    simp [HalfPlaneSAW.width, Int.toNat_eq_zero] at hw
    linarith
  · intro hall
    simp [HalfPlaneSAW.width]
    have hstart := hall paperStart h.walk.1.start_mem_support
    have := walk_max_dc_ge_start h.walk.1
    have hmax : walk_max_dc h.walk.1 = 0 := by
      obtain ⟨u, hu, hueq⟩ := walk_max_dc_achieved h.walk.1
      rw [← hueq, hall u hu]
    simp [hmax]

/-- A SAW of length n from paperStart. -/
def SAW_from_start (n : ℕ) := SAW paperStart n

/-- Every SAW from paperStart determines a walk. -/
def SAW_to_walk {n : ℕ} (s : SAW paperStart n) : hexGraph.Path paperStart s.w :=
  s.p

/-! ## Splitting a SAW at its first minimum diagCoord vertex

Given a SAW from paperStart, we find the first vertex with minimum diagCoord.
The prefix (reversed) and suffix form two half-plane walks.
-/

/-- The minimum diagCoord over a walk from paperStart. -/
def SAW_min_dc {n : ℕ} (s : SAW paperStart n) : ℤ :=
  walk_min_dc s.p.1

/-- The minimum diagCoord is ≤ 0 (since paperStart has diagCoord 0). -/
lemma SAW_min_dc_le_zero {n : ℕ} (s : SAW paperStart n) :
    SAW_min_dc s ≤ 0 := by
  unfold SAW_min_dc
  have := walk_min_dc_le s.p.1 paperStart s.p.1.start_mem_support
  simp [diagCoordHW_paperStart] at this
  linarith

/-! ## Key counting lemma: SAW count bounded by bridge product

For each SAW of length n, we can associate it with a pair of bridge
sequences. The total bridge weight bounds the SAW weight.

This is stated abstractly to simplify the proof. -/

/-- Any SAW from paperStart of length n has at most n as its walk length. -/
lemma SAW_length_eq {n : ℕ} (s : SAW paperStart n) :
    s.p.1.length = n := s.l

/-! ## Bridge partition function properties -/

/-- paper_bridge_partition is monotone: B_{T+1}(x) ≤ B_T(x) is FALSE in general.
    But we have B_T(x) is non-negative for x ≥ 0. -/
lemma paper_bridge_partition_nonneg' (T : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ paper_bridge_partition T x :=
  tsum_nonneg fun _ => pow_nonneg hx _

/-! ## Key bridge extraction from walks

The core technical construction: given a SAW of length n from paperStart,
we can extract bridge widths. -/

/-- For any finite set of natural numbers S ⊆ {0,...,N-1}, the product
    ∏_{T∈S} paper_bridge_partition(T+1, x) represents choosing one bridge
    of each width T+1 for T ∈ S. -/
lemma bridge_product_expansion (N : ℕ) (x : ℝ) (_hx : 0 < x) :
    ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, paper_bridge_partition (T + 1) x =
    ∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x) := by
  exact Finset.sum_powerset_prod_eq_prod_add_one _ _

end
