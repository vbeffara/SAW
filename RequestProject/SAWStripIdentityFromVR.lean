/-
# Strip Identity from the Vertex Relation via Discrete Stokes

This file derives the strip identity (Lemma 2 of Duminil-Copin & Smirnov 2012)
from the vertex relation (Lemma 1), using the discrete Stokes theorem.

## Key result

The finite strip identity: 1 = c_α·A + B + c_ε·E
is proved from `fresh_vertex_relation` by:
1. Summing the vertex relation over all interior vertices (discrete Stokes)
2. Interior mid-edges cancel (each appears in two vertex sums with opposite signs)
3. Boundary mid-edges survive, giving 0 = -1 + c_α·A + B + c_ε·E

## Status

This file establishes the bridge between the proved `fresh_vertex_relation`
and the needed `infinite_strip_identity`. The key sorry is
`finite_strip_identity_from_vr` — the finite strip identity derived
from the vertex relation.

## Import note

This file does NOT import SAWDiagProof to avoid a circular import.
Instead, SAWDiagProof imports this file and uses B_paper_le_one_from_vr.
-/

import Mathlib
import RequestProject.SAWPairInvolutionProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The vertex relation for the fresh observable (proved) -/

/-- The vertex relation holds at every interior vertex of the strip.
    This is `fresh_vertex_relation` from SAWPairInvolutionProof.lean.
    **Status: PROVED** (modulo `pair_winding_relation`). -/
theorem vertex_relation_at_interior (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v)
    (hv_ne : v ≠ paperStart)
    (h_nbrs : ∀ i : Fin 3, PaperFinStrip T L (hexNeighbors3 v i)) :
    freshVertexSum T L v = 0 :=
  fresh_vertex_relation T L v hv hv_ne h_nbrs

/-! ## Direction vectors sum to zero -/

/-- At every hex vertex, the three direction vectors sum to zero.
    This is the key geometric fact for the discrete Stokes cancellation:
    interior mid-edges cancel when summing the vertex relation. -/
lemma midEdgeDir_sum_zero (v : HexVertex) :
    midEdgeDir v 0 + midEdgeDir v 1 + midEdgeDir v 2 = 0 := by
  have ⟨h1, h2⟩ := midEdgeDir_j_relation v
  rw [h1, h2]; ring_nf
  have hj : j + starRingEnd ℂ j = -1 := by
    unfold j; simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
    simp [Real.cos_pi_sub]
    linarith [Real.cos_pi_div_three]
  linear_combination midEdgeDir v 0 * hj

/-- midEdgeDir v 0 is nonzero (unit length). -/
lemma midEdgeDir_zero_ne_zero' (v : HexVertex) : midEdgeDir v 0 ≠ 0 :=
  midEdgeDir_zero_ne_zero v

/-! ## The finite strip identity

The discrete Stokes step (step 2) and boundary evaluation (step 3)
require substantial combinatorial infrastructure. The key ingredients are:

- `right_boundary_trails_are_paths` — trails to right boundary are SAWs
- `boundary_cos_pos` — all hex boundary angles have positive cos(3θ/8)
- `starting_path_unique` — only the trivial walk from a to a
- The winding telescopes: W = d_last - d_first on the hex lattice -/

/-- **Lemma 2** (Finite Strip Identity).
    For the finite strip S_{T,L} with T ≥ 1, L ≥ 1:
      1 = c_α · A_paper + B_paper + c_ε · E_paper -/
lemma finite_strip_identity_from_vr (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_paper T L xc + B_paper T L xc + c_eps * E_paper T L xc := by
  sorry

/-! ## Consequences of the finite strip identity -/

/-- B_paper(T,L,xc) ≤ 1 follows immediately from the strip identity. -/
lemma B_paper_le_one_from_vr (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  have h_id := finite_strip_identity_from_vr T L hT hL
  have h_A := A_paper_nonneg T L xc xc_pos.le
  have h_E := E_paper_nonneg T L xc xc_pos.le
  have h_ca := c_alpha_pos
  have h_ce := c_eps_pos
  nlinarith

/-! ## Summary

This file provides:
1. `vertex_relation_at_interior` — PROVED (from fresh_vertex_relation)
2. `finite_strip_identity_from_vr` — SORRY (discrete Stokes + boundary eval)
3. `B_paper_le_one_from_vr` — PROVED from #2

The single sorry `finite_strip_identity_from_vr` represents the
discrete Stokes argument + boundary evaluation. It is equivalent to
`B_paper_le_one_strip` (in SAWStripIdentityCorrect.lean).

### Connection to the main theorem

SAWDiagProof imports this file and uses `B_paper_le_one_from_vr`
instead of `B_paper_le_one_strip`, connecting the vertex relation
chain to the bridge partition bounds.
-/

end
