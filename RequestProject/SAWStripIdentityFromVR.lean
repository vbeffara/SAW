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
import RequestProject.SAWStartVertex

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## The vertex relation for the fresh observable (proved) -/

/-- The vertex relation holds at every interior vertex of the strip.
    This is `fresh_vertex_relation` from SAWPairInvolutionProof.lean.
    **Status: PROVED** (modulo `pair_winding_relation`). -/
theorem vertex_relation_at_interior (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v)
    (hv_ne : v ≠ paperStart) :
    freshVertexSum T L v = 0 :=
  fresh_vertex_relation T L v hv hv_ne

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

/- **Lemma 2** (Finite Strip Identity), original formulation.

    ```
    lemma finite_strip_identity_from_vr (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
        1 = c_alpha * A_paper T L xc + B_paper T L xc + c_eps * E_paper T L xc
    ```

    This exact form is **not** what the discrete Stokes argument delivers, and
    is very unlikely to be true as stated.  The escape term produced by the
    boundary sum is a sum over the escape *mid-edges* leaving the strip,
    whereas `E_paper` is a sum over the *walks* that can leave the strip.  These
    differ: at a corner of the strip a single walk can leave through two
    different mid-edges (e.g. a walk ending at `(-L, y, false)` with
    `x + y = -T` leaves through both `(-L, y, true)` and `(-L, y+1, true)`),
    and such a walk is counted by `B_paper`, not by `E_paper`, while its second
    exit mid-edge still contributes to the boundary sum.

    It is therefore replaced by `finite_strip_identity_rest` below, which keeps
    the `α` and `β` terms exact (those *are* in bijection with `A_paper` and
    `B_paper`) and only records non-negativity of the escape term.  This is all
    that is used downstream, via `B_paper_le_one_from_vr`. -/

/-- **Lemma 2** (Finite Strip Identity), corrected form.
    For the finite strip S_{T,L} with T ≥ 1, L ≥ 1 there is a non-negative
    escape contribution `Erest` with
      `1 = c_α · A_paper + B_paper + Erest`. -/
lemma finite_strip_identity_rest (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    ∃ Erest : ℝ, 0 ≤ Erest ∧
      1 = c_alpha * A_paper T L xc + B_paper T L xc + Erest :=
  strip_identity_nonneg_rest T L hT hL

/-! ## Consequences of the finite strip identity -/

/-- B_paper(T,L,xc) ≤ 1 follows immediately from the strip identity. -/
lemma B_paper_le_one_from_vr (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_paper T L xc ≤ 1 := by
  obtain ⟨Erest, hE, h_id⟩ := finite_strip_identity_rest T L hT hL
  have h_A := A_paper_nonneg T L xc xc_pos.le
  have h_ca := c_alpha_pos
  nlinarith

/-! ## Summary

This file provides:
1. `vertex_relation_at_interior` — PROVED (from fresh_vertex_relation)
2. `finite_strip_identity_rest` — PROVED from `strip_identity_nonneg_rest`
   in `SAWStripBoundarySum.lean`
3. `B_paper_le_one_from_vr` — PROVED from #2

The discrete Stokes summation itself is now proved
(`SAWStokesSum.lean`, `SAWStripBoundarySum.lean`).  What remains are the
four boundary-evaluation lemmas `bdry_A_eval`, `bdry_B_eval`,
`bdry_E_re_nonneg`, `bdry_start_eval` of `SAWStripBoundarySum.lean`.

### Connection to the main theorem

SAWDiagProof imports this file and uses `B_paper_le_one_from_vr`
instead of `B_paper_le_one_strip`, connecting the vertex relation
chain to the bridge partition bounds.
-/

end
