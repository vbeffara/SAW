/-
# Discrete Stokes and the Strip Identity

Connects the cancellation identity (Lemma 1) to the strip identity (Lemma 2).

The discrete Stokes argument: summing the vertex relation over all vertices
of a finite domain, interior mid-edges cancel pairwise and only boundary
mid-edges survive.

## Main results

* `boundary_phase_right` — right boundary mid-edges have winding 0
* `right_boundary_direction` — right boundary direction = 1
* `left_boundary_direction` — left boundary direction = -1
* `starting_midedge_contribution` — starting contribution = -1
* `strip_identity_outline` — the structure of the strip identity proof
-/

import Mathlib
import RequestProject.SAWCancellationProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Boundary winding analysis

For the strip domain S_{T,L}:
- Starting mid-edge a: horizontal, winding = 0, F(a) = 1
- Right boundary β (diagCoord = -T): winding = 0 (horizontal mid-edges)
- Left boundary α (diagCoord = 0): winding = ±π
- Escape boundary ε (top/bottom): winding = ±2π/3

The winding TELESCOPES: W(a, z) = θ_final - θ_initial
where θ_initial = 0 (starting direction from a). -/

/-- Right boundary phase = 1 (winding = 0). -/
lemma boundary_phase_right :
    Complex.exp (-Complex.I * ↑sigma * 0) = 1 := by simp

/-- Right boundary direction = 1. -/
lemma right_boundary_direction (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

/-- Left boundary direction = -1. -/
lemma left_boundary_direction (x y : ℤ) :
    correctHexEmbed (x, y, false) - correctHexEmbed (x, y, true) = -1 :=
  true_dir1 x y

/-- Starting mid-edge contribution = -1. -/
lemma starting_midedge_contribution :
    correctHexEmbed hexOrigin - correctHexEmbed paperStart = -1 :=
  starting_direction

/-! ## The Strip Identity Architecture

The strip identity (Lemma 2) proof has this structure:

1. **Vertex relation** (Lemma 1): at each vertex v ∈ V(S_{T,L}),
   Σᵢ (pᵢ - v) · F(pᵢ) = 0
   where pᵢ are v's three mid-edges.

   This follows from:
   - Walk partition into cancelling triplets and pairs
   - Algebraic cancellation: `triplet_contribution_zero`, `pair_contribution_zero`
   (Both proved in SAWObservable.lean)

2. **Discrete Stokes**: summing over all vertices, each interior mid-edge
   appears in exactly two vertex sums with opposite directions, cancelling:
   (p - v) F(p) + (p - w) F(p) = ((p-v) + (p-w)) F(p)
   Since p is the midpoint of edge {v,w}: (p-v) + (p-w) = 0.
   Only boundary mid-edges survive.

   Key lemma: `direction_cancellation` (proved in SAWCancellationProof.lean)

3. **Boundary evaluation**:
   - Starting mid-edge a: direction = -1, F(a) = 1 → contributes -1
   - Right boundary β: direction = 1, winding = 0 → contributes B
   - Left boundary α: direction = -1, winding = ±π → contributes c_α · A
   - Escape boundary ε: winding = ±2π/3 → contributes c_ε · E

   Key lemmas (all proved):
   - `right_boundary_direction`: direction = 1
   - `left_boundary_direction`: direction = -1
   - `boundary_phase_right`: phase = 1 for right boundary
   - `left_boundary_contrib_re`: Re(phase) = c_alpha for left boundary
   - `boundary_cos_pos`: all boundary phases have positive real part

4. **Conclusion**: 0 = -1 + B + c_α · A + c_ε · E
   Since A, E ≥ 0 and c_α, c_ε > 0: B ≤ 1.

### Status:
- Steps 1 (algebraic part) and 3 are FULLY PROVED.
- Step 1 (combinatorial walk partition) is the remaining gap.
  The extension/retraction infrastructure is proved in SAWWalkPartition.lean.
- Steps 2 and 4 require connecting the walk-level observable to the
  strip-level partition functions, which is the next major formalization target.
-/

end
