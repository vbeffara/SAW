/-
# Parafermionic Observable Infrastructure

Direction vector computations and boundary analysis for the
parafermionic observable proof (Lemma 2 of Duminil-Copin & Smirnov 2012).

This file provides additional infrastructure for the discrete Stokes
argument that will eventually prove B_paper(T,L,xc) ≤ 1.

## Key facts proved here

1. Direction vectors: hexDir(v,w) = embed(w) - embed(v)
2. Direction negation: hexDir(w,v) = -hexDir(v,w)
3. Right boundary direction: +1 (FALSE→TRUE at diagCoord = -T)
4. Left boundary direction: -1 (TRUE→FALSE at diagCoord = 0)
5. Starting mid-edge direction: -1 (paperStart→hexOrigin)

## What's still needed for the full proof

The discrete Stokes argument requires:
1. Defining the observable F(z) at mid-edges (complex-valued)
2. The vertex relation: ∑_{w~v} D(v,w)·F(mid(v,w)) = 0 at each vertex
   (follows from pair_cancellation + triplet_cancellation)
3. Telescoping: interior mid-edges cancel when summing over vertices
4. Boundary evaluation: winding computation for each boundary type
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Direction vectors on hexGraph -/

/-- Direction vector of a hexGraph edge. -/
def hexDir (v w : HexVertex) : ℂ :=
  correctHexEmbed w - correctHexEmbed v

/-- Direction from TRUE(x,y) to FALSE(x,y) is -1. -/
lemma hexDir_tt_ff (x y : ℤ) :
    hexDir (x, y, true) (x, y, false) = -1 := by
  simp [hexDir, correctHexEmbed, Complex.ext_iff]

/-- Direction from FALSE(x,y) to TRUE(x,y) is +1. -/
lemma hexDir_ff_tt (x y : ℤ) :
    hexDir (x, y, false) (x, y, true) = 1 := by
  simp [hexDir, correctHexEmbed, Complex.ext_iff]

/-- Direction from paperStart to hexOrigin is -1. -/
lemma hexDir_start :
    hexDir paperStart hexOrigin = -1 := by
  unfold paperStart hexOrigin
  exact hexDir_tt_ff 0 0

/-- For any pair of vertices, the opposite direction is the negative. -/
lemma hexDir_neg (v w : HexVertex) :
    hexDir w v = -hexDir v w := by
  unfold hexDir; ring

/-! ## Boundary directions

The boundary of the strip PaperFinStrip T L consists of:
1. Starting mid-edge: paperStart → hexOrigin (direction -1)
2. Left boundary (α\{a}): TRUE(x,-x) → FALSE(x,-x) (direction -1)
3. Right boundary (β): FALSE(x,y) → TRUE(x,y) at d=-T (direction +1)
4. Escape boundary (ε∪ε̄): various diagonal directions
-/

/-- Right boundary edges have direction +1. -/
lemma right_boundary_hexDir (x y : ℤ) :
    hexDir (x, y, false) (x, y, true) = 1 :=
  hexDir_ff_tt x y

/-- Left boundary edges have direction -1. -/
lemma left_boundary_hexDir (x y : ℤ) :
    hexDir (x, y, true) (x, y, false) = -1 :=
  hexDir_tt_ff x y

/-! ## Discrete Stokes: key cancellation

The core of the discrete Stokes argument is that for any interior edge
{u,v} of the strip (both u,v ∈ V), the contributions from u and v cancel:

  D(u,v) · f + D(v,u) · f = 0

because D(v,u) = -D(u,v). This is used to show that the sum of vertex
relations over all vertices telescopes to boundary terms. -/

/-- Interior edge cancellation: opposite directions sum to zero. -/
lemma interior_edge_cancellation (v w : HexVertex) (f : ℂ) :
    hexDir v w * f + hexDir w v * f = 0 := by
  rw [hexDir_neg]; ring

end
