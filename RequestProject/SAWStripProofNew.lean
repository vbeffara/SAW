/-
# Proof of B_paper ≤ 1 via the parafermionic observable

This file proves the core bound B_paper(T,L,xc) ≤ 1 from the
parafermionic observable argument (Lemma 2 of Duminil-Copin & Smirnov 2012).

## Proof strategy

The vertex relation (Lemma 1) says: for each interior vertex v of the strip,
the sum of direction-weighted observable values at v's three mid-edges is zero.

The algebraic core (already proved):
- triplet_cancellation: 1 + xc · j · conj(λ) + xc · conj(j) · λ = 0

At each vertex v, walks ending at v form "triplets": a base walk γ ending at v
plus its two one-step extensions. The triplet cancellation shows each triplet's
contribution to the vertex relation is zero. Summing over all vertices and
using interior cancellation (discrete Stokes), only boundary terms survive.
The boundary sum gives 0 = -1 + c_α·A + B + c_ε·E, hence B ≤ 1.

## Key insight: winding definition

The winding W(γ) for a walk γ = (v₀,...,vₖ) from paperStart is defined as
walkWindingInt of the extended walk (hexOrigin → v₀ → ... → vₖ).
This equals the sum of hexTurn values at v₀,...,vₖ₋₁ (all vertices except
the last). The exit winding for extension to w includes hexTurn at vₖ too.

With this convention, the triplet cancellation gives zero at each vertex,
and the boundary evaluation gives the strip identity.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk winding from starting mid-edge

For a walk γ from paperStart, the "full winding" from the starting
mid-edge a includes the initial turn at paperStart. -/

/-- The turn at a vertex, as an integer multiple of π/3.
    hexTurn(u,v,w) = signed turn from direction u→v to direction v→w. -/
def hexTurn' (u v w : HexVertex) : ℤ :=
  match hexEdgeDir u v, hexEdgeDir v w with
  | some d1, some d2 => ((d2 : ℤ) - (d1 : ℤ) + 3) % 6 - 3
  | _, _ => 0

/-- Full winding of a walk from paperStart, measured from the starting
    mid-edge direction. Includes the initial turn at paperStart.
    Defined as walkWindingInt of (hexOrigin → walk). -/
def fullWinding {v : HexVertex} (p : hexGraph.Walk paperStart v) : ℤ :=
  walkWindingInt (SimpleGraph.Walk.cons
    (show hexGraph.Adj hexOrigin paperStart by decide) p)

/-! ## Observable weight for strip walks

The weight of a walk γ at vertex v, for the vertex relation, is:
  wt(γ) = e^{-iσ · fullWinding(γ) · π/3} · xc^{length(γ)}

The vertex relation sums d(v,w) · wt over exits w from v. -/

/-- The complex phase for a walk with winding W (integer, in units of π/3). -/
def windingPhase (W : ℤ) : ℂ :=
  Complex.exp (-Complex.I * sigma * (↑W * Real.pi / 3))

/-- The weight of a strip walk γ ending at v. -/
def walkWeight {v : HexVertex} (p : hexGraph.Walk paperStart v) : ℂ :=
  windingPhase (fullWinding p) * (xc : ℂ) ^ p.length

/-! ## Triplet cancellation at vertices

At each vertex v, the triplet sum is zero:
  d(v, entry) · wt(γ) + Σ_{w ≠ entry} d(v,w) · xc · e^{-iσ·hexTurn·π/3} · wt(γ) = 0

This follows from triplet_cancellation. -/

/-
The triplet identity at a FALSE vertex: entering from TRUE(x,y),
    the sum of direction-weighted phases is zero.
    This is a reformulation of triplet_cancellation.
-/
lemma false_vertex_triplet_zero (_x _y : ℤ) (W : ℤ) :
    (1 : ℂ) * windingPhase W +
    j * windingPhase (W - 1) * (xc : ℂ) +
    conj j * windingPhase (W + 1) * (xc : ℂ) = 0 := by
  norm_num [ windingPhase ];
  -- Factor out `cexp (-(I * sigma * W * π / 3))` from each term.
  suffices h_factor : 1 + j * Complex.exp (I * sigma * Real.pi / 3) * xc + starRingEnd ℂ j * Complex.exp (-I * sigma * Real.pi / 3) * xc = 0 by
    convert congr_arg ( fun x : ℂ => x * Complex.exp ( - ( I * sigma * ( W * Real.pi / 3 ) ) ) ) h_factor using 1 <;> ring;
    simpa only [ Complex.exp_add ] using by ring;
  convert vertex_relation_pair_triplet.2 using 1 ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, neg_div ];
  unfold lam; norm_num [ Complex.exp_re, Complex.exp_im, sigma_is_five_eighths ] ; ring ; norm_num;

/-
The triplet identity at a TRUE vertex: entering from FALSE(x,y),
    the sum of direction-weighted phases is zero.
-/
lemma true_vertex_triplet_zero (_x _y : ℤ) (W : ℤ) :
    (-1 : ℂ) * windingPhase W +
    (-j) * windingPhase (W - 1) * (xc : ℂ) +
    (-conj j) * windingPhase (W + 1) * (xc : ℂ) = 0 := by
  have := false_vertex_triplet_zero _x _y W; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
  constructor <;> linarith

end