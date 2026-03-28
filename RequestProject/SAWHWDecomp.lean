/-
# Hammersley-Welsh Bridge Decomposition Algorithm

Formalization of the bridge decomposition algorithm from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The algorithm decomposes any self-avoiding walk into a sequence of bridges
with monotone widths. This gives an injection from SAWs to pairs of bridge
selections, yielding the key counting inequality for the upper bound.

## Key steps

1. Half-plane walk decomposition (induction on width)
2. General SAW decomposition (split at first max-x vertex)
3. Injectivity of the decomposition
4. Weight accounting (walk length ≥ sum of bridge lengths)
5. The counting inequality

## Status

The counting inequality `bridge_decomposition_injection_proof` is sorry'd.
It requires formalizing the full bridge decomposition algorithm.
-/

import Mathlib
import RequestProject.SAWHWInject

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Walk utilities -/

/-- The x-coordinate of a walk's endpoint is bounded by the walk length
    when starting from x = 0. -/
lemma walk_endpoint_x_le_length {v w : HexVertex} (p : hexGraph.Walk v w)
    (hv : v.1 = 0) : w.1 ≤ p.length := by
  have := (hexGraph_walk_bound p).1
  omega

/-- Each step in hexGraph changes x-coordinate by at most 1. -/
lemma hexGraph_adj_x_diff {v w : HexVertex} (h : hexGraph.Adj v w) :
    |w.1 - v.1| ≤ 1 := by
  have ⟨h1, h2, _, _⟩ := hexGraph_adj_bound h
  exact abs_le.mpr ⟨by omega, by omega⟩

/-! ## Bridge data -/

/-- A walk prefix from v to u that forms a bridge of width T. -/
structure WalkBridgeData (T : ℕ) where
  start_v : HexVertex
  end_v : HexVertex
  path : hexGraph.Path start_v end_v
  start_zero : start_v.1 = 0
  end_at_T : end_v.1 = (T : ℤ)
  all_in_range : ∀ u ∈ path.1.support, 0 ≤ u.1 ∧ u.1 ≤ (T : ℤ)

/-- Convert a WalkBridgeData to a Bridge. -/
def WalkBridgeData.toBridge (d : WalkBridgeData T) : Bridge T where
  start_v := d.start_v
  end_v := d.end_v
  walk := d.path
  start_left := d.start_zero
  end_right := by exact_mod_cast d.end_at_T
  in_strip := fun v hv => d.all_in_range v hv

/-! ## Half-plane walk decomposition

A half-plane walk is a SAW where the start has minimal x-coordinate.
The decomposition finds the last vertex with maximal x, extracts a bridge,
and recurses on the remainder (which has strictly smaller width). -/

/-- For a half-plane walk starting from hexOrigin, every vertex
    has non-negative x-coordinate. -/
lemma halfplane_nonneg_x {w : HexVertex} (p : hexGraph.Path hexOrigin w)
    (hp : ∀ v ∈ p.1.support, hexOrigin.1 ≤ v.1)
    (u : HexVertex) (hu : u ∈ p.1.support) : 0 ≤ u.1 := by
  have := hp u hu; simp [hexOrigin] at this; exact this

/-! ## The bridge decomposition counting inequality

This is the main result: the Hammersley-Welsh counting inequality.

  ∑_{n≤N} c_n x^n ≤ 2 × (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}^x)²

The proof requires formalizing the full bridge decomposition algorithm
(half-plane walk induction on width, general walk splitting at first max-x
vertex, reverse procedure establishing injectivity, weight accounting).

The factor 2 accounts for the two choices of first vertex from the starting
mid-edge.

**Status: sorry.** This is the key remaining combinatorial gap. -/
theorem bridge_decomposition_injection_proof {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, origin_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end
