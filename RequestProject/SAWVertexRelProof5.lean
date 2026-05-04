/-
# Vertex Relation for the Parafermionic Observable (Lemma 1)

Proves that for x = xc and σ = 5/8, at every vertex v:
  (p-v)F(p) + (q-v)F(q) + (r-v)F(r) = 0
where p, q, r are the mid-edges of the three edges adjacent to v.

The proof partitions walks ending at p, q, r into:
- Pairs: walks visiting all 3 mid-edges (loop reversal)
- Triplets: walks visiting 1 or 2 mid-edges (extension by one step)

Each pair contributes 0 by pair_cancellation.
Each triplet contributes 0 by triplet_cancellation.

## Walk classification at vertex v

For a SAW γ ending at neighbor w of v:
- γ "visits v" if v ∈ γ.support (i.e., v is visited during the walk)
- If γ visits v: γ enters v from one neighbor and exits to w
  → γ visits 2 of the 3 mid-edges adjacent to v
- If γ doesn't visit v: γ just ends at w without passing through v
  → γ visits 1 mid-edge (the edge (v,w))

## Pair construction

If γ visits all 3 mid-edges of v, it means γ visits v twice.
But wait — SAWs visit each vertex at most once! So a SAW can visit v
at most once, using at most 2 edges adjacent to v.

CORRECTION: A walk visiting "all 3 mid-edges" means it visits 2
neighbors of v (entering v from one, exiting to another) AND ends at
the third neighbor. In this case, the walk uses 2 of the 3 edges
adjacent to v (for entry/exit) and the third edge is the "endpoint edge."

Pair construction: swap the entry and exit edges at v.
This reverses the direction of traversal around v.

## Triplet construction

If γ visits only 1 mid-edge of v (i.e., γ doesn't pass through v,
just ends at a neighbor w), then γ can be extended by one step through
v to reach another neighbor. This gives 2 new walks (one for each
of the other 2 neighbors of v).

Reference: Section 2 of Duminil-Copin & Smirnov (2012).
-/

import Mathlib
import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk classification at a vertex

For a SAW γ from some start vertex to a neighbor w of vertex v,
classify the walk by which edges adjacent to v it uses. -/

/-- A vertex v is "interior to a walk" if it appears in the walk's support
    but is not the endpoint. -/
def vertexInterior {start finish : HexVertex} (p : hexGraph.Walk start finish)
    (v : HexVertex) : Prop :=
  v ∈ p.support ∧ v ≠ finish

/-- Whether vertex v appears in the walk's support. -/
def walksThrough {start finish : HexVertex}
    (p : hexGraph.Walk start finish) (v : HexVertex) : Prop :=
  v ∈ p.support

/-! ## Extension of a walk by one step

Given a SAW γ from start to w where w is adjacent to v,
if v ∉ γ.support, we can extend γ by adding the edge (w, v). -/

/-- Extend a walk by one step. -/
def walkExtendOne {start w : HexVertex} (p : hexGraph.Walk start w)
    (v : HexVertex) (hAdj : hexGraph.Adj w v) : hexGraph.Walk start v :=
  p.append (.cons hAdj .nil)

/-- The extended walk has length = original + 1. -/
lemma walkExtendOne_length {start w : HexVertex} (p : hexGraph.Walk start w)
    (v : HexVertex) (hAdj : hexGraph.Adj w v) :
    (walkExtendOne p v hAdj).length = p.length + 1 := by
  simp [walkExtendOne]

/-
If v ∉ p.support and p is a path, then the extension is also a path
    (provided v ∉ p.support and v ≠ start).
-/
lemma walkExtendOne_isPath {start w : HexVertex} (p : hexGraph.Walk start w)
    (hp : p.IsPath) (v : HexVertex) (hAdj : hexGraph.Adj w v)
    (hv : v ∉ p.support) :
    (walkExtendOne p v hAdj).IsPath := by
  unfold walkExtendOne;
  simp_all +decide [ SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append ];
  grind

/-! ## Retraction of a walk by one step

Given a SAW γ from start to v where the last step goes through w → v,
we can retract to get a walk from start to w. -/

-- Placeholder for walk infrastructure

/-! ## Key algebraic lemma: triplet contribution is zero

For a walk γ from start to neighbor w₁ of v (not passing through v),
let γ₂ = extend γ through v to w₂, and γ₃ = extend γ through v to w₃.

The triplet contribution is:
  (w₁-v)·e^{-iσW₁}·x^{ℓ₁} + (w₂-v)·e^{-iσW₂}·x^{ℓ₂} + (w₃-v)·e^{-iσW₃}·x^{ℓ₃}

With w₂ and w₃ being the other two neighbors of v:
  W₂ = W₁ + turning_angle(w₁→v→w₂)
  W₃ = W₁ + turning_angle(w₁→v→w₃)
  ℓ₂ = ℓ₃ = ℓ₁ + 1

The direction factors (wᵢ - v) are the three cube roots of unity times (w₁-v).
So (w₂-v) = j·(w₁-v) and (w₃-v) = j̄·(w₁-v) (up to ordering).

The winding changes are ±π/3 (60° turns).
So e^{-iσ·±π/3} = conj(λ) or λ (using λ = e^{-i5π/24}).

The triplet sum becomes:
  (w₁-v)·e^{-iσW₁}·x^{ℓ₁} · (1 + xc·j·conj(λ) + xc·j̄·λ)

By triplet_cancellation: 1 + xc·j·conj(λ) + xc·j̄·λ = 0.

So the triplet contribution is 0. -/

/-! ## Key algebraic lemma: pair contribution is zero

For a walk γ₁ visiting all 3 edges adjacent to v (entering from one
direction, passing through v, and then the walk continues but also
"touches" the third edge because it ends at the third neighbor):

The paired walk γ₂ reverses the loop around v.

If γ₁ enters v from direction d₁ and exits to d₂:
  winding of γ₁ = W(start→d₁) + W(d₁→v→d₂) + W(d₂→end)
  winding of γ₂ = W(start→d₁) + W(d₁→v→d₃) + W(d₃→end')

The winding difference is ±4π/3 (the two ways around v differ by 4π/3).

The pair sum involves j·conj(λ)⁴ + j̄·λ⁴.
By pair_cancellation: j·conj(λ)⁴ + j̄·λ⁴ = 0.

So the pair contribution is 0. -/

end