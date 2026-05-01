/-
# Vertex relation analysis for the parafermionic observable (Lemma 1)

This file documents the key mathematical insights for proving the vertex
relation (Lemma 1 of Duminil-Copin & Smirnov 2012), which is the core
ingredient for proving B_paper ≤ 1 (the strip identity).

## Key insight: Only triplet cancellation needed at interior vertices

At an interior vertex v (where all three neighbors are inside the domain),
a self-avoiding walk can visit at most 2 of v's 3 mid-edges:
- Entry mid-edge: the edge through which the walk enters v
- Exit mid-edge: the edge through which the walk exits v

The third mid-edge is NOT visited because:
1. A SAW visits each vertex at most once.
2. To use all 3 edges of v, the walk would need to enter v, exit, and
   re-enter v — which violates self-avoidance.

Therefore, the walk classification at interior vertices is:
- **1 mid-edge visited**: walk approaches v's mid-edge from outside, v ∉ walk.
  Both extensions through v exist (adding v to the walk is valid since v ∉ walk,
  and mid-edge extensions only visit v, not the far vertex).
- **2 mid-edges visited**: walk passes through v (enter + exit).
  This is the extension of a 1-mid-edge walk.
- **3 mid-edges visited**: IMPOSSIBLE at interior vertices.

This means only **triplet cancellation** is needed (no pair cancellation
at interior vertices).

## Winding formula for simply connected domains

For a SAW γ in a simply connected hex lattice domain from mid-edge a to
mid-edge z, the winding (total rotation) telescopes:

  W_γ(a,z) = θ_exit(z) - θ_entry(a)

This follows from the fundamental theorem for plane curves: the total
turning angle of a non-self-intersecting polygonal path equals the
net direction change.

Since the hex lattice is planar and the strip domain is simply connected
(homeomorphic to the plane), SAWs have trivial winding number, and the
winding depends only on the entry and exit directions.

## Consequence for boundary evaluation

With the winding formula, the phase factor exp(-iσW) depends only on
the exit direction of the boundary mid-edge:

- Right boundary (exit direction 0): exp(0) = 1 → weight is B_paper
- Left boundary (exit direction π): exp(-i5π/8) → real part is c_alpha
- Starting mid-edge (trivial walk): weight 1, direction -1 → contributes -1

The boundary sum being zero gives: 1 = c_alpha · A + B_paper.

## References

- pair_cancellation: j * conj(λ)^4 + conj(j) * λ^4 = 0
- triplet_cancellation: 1 + xc * j * conj(λ) + xc * conj(j) * λ = 0
- discrete_stokes_abstract: abstract discrete Stokes theorem
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

-- Verify key identities are available
#check @pair_cancellation   -- j * conj lam ^ 4 + conj j * lam ^ 4 = 0
#check @triplet_cancellation -- 1 + ↑xc * j * conj lam + ↑xc * conj j * lam = 0
