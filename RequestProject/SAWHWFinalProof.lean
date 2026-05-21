/-
# Hammersley-Welsh Bridge Decomposition: Final Proof

The key inequality for the upper bound μ ≤ √(2+√2).

## Proof strategy (from Duminil-Copin-Smirnov 2012 §3)

The paper proves this following Hammersley-Welsh (1962):

1. **Half-plane walk decomposition** (by induction on width T₀):
   Given a half-plane SAW γ̃ (start has extremal projected coordinate):
   - Find the LAST vertex at max projected coordinate, after n steps.
   - The first n vertices form a bridge of width T₀ (prolonged to the
     mid-edge past the last vertex).
   - "We forget about the (n+1)-th vertex, since there is no ambiguity
     in its position." This forgotten vertex starts the remainder.
   - The remaining steps form a half-plane walk of width T₁ < T₀.
   - By induction: the walk decomposes into bridges of widths T₀ > ⋯ > Tⱼ.
   - The forgotten vertex convention ensures the width STRICTLY decreases.

2. **General SAW decomposition**:
   Cut the SAW at the first vertex of maximal projected coordinate.
   The left part (reversed) and right part are half-plane walks.
   Decompose each into bridges with strictly decreasing widths.

3. **Injectivity**: Given the starting mid-edge and first vertex, the
   decomposition uniquely determines the walk (reverse procedure).

4. **Weight bound**: The total bridge length ≤ walk length (the
   forgotten vertices add length not counted in bridges, and for x ≤ 1
   this means x^{walk_length} ≤ x^{bridge_lengths}).

5. **Factor 2**: Two choices for the first vertex from the starting
   mid-edge (one TRUE, one FALSE in the hex lattice).

## Key infrastructure available

- `max_dc_is_true'`: max diagCoord achieved by TRUE vertex
- `bridge_satisfies_paper_inf_strip`: bridges satisfy PaperInfStrip
- `hexFlip`, `hexShift`: lattice automorphisms for translation/reflection
- `hexReScaled_adj_ne`: hexReScaled strictly changes at every step
- `prefix_to_first_min_is_bridge`: bridge extraction from walks
- `first_min_dc_is_false`: first vertex at min dc is FALSE

## What remains to formalize

The main gap is the recursive bridge extraction algorithm with the
"forgotten vertex" convention, and the proof that the map from SAWs
to bridge sequences is injective. This requires:
1. Defining the decomposition function (recursive, using hexReScaled)
2. Proving it produces valid PaperBridges (using existing structural lemmas)
3. Proving the width strictly decreases at each step
4. Proving injectivity (the reverse procedure)
5. Deriving the counting inequality
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- The Hammersley-Welsh bridge decomposition inequality.

    **Status**: sorry. This is the core combinatorial gap.
    See the module docstring for the proof strategy and remaining steps. -/
theorem hw_injection_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∏ T ∈ Finset.range N, (1 + paper_bridge_partition (T + 1) x)) ^ 2 := by
  sorry

/-- Main theorem: paper_bridge_decomp_injection expressed with powerset sum. -/
theorem hw_bridge_decomp_proved {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  have h1 : x ≤ 1 := le_of_lt (lt_trans hxc xc_lt_one)
  have h2 := hw_injection_bound hx h1 N
  simp only [Finset.prod_one_add] at h2
  exact h2

end
