/-
# Bridge Decomposition of Self-Avoiding Walks (Hammersley-Welsh)

Formalization of the canonical bridge decomposition from Section 3 of:
  Duminil-Copin, H. and Smirnov, S., "The connective constant of the
  honeycomb lattice equals √(2+√2)", Annals of Mathematics, 2012.

The key result: any SAW can be canonically decomposed into bridges of
strictly decreasing widths. This gives the upper bound Z(x) < ∞ for x < xc.

## Proof outline

1. Define the diagonal coordinate d(v) = v.1 + v.2.1.
2. For any SAW γ, find the "deepest vertex" (minimum d, first occurrence).
3. Split γ at the deepest vertex into two half-plane walks.
4. Each half-plane walk decomposes into bridges of strictly decreasing widths.
5. The decomposition is injective (given the starting vertex choice).
6. For x ≤ 1, the walk weight x^n ≤ product of bridge weights.
7. Summing gives Z_N(x) ≤ 2 · (Π(1 + B_T(x)))².
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Diagonal coordinate -/

/-- The diagonal coordinate d(v) = v.1 + v.2.1 for a HexVertex. -/
def diagCoord (v : HexVertex) : ℤ := v.1 + v.2.1

@[simp] lemma diagCoord_paperStart : diagCoord paperStart = 0 := by
  simp [diagCoord, paperStart]

/-- Each hex edge changes diagCoord by 0 or ±1. -/
lemma diagCoord_adj_le {v w : HexVertex} (h : hexGraph.Adj v w) :
    diagCoord w ≤ diagCoord v + 1 ∧ diagCoord v - 1 ≤ diagCoord w := by
  unfold diagCoord hexGraph at *
  rcases h with ⟨_, _, h3 | h3 | h3⟩ | ⟨_, _, h3 | h3 | h3⟩ <;>
    simp_all <;> constructor <;> omega

/-! ## Half-plane walks and bridge width -/

/-- A walk is "half-plane" if its start achieves the minimum diagCoord. -/
def Walk.isHalfPlane {v w : HexVertex} (p : hexGraph.Walk v w) : Prop :=
  ∀ u ∈ p.support, diagCoord v ≤ diagCoord u

/-! ## Powerset product identity -/

/-- The standard identity: Π (1 + f(i)) = Σ_{S ⊆ range n} Π_{i ∈ S} f(i). -/
lemma powerset_prod_eq {n : ℕ} (f : ℕ → ℝ) :
    ∏ i ∈ Finset.range n, (1 + f i) =
    ∑ S ∈ (Finset.range n).powerset, ∏ i ∈ S, f i := by
  rw [Finset.prod_one_add]

/-! ## The Hammersley-Welsh injection

The core mathematical argument, stated as a single theorem.
The proof decomposes each SAW into bridges:

1. **Split at deepest point**: Find the first vertex with minimum
   diagonal coordinate. Split the walk there.

2. **Half-plane decomposition**: Each half is a half-plane walk.
   For a half-plane walk of width T₀:
   - Find the last vertex with maximum diagCoord.
   - The prefix is a bridge of width T₀.
   - The suffix (after forgetting one vertex) is a half-plane walk
     of width T₁ < T₀.
   - Recurse.

3. **Injectivity**: Given the starting vertex and the sequence of
   bridge widths, the walk can be uniquely reconstructed.

4. **Weight bound**: For x ≤ 1, connecting vertices only reduce
   the weight: x^n ≤ Π x^{bridge_lengths}.

5. **Counting**: The factor of 2 accounts for two starting vertex
   choices. Each half gives a subset of {1,...,N}. The total bound
   is 2 · (Σ_{S} Π_{T∈S} B_T)² = 2 · (Π (1+B_T))².
-/

theorem paper_bridge_decomp_injection_v2 {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end
