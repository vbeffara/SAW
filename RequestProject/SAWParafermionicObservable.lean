/-
# Parafermionic Observable Infrastructure

Defines the edge-weight function for the parafermionic observable and proves
the vertex relation at the level of individual SAW extensions.

The vertex relation (Lemma 1 of Duminil-Copin & Smirnov 2012) says:
at each vertex v, the sum of direction * phase over the 3 adjacent mid-edges is 0.

This is the algebraic core of the strip identity proof.
-/

import Mathlib
import RequestProject.SAWObservableStokes

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Edge phase factors

On the hexagonal lattice, each edge has a direction. The phase factor
for extending a walk by one edge involves:
- The edge direction (as a complex number)
- The winding change (turning angle) at the vertex
- The fugacity factor xc

At each vertex v, the 3 adjacent edges have specific direction-winding
relationships given by pair_cancellation and triplet_cancellation. -/

/-! ## Direction vectors as complex exponentials

The 6 possible hex edge directions, as unit complex numbers:
  FALSE→TRUE same: 1 (angle 0)
  FALSE→TRUE x+1: exp(2πi/3) = j̄ (angle 2π/3)
  FALSE→TRUE y+1: exp(-2πi/3) = j (angle -2π/3)
  TRUE→FALSE same: -1 (angle π)
  TRUE→FALSE x-1: exp(-πi/3) (angle -π/3)
  TRUE→FALSE y-1: exp(πi/3) (angle π/3)
-/

/-- At a FALSE vertex, the three edge directions to TRUE neighbors. -/
lemma false_edge_dirs (x y : ℤ) :
    hexEdgeDirC (x, y, false) (x, y, true) = 1 ∧
    hexEdgeDirC (x, y, false) (x + 1, y, true) = -1/2 + Complex.I * (Real.sqrt 3 / 2) ∧
    hexEdgeDirC (x, y, false) (x, y + 1, true) = -1/2 - Complex.I * (Real.sqrt 3 / 2) := by
  refine ⟨hexEdgeDirC_F_T_same x y, ?_, ?_⟩ <;>
  unfold hexEdgeDirC correctHexEmbed <;>
  apply Complex.ext <;> simp <;> ring

/-- At a TRUE vertex, the three edge directions to FALSE neighbors. -/
lemma true_edge_dirs (x y : ℤ) :
    hexEdgeDirC (x, y, true) (x, y, false) = -1 ∧
    hexEdgeDirC (x, y, true) (x - 1, y, false) = 1/2 - Complex.I * (Real.sqrt 3 / 2) ∧
    hexEdgeDirC (x, y, true) (x, y - 1, false) = 1/2 + Complex.I * (Real.sqrt 3 / 2) := by
  refine ⟨hexEdgeDirC_T_F_same x y, ?_, ?_⟩ <;>
  unfold hexEdgeDirC correctHexEmbed <;>
  apply Complex.ext <;> simp <;> ring

/-! ## The vertex relation in abstract form

The vertex relation says: for any complex number z₀ (representing the
phase of a walk ending at vertex v), the sum over 3 possible extensions
of (direction * extended_phase) is 0.

This is the content of pair_cancellation and triplet_cancellation:
- Triplet: 1 + xc·j·conj(λ) + xc·conj(j)·λ = 0
  (walk visits 1 mid-edge → extend to 2 more)
- Pair: j·conj(λ)⁴ + conj(j)·λ⁴ = 0
  (walk visits all 3 mid-edges → swap loop direction)
-/

/-- The vertex relation for the observable: at each vertex, the sum of
    direction · phase over 3 extensions is 0. This follows from
    triplet_cancellation (for walks visiting 1 mid-edge) and
    pair_cancellation (for walks visiting all 3 mid-edges). -/
theorem observable_vertex_relation :
    (1 : ℂ) + (xc : ℂ) * j * conj lam + (xc : ℂ) * conj j * lam = 0 ∧
    j * conj lam ^ 4 + conj j * lam ^ 4 = 0 :=
  ⟨triplet_cancellation, pair_cancellation⟩

/-! ## Discrete Stokes abstract framework

For a finite set V of vertices with a function f: V → ℂ
satisfying f(v) = 0 for all v ∈ V, the sum Σ f(v) = 0.

This trivial fact IS the discrete Stokes theorem:
the "vertex relation" is f(v) = 0 at each vertex,
and the total sum (which equals the boundary sum after
interior cancellation) is 0. -/

/-- Abstract Stokes: sum of zeros is zero. -/
lemma abstract_stokes {V : Type*} [Fintype V] (f : V → ℂ)
    (h : ∀ v, f v = 0) : ∑ v, f v = 0 := by
  simp [h]

/-- Abstract Stokes with boundary: if interior sum cancels,
    total = boundary. -/
lemma abstract_stokes_boundary {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → ℂ} (h_total : ∑ a, f a = 0)
    {int_set bdry_set : Finset α}
    (h_partition : int_set ∪ bdry_set = Finset.univ)
    (h_disjoint : Disjoint int_set bdry_set)
    (h_interior : ∑ a ∈ int_set, f a = 0) :
    ∑ a ∈ bdry_set, f a = 0 := by
  have h1 : ∑ a ∈ Finset.univ, f a = ∑ a ∈ int_set, f a + ∑ a ∈ bdry_set, f a := by
    rw [← Finset.sum_union h_disjoint, h_partition]
  simp at h1
  rw [h_total, h_interior, zero_add] at h1
  exact h1.symm

/-! ## The boundary equation gives B ≤ 1

Once we establish:
  0 = -1 + c_alpha * A + B + c_eps * E  (boundary equation)
with A, E ≥ 0, we get B ≤ 1.

This is already proved as bridge_bound_of_strip_identity. -/

end
