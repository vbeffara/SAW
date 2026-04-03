/-
# Parafermionic observable and vertex relation for the strip identity

This file builds the infrastructure needed for proving B_paper ≤ 1
via the parafermionic observable argument.

The key idea: define a complex-valued "weight" for each SAW in the strip,
and show that the total weighted sum vanishes. This gives B_paper ≤ 1
after taking real parts.

## Walk weight definition

For a SAW γ from paperStart to vertex w through the strip, define:
  weight(γ, w_next) = (embed(w_next) - embed(w)) · exp(-i·σ·W(γ)) · xc^(ℓ(γ)+1)

where w_next is a neighbor of w (the "exit direction"), and W(γ) is the
winding of γ. The sum of weights over all walks and all exit directions
can be partitioned into vertex-local sums that vanish by the vertex relation.
-/

import Mathlib
import RequestProject.SAWStripIdentityCorrect

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Walk weight as a product of turn factors

On the hexagonal lattice, each SAW makes turns of ±π/3 at each vertex.
The complex weight exp(-i·σ·W) can be written as a product of λ or conj(λ)
per turn, where λ = exp(-i·5π/24).

The key property: only the RELATIVE angles matter, and on the hex lattice
all angles are multiples of π/3. -/

/-- The six possible edge directions in hexGraph, encoded as the index 0..5
    representing angles 0, π/3, 2π/3, π, -2π/3, -π/3 respectively. -/
def hexEdgeDir (v w : HexVertex) : Option (Fin 6) :=
  if hexGraph.Adj v w then
    -- FALSE → TRUE edges
    if v.2.2 = false then
      if w = (v.1, v.2.1, true) then some 0           -- same cell: angle 0
      else if w = (v.1 + 1, v.2.1, true) then some 2   -- angle 2π/3
      else some 4                                       -- angle -2π/3 (= 4π/3)
    -- TRUE → FALSE edges
    else
      if w = (v.1, v.2.1, false) then some 3           -- same cell: angle π
      else if w = (v.1 - 1, v.2.1, false) then some 5  -- angle -π/3 (= 5π/3)
      else some 1                                       -- angle π/3
  else none

/-! ## Winding as sum of turns

The winding of a walk is the sum of turns at each vertex.
On the hex lattice, each turn is a multiple of π/3.
We track the winding as an integer multiple of π/3. -/

/-- The turn at a vertex: the change in direction (mod 6) from one edge
    to the next. Values in {-2, -1, 0, 1, 2} × (π/3). -/
def hexTurn (u v w : HexVertex) : ℤ :=
  match hexEdgeDir u v, hexEdgeDir v w with
  | some d1, some d2 =>
    let diff := ((d2 : ℤ) - (d1 : ℤ) + 3) % 6 - 3
    diff
  | _, _ => 0

/-- The winding of a walk as an integer multiple of π/3. -/
def walkWindingInt : {v w : HexVertex} → hexGraph.Walk v w → ℤ
  | _, _, .nil => 0
  | _, _, .cons h (.nil) => 0
  | v, _, @SimpleGraph.Walk.cons _ _ _ u _ h (@SimpleGraph.Walk.cons _ _ _ _ w h' rest) =>
    hexTurn v u w + walkWindingInt (.cons h' rest)

/-! ## Observable contribution

For the strip identity, we need the "boundary contribution" which is:
  Σ_{boundary mid-edges z} (direction(z)) · F(z)
where F(z) is the observable at z. -/

/-- The complex direction factor for a hex edge (w-v), embedded in ℂ.
    This is the "direction vector" (p-v) where p is the mid-edge center. -/
def hexComplexDir (v w : HexVertex) : ℂ :=
  correctHexEmbed w - correctHexEmbed v

/-! ## Finiteness of walks in finite strip

PaperFinStrip T L has finitely many vertices, so finitely many SAWs. -/

/-
PaperFinStrip T L has finitely many vertices.
-/
lemma paper_fin_strip_finite (T L : ℕ) :
    Set.Finite {v : HexVertex | PaperFinStrip T L v} := by
  refine' Set.Finite.subset ( Set.finite_Icc ( -T - L - 1 : ℤ ) ( T + L + 1 ) |> Set.Finite.prod <| Set.finite_Icc ( -T - L - 1 : ℤ ) ( T + L + 1 ) |> Set.Finite.prod <| Set.toFinite { true, false } ) _;
  intro v hv
  obtain ⟨hv_inf, hv_fin⟩ := hv;
  unfold PaperInfStrip at hv_inf;
  grind

/-
PaperSAW_B T L is a finite type.
-/
instance paper_saw_b_finite (T L : ℕ) : Finite (PaperSAW_B T L) := by
  -- Since every SAW has length ≤ the number of vertices in the strip, there are finitely many SAWs of bounded length from a fixed starting vertex.
  have h_finite_length : ∃ N, ∀ s : PaperSAW_B T L, s.len ≤ N := by
    -- Since every SAW has length ≤ the number of vertices in the strip, there are finitely many SAWs of bounded length from a fixed starting vertex. Use this fact to find such an N.
    have h_finite_vertices : Set.Finite {v : HexVertex | PaperFinStrip T L v} := by
      exact?;
    use h_finite_vertices.toFinset.card;
    intro s
    have h_support : s.saw.p.1.support.toFinset ⊆ h_finite_vertices.toFinset := by
      exact fun x hx => h_finite_vertices.mem_toFinset.mpr <| s.in_strip x <| by simpa using hx;
    have := Finset.card_le_card h_support;
    rw [ List.toFinset_card_of_nodup ] at this;
    · grind +suggestions;
    · exact s.saw.p.2.support_nodup;
  choose N hN using h_finite_length;
  have h_inj : Function.Injective (fun s : PaperSAW_B T L => ⟨⟨s.len, by linarith [hN s]⟩, s.saw⟩ : PaperSAW_B T L → Σ n : Fin (N + 1), SAW paperStart n) := by
    intro s t h_eq; cases s; cases t; aesop;
  exact Finite.of_injective _ h_inj

/-
B_paper is a finite sum.
-/
lemma B_paper_eq_finsum (T L : ℕ) (x : ℝ) :
    B_paper T L x = ∑ᶠ (s : PaperSAW_B T L), x ^ (s.len + 1) := by
  haveI : Fintype (PaperSAW_B T L) := Fintype.ofFinite (PaperSAW_B T L);
  unfold B_paper;
  rw [ tsum_fintype ];
  rw [ ← finsum_eq_sum_of_fintype ]

end