/-
# Ear-step orientation lemmas (discrete Umlaufsatz preparation)

This file collects small, **fully sorry-free** orientation facts about a single
triangle (an "ear") that the ear-clipping / discrete Gauss–Bonnet induction
toward the discrete Hopf Umlaufsatz core
`hex_signed_turn_eq_six_sign_shoelace` (in
`RequestProject.SAWUmlaufSignedArea`) needs at each clipping step.

Recall the inductive invariant maintained by the ear-clipping induction is

  total signed turn  =  `6 · sign (HexArea.shoelace2 (embedded polygon))`.

When a vertex `b` is cut from between its neighbours `a` and `c`:

* the signed area changes by exactly the **triangle term**
  `cross a b + cross b c + cross c a` (`HexArea.shoelace2_ear`); and
* the total signed turn changes by exactly the **turn sign** at `b`
  (`hexTurnSign`, see `hexSignedTurnCount`).

For the invariant to be preserved these two changes must have the *same sign*.
The lemmas here pin that down at the level of the cut-off triangle:

* `shoelace2_triple_eq_cross` — the signed area of the ear triangle `[a,b,c]`
  equals the edge cross product `cross (b-a) (c-b)`;
* `shoelace2_triple_sign` — hence its orientation (`0 < area`) is exactly the
  orientation of that cross product;
* `hexTurnSign_eq_shoelace2_triple_sign` — the **combinatorial turn sign**
  `hexTurnSign v₀ v₁ v₂` at a genuine hex turn equals the orientation
  `if 0 < shoelace2 [embed v₀, embed v₁, embed v₂] then 1 else -1` of the
  embedded ear triangle.  This is the precise per-vertex compatibility between
  the signed-turn change and the signed-area change that the ear-clipping
  induction consumes.

These are the *algebraic* (per-triangle) half of the ear step; they are
sorry-free.  The remaining genuinely topological content (a simple polygon with
`≥ 4` vertices has an ear, and ear removal preserves planar simplicity) is the
irreducible Jordan-curve-level gap recorded as the single `sorry`
`hex_signed_turn_eq_six_sign_shoelace`.

This file is imported from `RequestProject.SAWUmlaufGaussBonnet` (hence
transitively from `RequestProject.SAWFinal`); it is **preparation** for the
Umlaufsatz and is not yet consumed by another declaration.
-/

import Mathlib
import RequestProject.SAWUmlaufBridge

open Real Complex ComplexConjugate

noncomputable section

/-- The signed area (twice) of the ear triangle `[a, b, c]` equals the cross
    product of its two edge vectors `b-a` and `c-b`.  (Combines
    `HexArea.shoelace2_triple` with `cross_triangle_eq_cross_edges`.) -/
lemma shoelace2_triple_eq_cross (a b c : ℂ) :
    HexArea.shoelace2 [a, b, c] = HexArea.cross (b - a) (c - b) := by
  rw [HexArea.shoelace2_triple, cross_triangle_eq_cross_edges]

/-- The orientation of the ear triangle `[a, b, c]` (the sign of its signed
    area) equals the orientation of the edge cross product `cross (b-a) (c-b)`. -/
lemma shoelace2_triple_sign (a b c : ℂ) :
    (0 < HexArea.shoelace2 [a, b, c]) ↔ (0 < HexArea.cross (b - a) (c - b)) := by
  rw [shoelace2_triple_eq_cross]

/-- **Per-vertex ear-step compatibility.**  At a genuine hex turn
    `v₀ → v₁ → v₂` (the first edge being an adjacency), the combinatorial turn
    sign `hexTurnSign v₀ v₁ v₂` equals the orientation of the embedded ear
    triangle `[embed v₀, embed v₁, embed v₂]`.

    This is the exact compatibility the ear-clipping induction needs: cutting the
    vertex `v₁` changes the total signed turn by `hexTurnSign v₀ v₁ v₂` and the
    signed area by the triangle term `HexArea.shoelace2 [..]` (via
    `HexArea.shoelace2_ear`), and the two changes have the *same* sign, so the
    invariant `total signed turn = 6 · sign(area)` is preserved. -/
lemma hexTurnSign_eq_shoelace2_triple_sign (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) :
    (hexTurnSign v₀ v₁ v₂ : ℤ) =
      (if 0 < HexArea.shoelace2
              [correctHexEmbed v₀, correctHexEmbed v₁, correctHexEmbed v₂]
       then 1 else -1) := by
  rw [hexTurnSign_eq_cross_sign v₀ v₁ v₂ h₁]
  congr 1
  exact propext (shoelace2_triple_sign _ _ _).symm

end
