/-
# The base hexagonal face and its signed area / turning (Umlaufsatz base case)

This file isolates the concrete *base case* of the discrete Gauss–Bonnet /
ear-clipping route to the discrete Hopf Umlaufsatz: a single hexagonal face of
the honeycomb, traversed once as a closed trail.

It is deliberately placed **upstream** of the sorry'd Umlaufsatz core
`hex_signed_turn_eq_six_sign_shoelace` (in
`RequestProject.SAWUmlaufSignedArea`), so that the base-case facts below are
genuine, self-contained computations that cannot circularly invoke the
unproved core.

## Contents (all sorry-free)

* `hexEmbeddedPolygon` — the planar polygon `L.dropLast.map correctHexEmbed`
  obtained by embedding the vertex cycle of a closed hex trail into `ℂ`.
* `hexHexagon` — a concrete hexagonal face of the honeycomb, as a closed trail.
* `hexHexagon_is_simple_closed_trail` — it satisfies all Umlaufsatz hypotheses
  (length `≥ 4`, `HexTrailList`, closed, simple interior).
* `hexHexagon_signed_turn` — its total signed turn is `+6` (turning number `+1`).
* `hexHexagon_shoelace2_eq` — its embedded signed area is `HexArea.shoelace2 = 3√3`.
* `hexHexagon_shoelace2_pos` — hence the signed area is positive.

Together `hexHexagon_signed_turn` (`+6`) and `hexHexagon_shoelace2_pos`
(`area > 0`) fix the orientation/sign convention
`total signed turn = 6 · sign (signed area)` used in the inductive core.

This file is imported from `RequestProject.SAWUmlaufSignedArea` (hence
transitively from `RequestProject.SAWFinal`).
-/

import Mathlib
import RequestProject.SAWUmlaufBridge
import RequestProject.SAWSignedArea

open Real Complex ComplexConjugate

noncomputable section

/-- The planar polygon obtained by embedding the vertex cycle of a closed hex
    trail: drop the repeated closing vertex and embed each lattice vertex into
    `ℂ`.  For a *simple* closed trail this is a genuine simple polygon with
    pairwise-distinct vertices (`hex_closed_trail_embed_nodup`). -/
def hexEmbeddedPolygon (L : List HexVertex) : List ℂ :=
  L.dropLast.map correctHexEmbed

/-- A concrete hexagonal face of the honeycomb, written as a closed trail
    (the last vertex repeats the first).  Its six edges are the six sides of one
    hexagon. -/
def hexHexagon : List HexVertex :=
  [(0, 0, false), (0, 0, true), (0, -1, false), (1, -1, true),
   (1, -1, false), (1, 0, true), (0, 0, false)]

/-- The concrete hexagon is a simple closed hex trail: it has length `7 ≥ 4`, is
    a `HexTrailList`, is closed (`head? = getLast?`), and its interior vertices
    are distinct. -/
lemma hexHexagon_is_simple_closed_trail :
    4 ≤ hexHexagon.length ∧ HexTrailList hexHexagon ∧
    hexHexagon.head? = hexHexagon.getLast? ∧ hexHexagon.tail.dropLast.Nodup := by
  unfold hexHexagon; simp +decide [ HexTrailList ]

/-- **Base case of the discrete Gauss–Bonnet induction.**  Going once around a
    single hexagonal face accumulates total signed turn `+6` (turning number
    `+1`, i.e. counterclockwise for this orientation). -/
lemma hexHexagon_signed_turn :
    hexSignedTurnCount hexHexagon +
      hexTurnSign (hexHexagon.get ⟨hexHexagon.length - 2, by decide⟩)
        (hexHexagon.get ⟨0, by decide⟩) (hexHexagon.get ⟨1, by decide⟩) = 6 := by
  unfold hexTurnSign; norm_num [ hexHexagon ] ;
  unfold correctHexEmbed; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ] ;
  ring_nf; norm_num;
  simp +decide [ hexSignedTurnCount, hexTurnSign ];
  unfold correctHexEmbed; norm_num [ Complex.normSq, Complex.div_im ] ; ring_nf ;
  norm_num [ Real.sqrt_lt ]

/-- The embedded hexagonal face has signed area `HexArea.shoelace2 = 3·√3`. -/
lemma hexHexagon_shoelace2_eq :
    HexArea.shoelace2 (hexEmbeddedPolygon hexHexagon) = 3 * Real.sqrt 3 := by
  unfold hexEmbeddedPolygon hexHexagon
  norm_num [ HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross, correctHexEmbed ]
  ring

/-- **Base case for the signed area.**  The embedded hexagonal face has positive
    signed area.  Together with `hexHexagon_signed_turn` (total signed turn `+6`)
    this fixes the sign convention `total signed turn = 6 · sign (signed area)`
    in `hex_signed_turn_eq_six_sign_shoelace`, and is the base case of the
    ear-clipping / discrete Gauss–Bonnet induction. -/
lemma hexHexagon_shoelace2_pos :
    0 < HexArea.shoelace2 (hexEmbeddedPolygon hexHexagon) := by
  rw [hexHexagon_shoelace2_eq]
  have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  positivity

end
