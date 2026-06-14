/-
# Signed-area reformulation of the discrete Umlaufsatz core

This file restates the remaining topological core of the discrete Hopf
Umlaufsatz for simple closed honeycomb trails in its *inductive-friendly*
signed-area form, and connects it to the signed-area toolkit
(`RequestProject.SAWSignedArea`, `RequestProject.SAWUmlaufBridge`,
`RequestProject.SAWUmlaufEmbed`) and the base case
(`RequestProject.SAWUmlaufHexagon`).

The bare `±6` disjunction `hex_total_signed_turn_pm_six` is *not* a good target
for an ear-clipping induction: the disjunction is not preserved when a vertex is
removed.  The genuinely inductive statement is the **equality**

  total signed turn  =  `6 · sign (signed area)`,

i.e. `hex_signed_turn_eq_six_sign_shoelace` below.  This is strictly stronger
(it pins which of `±6` occurs, namely by the orientation/signed area of the
embedded polygon), and is exactly the invariant maintained by an ear-clipping /
discrete Gauss–Bonnet induction:

* the signed area changes by the exact ear amount `HexArea.shoelace2_ear`;
* each removed turn sign equals the sign of the corresponding triangle cross
  product (`hexTurnSign_eq_cross_sign`, `hex_turn_cross`); and
* the base case is a single hexagonal face, where the total signed turn is `+6`
  and the embedded hexagon has positive signed area `+3√3`
  (`hexHexagon_signed_turn`, `hexHexagon_shoelace2_pos`).

The bare `±6` disjunction is then an immediate consequence (the right-hand side
`6 · (if 0 < area then 1 else -1)` is always `6` or `-6`), which is how
`hex_total_signed_turn_pm_six` is discharged downstream in
`RequestProject.SAWUmlaufGaussBonnet`.

This file is imported from `RequestProject.SAWUmlaufGaussBonnet` (hence
transitively from `RequestProject.SAWFinal`).  It is **preparation** for the
Umlaufsatz: the single remaining `sorry` here,
`hex_signed_turn_eq_six_sign_shoelace`, is the irreducible Jordan-curve-level
content, now in its cleanest signed-area form.
-/

import Mathlib
import RequestProject.SAWUmlaufHexagon
import RequestProject.SAWUmlaufEmbed

open Real Complex ComplexConjugate

noncomputable section

/-- **Signed-area form of the discrete Umlaufsatz (remaining core).**  For a
    simple closed hex trail, the total signed-turn count over all polygon
    vertices — the interior turns `hexSignedTurnCount L` plus the closing-turn
    sign at the start vertex — equals `6 · sign (signed area)`, where the signed
    area is `HexArea.shoelace2 (hexEmbeddedPolygon L)` (twice the signed area of
    the embedded polygon).  Equivalently, the turning number is `+1` for a
    counterclockwise (positive-area) traversal and `-1` for a clockwise one.

    This is the genuine topological content of the discrete Hopf Umlaufsatz /
    turning-tangent theorem (equivalently the Jordan curve theorem for polygons),
    in its cleanest *inductive* signed-area form.  Proof route (ear-clipping /
    discrete Gauss–Bonnet induction over the perimeter):
    * the algebraic ear step for the area is `HexArea.shoelace2_ear`;
    * each turn sign equals the sign of the corresponding triangle cross product
      via `hexTurnSign_eq_cross_sign` and `hex_turn_cross` (each turn cross is
      `±√3/2 ≠ 0`, so no three consecutive vertices are collinear);
    * planar simplicity of the embedded polygon is `hex_closed_trail_embed_nodup`;
    * the base case is one hexagonal face, with total signed turn `+6` and
      positive signed area (`hexHexagon_signed_turn`, `hexHexagon_shoelace2_pos`).

    **Sorry**: this is the irreducible Jordan-curve-level content, absent from
    Mathlib. -/
lemma hex_signed_turn_eq_six_sign_shoelace (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    hexSignedTurnCount L +
      hexTurnSign (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨0, by omega⟩)
        (L.get ⟨1, by omega⟩)
      = 6 * (if 0 < HexArea.shoelace2 (hexEmbeddedPolygon L) then 1 else -1) := by
  sorry

end
