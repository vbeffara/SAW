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
transitively from `RequestProject.SAWFinal`).

**Status.**  `hex_signed_turn_eq_six_sign_shoelace` is now **proved sorry-free**
here by *deriving* it from the general planar-polygon Umlaufsatz
(`polygon_umlaufsatz`) applied to the embedded polygon, via the bridge
`polyWind_hexEmbedded_cyclic` (cyclic turning = `hexWalkWinding L + closure`)
and the already-proved combinatorial reductions
(`hexWalkWinding_eq_signedTurnCount`, `hex_closure_arg_eq_sign`).  The remaining
Umlaufsatz gaps are the two clean, reusable topological facts in
`RequestProject.SAWUmlaufPolygon`:
* `polygon_umlaufsatz` — the classical turning-tangent theorem for a
  non-self-intersecting polygon in `ℂ`; and
* `hexEmbeddedPolygon_edges_disjoint` — honeycomb planarity (the embedded
  polygon's edges meet only at shared vertices).
-/

import Mathlib
import RequestProject.SAWUmlaufHexagon
import RequestProject.SAWUmlaufEmbed
import RequestProject.SAWUmlaufPolygon

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

    **Now proved sorry-free** by deriving it from the general planar-polygon
    Umlaufsatz `polygon_umlaufsatz` (applied to `hexEmbeddedPolygon L`) through
    the bridge `polyWind_hexEmbedded_cyclic` and the combinatorial reductions
    `hexWalkWinding_eq_signedTurnCount` / `hex_closure_arg_eq_sign`.  The two
    remaining irreducible topological gaps live in
    `RequestProject.SAWUmlaufPolygon` (`polygon_umlaufsatz` and
    `hexEmbeddedPolygon_edges_disjoint`). -/
lemma hex_signed_turn_eq_six_sign_shoelace (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    hexSignedTurnCount L +
      hexTurnSign (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨0, by omega⟩)
        (L.get ⟨1, by omega⟩)
      = 6 * (if 0 < HexArea.shoelace2 (hexEmbeddedPolygon L) then 1 else -1) := by
  -- Apply the general planar-polygon Umlaufsatz to the embedded polygon, then
  -- divide out the common `π/3` against the proved combinatorial reductions.
  have hlen3 : 3 ≤ (hexEmbeddedPolygon L).length := by
    rw [hexEmbeddedPolygon_length]; omega
  have hsimple' : PolygonSimple (hexEmbeddedPolygon L) :=
    hexEmbeddedPolygon_polygonSimple L hL h_trail h_closed h_simple
  have hum := polygon_umlaufsatz (hexEmbeddedPolygon L) hlen3 hsimple'
  have hglue := polyWind_hexEmbedded_cyclic L hL h_closed
  -- Combine: `hexWalkWinding L + closure = 2π · sign(area)`.
  rw [hglue] at hum
  -- Reduce the two turning terms to `(π/3)·(integer count)`.
  rw [hexWalkWinding_eq_signedTurnCount L h_trail,
      hex_closure_arg_eq_sign L hL h_trail h_closed h_simple] at hum
  set S : ℤ := hexSignedTurnCount L with hS
  set cs : ℤ := hexTurnSign (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨0, by omega⟩)
    (L.get ⟨1, by omega⟩) with hcs
  set b : ℝ := (if 0 < HexArea.shoelace2 (hexEmbeddedPolygon L) then 1 else -1) with hb
  -- hum : π/3 * S + π/3 * cs = 2π · b
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have key : ((S + cs : ℤ) : ℝ) = 6 * b := by
    push_cast
    have h2 : Real.pi * (((S : ℝ) + cs) / 3) = Real.pi * (2 * b) := by
      ring_nf; ring_nf at hum; linarith [hum]
    have h3 : ((S : ℝ) + cs) / 3 = 2 * b := mul_left_cancel₀ hpi h2
    linarith
  by_cases hpos : 0 < HexArea.shoelace2 (hexEmbeddedPolygon L)
  · have hb1 : b = 1 := by rw [hb, if_pos hpos]
    rw [hb1] at key
    have : ((S + cs : ℤ) : ℝ) = ((6 : ℤ) : ℝ) := by push_cast at key ⊢; linarith
    have hSc : S + cs = 6 := by exact_mod_cast this
    rw [if_pos hpos]; push_cast; omega
  · have hb1 : b = -1 := by rw [hb, if_neg hpos]
    rw [hb1] at key
    have : ((S + cs : ℤ) : ℝ) = ((-6 : ℤ) : ℝ) := by push_cast at key ⊢; linarith
    have hSc : S + cs = -6 := by exact_mod_cast this
    rw [if_neg hpos]; push_cast; omega

end
