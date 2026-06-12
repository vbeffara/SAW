/-
# The discrete Hopf Umlaufsatz for simple closed honeycomb trails

This file collects the three top-level statements of the discrete Umlaufsatz
(the turning-tangent theorem) for simple closed trails on the hexagonal
lattice, **relocated here from `RequestProject.SAWTurningNumber`** so that the
genuinely topological core has the full signed-area toolkit in scope:

* `RequestProject.SAWSignedArea`   — the shoelace functional `HexArea.shoelace2`,
  its reversal antisymmetry, translation invariance, and ear step;
* `RequestProject.SAWUmlaufBridge`  — `hexTurnSign_eq_cross_sign` (the turn sign
  equals the sign of the geometric cross product) and `hex_turn_cross`;
* `RequestProject.SAWUmlaufEmbed`   — `hex_closed_trail_embed_nodup` (the
  embedded polygon `L.dropLast.map correctHexEmbed` has pairwise-distinct points
  in `ℂ`, i.e. it is a genuine *simple polygon in the plane*).

## Contents

* `hex_total_signed_turn_pm_six` — **the remaining topological gap.** For a
  simple closed hex trail the total signed-turn count over all polygon vertices
  (the interior turns `hexSignedTurnCount L` plus the closing-turn sign) equals
  `±6`. This is the discrete Hopf Umlaufsatz in its cleanest purely-integer
  form, equivalent in difficulty to the Jordan curve theorem for polygons, and
  is not available in Mathlib. (The analytic reduction *to* this statement is
  fully proved upstream in `SAWTurningNumber`.)
* `umlaufsatz_pm_one` — derived sorry-free from the core above: the turning
  number `n` of a simple closed hex trail is `±1`.
* `hex_closed_trail_turning_number` — derived sorry-free: the total turning
  (interior winding + closure) equals `±2π`.

## Base case of the Gauss–Bonnet route (proved)

* `hexHexagon` — a concrete hexagonal face of the honeycomb, as a closed trail.
* `hexHexagon_is_simple_closed_trail` — it satisfies all hypotheses of the
  Umlaufsatz (length `≥ 4`, `HexTrailList`, closed, simple).
* `hexHexagon_signed_turn` — its total signed turn equals `-6`, the explicit
  base case of the discrete Gauss–Bonnet induction over enclosed honeycomb
  faces.

This file is imported from `RequestProject.SAWFinal`.
-/

import Mathlib
import RequestProject.SAWUmlaufBridge
import RequestProject.SAWUmlaufEmbed

open Real Complex ComplexConjugate

noncomputable section

/-! ## The turning number theorem for simple closed hex trails (Umlaufsatz)

The "hard half": for a *simple* (non-self-intersecting) closed trail, the
integer multiple is exactly `±1`. This is the discrete analogue of Hopf's
Umlaufsatz / the turning tangent theorem.

It is reduced (`umlaufsatz_pm_one`) to the purely combinatorial
`hex_total_signed_turn_pm_six` below. -/

/-- **Combinatorial core of the discrete Umlaufsatz (remaining gap).**  For a
    simple closed hex trail, the total signed-turn count over all polygon
    vertices — the interior turns `hexSignedTurnCount L` plus the closing turn
    sign at the start vertex — equals `±6`.  Equivalently the turning number is
    `±1`.

    **Sorry**: this is the genuine topological content of the discrete
    Umlaufsatz / turning-tangent theorem (equivalently the Jordan curve theorem
    for polygons), now in its cleanest purely-integer form.  Provable by an
    ear-clipping induction on the perimeter (`HexArea.shoelace2_ear` provides the
    algebraic ear step; `hexTurnSign_eq_cross_sign` / `hex_turn_cross` link each
    turn sign to the signed triangle area; `hex_closed_trail_embed_nodup`
    supplies the planar simplicity) or by a discrete Gauss–Bonnet argument over
    the enclosed honeycomb faces (`hexHexagon_signed_turn` is the base case). -/
lemma hex_total_signed_turn_pm_six (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    hexSignedTurnCount L +
      hexTurnSign (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨0, by omega⟩)
        (L.get ⟨1, by omega⟩) = 6 ∨
    hexSignedTurnCount L +
      hexTurnSign (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨0, by omega⟩)
        (L.get ⟨1, by omega⟩) = -6 := by
  sorry

/-- The magnitude part of the Umlaufsatz: for a simple closed hex trail whose
    total turning is `2π·n`, the integer `n` is `±1`.

    This is *derived* from the combinatorial core
    `hex_total_signed_turn_pm_six` together with the signed-turn-count
    reduction (`hexWalkWinding_eq_signedTurnCount`) and the closing-turn sign
    (`hex_closure_arg_eq_sign`). -/
lemma umlaufsatz_pm_one (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup)
    (n : ℤ)
    (hn : hexWalkWinding L +
      Complex.arg ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
        (correctHexEmbed (L.get ⟨0, by omega⟩) -
          correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)))
      = 2 * Real.pi * n) :
    n = 1 ∨ n = -1 := by
  have hw := hexWalkWinding_eq_signedTurnCount L h_trail
  have hc := hex_closure_arg_eq_sign L hL h_trail h_closed h_simple
  rw [hw, hc] at hn
  set S : ℤ := hexSignedTurnCount L with hS
  set cs : ℤ := hexTurnSign (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨0, by omega⟩)
    (L.get ⟨1, by omega⟩) with hcs
  -- hn : π/3 * S + π/3 * cs = 2π·n, with S, cs, n integers.
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have key : ((S + cs : ℤ) : ℝ) = ((6 * n : ℤ) : ℝ) := by
    push_cast
    have h2 : Real.pi * (((S : ℝ) + cs) / 3) = Real.pi * (2 * n) := by ring_nf; ring_nf at hn; linarith [hn]
    have h3 : ((S : ℝ) + cs) / 3 = 2 * n := mul_left_cancel₀ hpi h2
    linarith
  have key' : S + cs = 6 * n := by exact_mod_cast key
  rcases hex_total_signed_turn_pm_six L hL h_trail h_closed h_simple with h | h
  · left; rw [← hS, ← hcs] at h; omega
  · right; rw [← hS, ← hcs] at h; omega

/-- The turning number theorem for simple closed hex trails.
    For a list [v₀, v₁, ..., vₙ₋₁, v₀] that forms a simple closed trail
    on the hex lattice:
    hexWalkWinding L + closure_turn = ±2π

    This is the discrete Gauss-Bonnet theorem applied to simple closed
    polygons on the hexagonal lattice (Umlaufsatz). The proof splits into
    the "easy half" (`hex_closed_winding_int_mul`: the total turning is a
    multiple of `2π`) and the "hard half" (`umlaufsatz_pm_one`: the
    multiple is `±1`). -/
lemma hex_closed_trail_turning_number (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    let d_first := correctHexEmbed (L.get ⟨1, by omega⟩) -
                   correctHexEmbed (L.get ⟨0, by omega⟩)
    let d_last := correctHexEmbed (L.get ⟨0, by omega⟩) -
                  correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)
    let closure := Complex.arg (d_first / d_last)
    hexWalkWinding L + closure = 2 * Real.pi ∨
    hexWalkWinding L + closure = -(2 * Real.pi) := by
  intro d_first d_last closure
  obtain ⟨n, hn⟩ := hex_closed_winding_int_mul L hL h_trail h_closed
  rcases umlaufsatz_pm_one L hL h_trail h_closed h_simple n hn with h | h
  · left; rw [show closure = _ from rfl, hn, h]; push_cast; ring
  · right; rw [show closure = _ from rfl, hn, h]; push_cast; ring

/-! ## Base case of the discrete Gauss–Bonnet route: one hexagonal face

A single hexagonal face of the honeycomb, traversed as a closed trail, has total
signed turn `±6` (here `-6`).  This is the base case of the Gauss–Bonnet
induction over enclosed faces: every closed simple honeycomb trail bounds a
union of hexagonal faces, the boundary turning telescopes over the faces, and a
single face contributes `±2π = ±6·(π/3)`. -/

/-- A concrete hexagonal face of the honeycomb, written as a closed trail
    (the last vertex repeats the first).  Its six edges are the six sides of one
    hexagon; one checks directly that consecutive vertices are `hexGraph`-adjacent
    and that the closing vertex returns to the start. -/
def hexHexagon : List HexVertex :=
  [(0, 0, false), (0, 0, true), (0, -1, false), (1, -1, true),
   (1, -1, false), (1, 0, true), (0, 0, false)]

/-
The concrete hexagon is a simple closed hex trail: it has length `7 ≥ 4`, is
    a `HexTrailList` (consecutive adjacencies, no immediate backtracking), is
    closed (`head? = getLast?`), and its interior vertices are distinct.
-/
lemma hexHexagon_is_simple_closed_trail :
    4 ≤ hexHexagon.length ∧ HexTrailList hexHexagon ∧
    hexHexagon.head? = hexHexagon.getLast? ∧ hexHexagon.tail.dropLast.Nodup := by
  unfold hexHexagon; simp +decide [ HexTrailList ] ;

/-
**Base case of the discrete Gauss–Bonnet induction.**  Going once around a
    single hexagonal face accumulates total signed turn `+6` (equivalently
    turning number `+1`, i.e. counterclockwise for this orientation: the
    embedded hexagon has positive shoelace signed area).
-/
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

end