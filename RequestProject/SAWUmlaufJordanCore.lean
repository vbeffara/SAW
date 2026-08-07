/-
# The Jordan core of the polygonal Umlaufsatz: winding dichotomy and the ear interior

Every remaining gap of the Meisters-style induction that proves the discrete
Hopf Umlaufsatz (`polygon_umlaufsatz`, `RequestProject.SAWUmlaufPolygon`) reduces
to **one** classical plane-topology statement about the winding number `ptWind`
of a *simple* closed polygon:

> `polygon_ptWind_dichotomy`: for a simple polygon `V` with `3 ≤ V.length` and a
> point `x` off every closed edge of `V`, either `ptWind x V = 0` (`x` outside)
> or `ptWind x V = 2π · sign (shoelace2 V)` (`x` inside).

This is the point-in-polygon form of the Jordan curve theorem for polygons.  It
is stated here with a `sorry` — it is the *single* remaining topological input of
the whole Umlaufsatz development, and this file shows how the previously separate
gaps follow from it.  **This is not a dead branch**: the file is imported on the
live route (see below), and the consequences proved here are sorry-free modulo
that one statement.

## What is proved here (all sorry-free given the dichotomy)

* `exists_clearance` — a point off a finite list of segments stays off them in a
  whole ball around it.
* `cross_sum_edges` — the three edge cross products of a point sum to the
  (doubled) signed area of the triangle.
* `inTriangleStrict_of_segment` — the strict interior of a triangle is convex.
* `bary_openSegment_ab` — the barycentric coordinates of an interior point of the
  side `[a, b]` of the triangle `a, b, c`.
* `exists_perturb_pair` — a pair of points on the two sides of the side `[a, b]`,
  arbitrarily close to a prescribed interior point of that side, the one on the
  side of the triangle being strictly inside the triangle.
* `ear_interior_ptWind_ne_zero` — **the ear-interior consequence**: if `a, b, c`
  is an empty ear of the simple polygon `L` whose tip corner is non-degenerate,
  and the orientation of the ear agrees with the orientation of `L`, then the
  winding number of `L` around any point strictly inside the ear triangle is
  nonzero.  (Jump `2π` across the ear side `[a, b]`, use the dichotomy on both
  sides of that side, and transport the winding along the triangle interior.)
* `chord_ear_empty_other_jordan` — the Jordan-separation keystone
  `chord_ear_empty_other` re-derived from the dichotomy: a vertex of the *other*
  chord piece cannot lie strictly inside an empty ear triangle of the piece `P`,
  since its winding number around `P` is `0` (`chord_ear_other_ptWind_zero`,
  proved) while the ear interior forces it to be nonzero.

Unlike the older route through `clipped_ear_escape_walk`, no cyclic
non-degeneracy of the chord piece `P` is needed: the ear clearance is supplied by
`RequestProject.SAWUmlaufEarClearance`, which only uses non-degeneracy of the ear
*tip* (an interior corner of the ambient polygon).
-/

import Mathlib
import RequestProject.SAWUmlaufPolyEscape
import RequestProject.SAWUmlaufEarClearance
import RequestProject.SAWUmlaufWindJump
import RequestProject.SAWUmlaufEarTipEscape
import RequestProject.SAWUmlaufJordanStep

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The former topological input (superseded) -/

/- **Point-in-polygon dichotomy (Jordan curve theorem for polygons).**  For a
simple closed polygon `V` and a point `x` off all its edges, the winding number
of `V` around `x` is either `0` or `2π · sign (shoelace2 V)`.

**Status: `sorry`.**  This is the single remaining plane-topology input of the
polygonal Umlaufsatz.  Classical proof: the ray-crossing index
(`RequestProject.SAWUmlaufRayIndex` expresses `ptWind` as a sum of wrap terms
with values in `{0, ±2π}`) is constant on the two components of the complement,
`0` on the unbounded one, and jumps by exactly `2π` across each edge
(`ptWind_jump_edge`, proved in `RequestProject.SAWUmlaufWindJump`); the collar of
a simple polygon has exactly two sides. -/
/- **SUPERSEDED (kept as a record, not a live gap).**  The point-in-polygon
dichotomy below was the previous single topological input.  It has been replaced
by the strictly weaker keystone `ear_interior_clip_ptWind_zero`
(`RequestProject.SAWUmlaufEarTipEscape`): *the ear region lies outside the
clipped polygon*.  That statement is all the Meisters induction consumes, it is
implied by the dichotomy, and it is already proved there in the convex-position
case.  The statement is retained, commented out, because it is the classical
form of the fact and may still be the most convenient route to the keystone.
-/
/-
theorem polygon_ptWind_dichotomy (V : List ℂ) (h3 : 3 ≤ V.length)
    (hsimple : PolygonSimple V) (x : ℂ)
    (hx : ∀ e ∈ HexArea.cycleEdges V, x ∉ segment ℝ e.1 e.2) :
    HexArea.ptWind x V = 0 ∨
      HexArea.ptWind x V = 2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1) := by
  sorry
-/

/-! ## 2. Elementary geometric preparation

The elementary bricks previously proved here (`exists_clearance`,
`cross_sum_edges`, `cross_real_mul`, `cross_I_mul_self`,
`inTriangleStrict_of_segment`, `bary_openSegment_ab`, `exists_perturb_pair`,
`cycleEdges_cons_cons`) have moved **upstream** to
`RequestProject.SAWUmlaufJordanDichotomy`, where they are consumed by the
derivation of the ear keystone from the dichotomy.  They remain available here
through the import chain. -/

/-! ## 3. The ear-interior consequence of the dichotomy -/

/-- **The winding number of a simple polygon around a point of an empty ear's
interior is nonzero.**

`a, b, c` is an empty ear of the simple polygon `L` (`hempty`, `hdiag`) whose tip
corner is non-degenerate (`hD`), and the ear is *positively coherent* with `L`
(`hor`: the ear triangle and `L` have the same orientation).  Then `ptWind x L`
is nonzero for every `x` strictly inside the ear triangle.

Proof.  Perturb the midpoint `m` of the ear side `[a, b]` to the two sides of that
side; the two winding numbers differ by `2π` (`ptWind_jump_edge`, using that `m`
lies on no other edge, `simple_edge_openSegment_not_mem`).  Both perturbed points
lie off all edges (clearance), so the dichotomy applies to both: their winding
numbers lie in `{0, 2π·σ}` with `σ = sign (shoelace2 L)`, and a difference of `2π`
forces the point on the side of the ear interior to carry the nonzero value.
Finally `ptWind · L` is constant on the (convex) open ear triangle, since the
triangle interior misses all edges (`ear_strict_interior_off_closedEdges`). -/
theorem ear_interior_ptWind_ne_zero (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hdich : PolyDichotomy (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 L))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x L ≠ 0 := by
  exact ear_interior_ptWind_ne_zero_via_clip L h4 hsimple ρ a b c rest hrot hdich hD hempty hdiag
    hor x hin
/-! ## 4. The Jordan-separation keystone, re-derived -/

/-- **`chord_ear_empty_other` from the dichotomy.**  A vertex `x` of the polygon
`W` that is not a vertex of the chord piece `P` cannot lie strictly inside an
empty ear triangle of `P`: its winding number around `P` vanishes
(`chord_ear_other_ptWind_zero`, proved), while `ear_interior_ptWind_ne_zero`
forces it to be nonzero.

The hypotheses are those of `chord_ear_empty_other` together with the two extra
data that the ear-interior argument needs and that are available at the call site
(`chord_ear_lift` in `RequestProject.SAWUmlaufPolyMeisters`): the ear tip corner
is non-degenerate (it is an interior corner of `W`), and no tail vertex of the
piece lies on the ear diagonal. -/
theorem chord_ear_empty_other_jordan (N : ℕ) (hN : DichBelow N)
    (W : List ℂ) (hsimple : PolygonSimple W) (hWN : W.length ≤ N)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiagW : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hDP : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (hdiagP : ∀ y ∈ tlP, y ∉ segment ℝ a' c')
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    ¬ HexArea.inTriangleStrict a' b' c' x := by
  intro hin
  have hzero : HexArea.ptWind x P = 0 :=
    chord_ear_other_ptWind_zero W hsimple k hk1 hk u v hu hv hdiagW hint P hP x hxW hxP
  have hPN : P.length ≤ N := by
    have : P.length ≤ W.length := by
      rcases hP with rfl | rfl
      · rw [HexArea.chordLeft_length W k hk]; omega
      · rw [HexArea.chordRight_length W k (by omega)]; omega
    omega
  exact ear_interior_ptWind_ne_zero_of_rotation_below N hN P hPN hPsimple a' b' c' s tlP
    hrotP hDP hemptyP hdiagP horientP x hin hzero
