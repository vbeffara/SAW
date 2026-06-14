/-
# The planar-polygon Umlaufsatz (general statement) and its bridge to hex trails

This file develops the **general planar-polygon form** of the discrete Hopf
Umlaufsatz and connects it to the honeycomb-specific core
`hex_signed_turn_eq_six_sign_shoelace` (in
`RequestProject.SAWUmlaufSignedArea`).

The point of this file is to *factor* the remaining topological content of the
discrete Umlaufsatz into two clean, reusable pieces:

1. `polygon_umlaufsatz` — the genuine plane-topology statement: for a
   **non-self-intersecting** closed polygon in `ℂ` (a "simple polygon"), the
   total exterior-angle turning equals `2π · sign(signed area)`.  This is the
   classical Umlaufsatz / turning-tangent theorem for polygons (equivalently
   the Jordan curve theorem for polygons), absent from Mathlib.  It is the
   single irreducible analytic/topological gap.

2. `hexEmbeddedPolygon_polygonSimple` — the honeycomb-specific *planarity*
   fact: the planar polygon obtained by embedding a simple closed hex trail is
   non-self-intersecting (its edges, being honeycomb lattice edges, meet only
   at shared vertices).  This is a finite geometric fact about unit honeycomb
   edges, also absent from Mathlib.

Everything else — the bridge `hexWalkWinding_eq_polyWind` turning the
honeycomb winding into the general polygon exterior-angle sum, the
`polyWind`-append glue identifying the cyclic total turning with
`hexWalkWinding L + closure`, and the reduction of the integer signed-turn core
to the real turning via the already proved `hexWalkWinding_eq_signedTurnCount` /
`hex_closure_arg_eq_sign` — is proved here sorry-free, so that the hex core
`hex_signed_turn_eq_six_sign_shoelace` is genuinely *derived* (in
`RequestProject.SAWUmlaufSignedArea`) from the two clean ingredients above.

This file is imported from `RequestProject.SAWUmlaufSignedArea` (hence
transitively from `RequestProject.SAWFinal`); it is **preparation** for the
Umlaufsatz core.
-/

import Mathlib
import RequestProject.SAWUmlaufHexagon
import RequestProject.SAWUmlaufEmbed

open Real Complex ComplexConjugate

noncomputable section

/-! ## The exterior-angle turning of a polygon in `ℂ`

`polyWind` is the analogue of `hexWalkWinding` for an arbitrary list of points
in `ℂ`: the sum, over consecutive triples, of the exterior turning angle
`arg ((p₂ - p₁) / (p₁ - p₀))`.  It lets us state the Umlaufsatz for genuine
planar polygons, decoupled from the hex lattice. -/

/-- The exterior-angle turning of a polygonal chain `P : List ℂ`: the sum over
    consecutive triples `p₀, p₁, p₂` of the turning angle `arg ((p₂-p₁)/(p₁-p₀))`.
    This is the planar-polygon analogue of `hexWalkWinding`. -/
def polyWind : List ℂ → ℝ
  | p₀ :: p₁ :: p₂ :: rest =>
      Complex.arg ((p₂ - p₁) / (p₁ - p₀)) + polyWind (p₁ :: p₂ :: rest)
  | _ => 0

@[simp] lemma polyWind_nil : polyWind [] = 0 := rfl
@[simp] lemma polyWind_singleton (a : ℂ) : polyWind [a] = 0 := rfl
@[simp] lemma polyWind_pair (a b : ℂ) : polyWind [a, b] = 0 := rfl

lemma polyWind_cons_cons_cons (a b c : ℂ) (rest : List ℂ) :
    polyWind (a :: b :: c :: rest) =
      Complex.arg ((c - b) / (b - a)) + polyWind (b :: c :: rest) := rfl

/-
**Bridge lemma.**  The honeycomb winding `hexWalkWinding` of a vertex list
    equals the general polygon exterior-angle turning `polyWind` of its planar
    embedding.  This is the link that lets the hex Umlaufsatz core be derived
    from the general planar-polygon Umlaufsatz.
-/
lemma hexWalkWinding_eq_polyWind (L : List HexVertex) :
    hexWalkWinding L = polyWind (L.map correctHexEmbed) := by
  induction' L with a L ih;
  · rfl;
  · cases L <;> simp_all +decide [ hexWalkWinding, polyWind ];
    cases ‹List HexVertex› <;> simp_all +decide [ hexWalkWinding, polyWind ]

/-
Appending a single point `b` to a chain `W` of length `≥ 2` adds exactly the
    one extra turn at the former last vertex:
    `polyWind (W ++ [b]) = polyWind W + arg ((b - last) / (last - penultimate))`,
    where `last = W[len-1]` and `penultimate = W[len-2]`.  This is the basic
    additivity step used to relate the cyclic total turning of a polygon to its
    open winding plus the closing turn.
-/
lemma polyWind_append_singleton (W : List ℂ) (hW : 2 ≤ W.length) (b : ℂ) :
    polyWind (W ++ [b]) =
      polyWind W +
        Complex.arg ((b - W[W.length - 1]'(by omega)) /
          (W[W.length - 1]'(by omega) - W[W.length - 2]'(by omega))) := by
  induction' W with a W ih generalizing b;
  · contradiction;
  · cases W <;> simp_all +decide [ List.length ];
    cases ‹List ℂ› <;> simp_all +decide [ List.length ];
    · -- By definition of polyWind, we have:
      simp [polyWind];
    · simp_all +decide [ polyWind_cons_cons_cons ];
      ring

/-- The embedded polygon has one fewer vertex than its closed trail. -/
lemma hexEmbeddedPolygon_length (L : List HexVertex) :
    (hexEmbeddedPolygon L).length = L.length - 1 := by
  simp [hexEmbeddedPolygon]

/-
**Cyclic-turning glue.**  The cyclic total turning of the embedded polygon
    (in the `polyWind (V ++ [V[0], V[1]])` form produced by `polygon_umlaufsatz`)
    equals the honeycomb winding plus the closing turn — exactly the left-hand
    side `hexWalkWinding L + closure` appearing throughout the hex Umlaufsatz
    chain.  This is the key bridge identity assembling `hexWalkWinding_eq_polyWind`
    (open winding = embedding's `polyWind`) and `polyWind_append_singleton` (the
    single extra closing turn).
-/
lemma polyWind_hexEmbedded_cyclic (L : List HexVertex) (hL : 4 ≤ L.length)
    (h_closed : L.head? = L.getLast?) :
    polyWind (hexEmbeddedPolygon L ++
        [(hexEmbeddedPolygon L)[0]'(by rw [hexEmbeddedPolygon_length]; omega),
         (hexEmbeddedPolygon L)[1]'(by rw [hexEmbeddedPolygon_length]; omega)])
      = hexWalkWinding L +
        Complex.arg
          ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
            (correctHexEmbed (L.get ⟨0, by omega⟩) -
              correctHexEmbed (L.get ⟨L.length - 2, by omega⟩))) := by
  rw [ hexWalkWinding_eq_polyWind ];
  convert polyWind_append_singleton _ _ _ using 2;
  any_goals exact correctHexEmbed ( L.get ⟨ 1, by omega ⟩ );
  all_goals norm_num [ hexEmbeddedPolygon ];
  any_goals omega;
  · rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> simp_all +decide [ List.dropLast ];
    · contradiction;
    · induction L using List.reverseRecOn <;> simp_all +decide [ List.dropLast ];
      grind;
  · rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> norm_num at *;
    grind +suggestions

/-! ## Non-self-intersection of a closed polygon

A closed polygon is given by its *vertex cycle* `V : List ℂ` (no repeated
closing vertex).  Its closed edges are the consecutive pairs together with the
wrap-around pair, packaged by `closedEdges`. -/

/-- The closed edges of the vertex cycle `V` as ordered pairs:
    `(V₀,V₁), (V₁,V₂), …, (V_{n-1}, V₀)`.  Built as `V.zip (V.rotate 1)`. -/
def closedEdges (V : List ℂ) : List (ℂ × ℂ) := V.zip (V.rotate 1)

/-- Predicate: the closed polygon with vertex cycle `V` (no repeated closing
    vertex) is *non-self-intersecting* — distinct edges that share no endpoint
    are disjoint segments.  Together with `V.Nodup`, edges that share exactly
    one endpoint are adjacent and meet only at that vertex, so this is the
    genuine "simple polygon in the plane" condition. -/
def PolygonSimple (V : List ℂ) : Prop :=
  V.Nodup ∧
  ∀ e₁ ∈ closedEdges V, ∀ e₂ ∈ closedEdges V,
    e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
    Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2)

/-- **The planar-polygon Umlaufsatz (remaining topological core).**  For a
    non-self-intersecting closed polygon with vertex cycle `V` (`3 ≤ V.length`,
    `PolygonSimple V`), the total exterior-angle turning around the cycle equals
    `2π · sign (signed area)`, where the signed area is `HexArea.shoelace2 V`.

    The total turning is expressed as `polyWind (V ++ [V[0], V[1]])`: appending
    the first two vertices closes the cycle so that every one of the `V.length`
    cyclic turns is counted exactly once.

    This is the classical Hopf Umlaufsatz / turning-tangent theorem for
    polygons (equivalently the Jordan curve theorem for polygons).  It is the
    single irreducible plane-topology gap, absent from Mathlib.  Proof route:
    ear-clipping induction on `V.length` (a simple polygon with `≥ 4` vertices
    has an ear; ear removal preserves `PolygonSimple`; the signed area changes
    by the ear triangle term `HexArea.shoelace2_ear` and the turning by the
    matching ear angle), with the triangle base case. -/
lemma polygon_umlaufsatz (V : List ℂ) (hlen : 3 ≤ V.length)
    (hsimple : PolygonSimple V) :
    polyWind (V ++ [V[0]'(by omega), V[1]'(by omega)]) =
      2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1) := by
  sorry

/-- **Honeycomb edge-disjointness (remaining geometric core).**  For a simple
    closed hex trail, two closed edges of the embedded polygon that share no
    endpoint have disjoint segments.  This is the *only* genuinely geometric
    content of honeycomb planarity (the `Nodup` half being already established by
    `hex_closed_trail_embed_nodup`).

    **Sorry**: a finite geometric fact about unit honeycomb edges — two distinct
    honeycomb lattice edges meet only at a shared vertex — absent from Mathlib. -/
lemma hexEmbeddedPolygon_edges_disjoint (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    ∀ e₁ ∈ closedEdges (hexEmbeddedPolygon L),
      ∀ e₂ ∈ closedEdges (hexEmbeddedPolygon L),
        e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
        Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2) := by
  sorry

/-- **Honeycomb planarity.**  The planar polygon obtained by embedding a simple
    closed hex trail is non-self-intersecting.  The `Nodup` half is
    `hex_closed_trail_embed_nodup`; the edge-disjointness half is
    `hexEmbeddedPolygon_edges_disjoint`.  This is the second clean ingredient
    (besides `polygon_umlaufsatz`) from which the hex Umlaufsatz core is
    derived. -/
lemma hexEmbeddedPolygon_polygonSimple (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    PolygonSimple (hexEmbeddedPolygon L) :=
  ⟨hex_closed_trail_embed_nodup L hL h_trail h_closed h_simple,
   hexEmbeddedPolygon_edges_disjoint L hL h_trail h_closed h_simple⟩

end