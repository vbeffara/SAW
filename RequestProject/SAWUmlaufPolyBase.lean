/-
# The planar-polygon Umlaufsatz (general statement) and its bridge to hex trails

This file develops the **general planar-polygon form** of the discrete Hopf
Umlaufsatz and connects it to the honeycomb-specific core
`hex_signed_turn_eq_six_sign_shoelace` (in
`RequestProject.SAWUmlaufSignedArea`).

The point of this file is to *factor* the topological content of the discrete
Umlaufsatz into clean, reusable pieces:

1. `polygon_umlaufsatz` — the genuine plane-topology statement: for a
   **non-self-intersecting** closed polygon in `ℂ` (a "simple polygon"), the
   total exterior-angle turning equals `2π · sign(signed area)`.  This is the
   classical Umlaufsatz / turning-tangent theorem for polygons (equivalently
   the Jordan curve theorem for polygons), absent from Mathlib.  It is proved
   here by ear-clipping induction; its exact turning-preservation core
   `ear_turn_concat` is now **fully proved** (via the per-corner no-wrap
   lemmas `ear_corner_turn_a` / `ear_corner_turn_c`, the pure `arg`-additivity
   criterion `arg_add_eq_arg_mul_of_im_sign`, and the cone cross-sign geometry
   `cone_cross_sign_of_disjoint` / `corner_a_cross_sign` / `corner_c_cross_sign`).

2. `hexEmbeddedPolygon_polygonSimple` — the honeycomb-specific *planarity*
   fact: the planar polygon obtained by embedding a simple closed hex trail is
   non-self-intersecting (its edges, being honeycomb lattice edges, meet only
   at shared vertices).  Proved here.

**Single remaining open core.**  The whole discrete Umlaufsatz now reduces to
the one lemma `exists_empty_convex_ear` below — the Meisters "two-ears"
existence theorem (a simple non-degenerate polygon with `≥ 4` vertices has a
cyclic rotation exhibiting an empty convex ear).  Everything that consumes it
(`exists_front_ear`, `exists_ear_clip`, `polygon_ear_reduction`,
`polygon_umlaufsatz`) is sorry-free.

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
import RequestProject.SAWUmlaufHexEdge
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarExist
import RequestProject.SAWUmlaufEarConvex
import RequestProject.SAWUmlaufEarEmpty
import RequestProject.SAWUmlaufEarExtreme
import RequestProject.SAWUmlaufEarSide
import RequestProject.SAWUmlaufEarOneSided
import RequestProject.SAWUmlaufSegment
import RequestProject.SAWUmlaufEscapeHelpers
import RequestProject.SAWUmlaufEscapeHull
import RequestProject.SAWUmlaufCorner
import RequestProject.SAWUmlaufEarSplit
import RequestProject.SAWUmlaufChordIncidence
import RequestProject.SAWUmlaufCornerEscape
import RequestProject.SAWUmlaufPtWind
import RequestProject.SAWUmlaufPtWindJordan
import RequestProject.SAWUmlaufPtWindHalfPlane
import RequestProject.SAWUmlaufPtWindRay
import RequestProject.SAWUmlaufExterior
import RequestProject.SAWUmlaufPtWindMove
import RequestProject.SAWUmlaufPolyConn
import RequestProject.SAWUmlaufHullExterior
import RequestProject.SAWUmlaufComponentEscape
import RequestProject.SAWUmlaufArcEscape
import RequestProject.SAWUmlaufChordArcWind

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

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

/-! ## Non-degeneracy of a polygonal chain

`PolygonSimple` (`V.Nodup` plus disjointness of non-adjacent edges) is **not**
by itself enough to make the planar Umlaufsatz true: it does not exclude three
*consecutive* collinear vertices.  For instance the collinear "spike"
`a = 0, b = 2, c = 1` has all three edges pairwise sharing an endpoint (so the
disjointness clause is vacuous) and `V.Nodup`, yet
`polyWind [a,b,c,a,b] = arg(-1/2) + arg(1) + arg(-2) = 2π` while its signed area
`HexArea.shoelace2 [a,b,c] = 0`, so `2π · sign(area)` would be `-2π ≠ 2π`.

The missing hypothesis is that no three consecutive vertices are collinear,
i.e. every turn has a nonzero cross product.  This is genuinely satisfied by the
honeycomb embedding (every hex turn cross is `±√3/2`, see `hex_turn_cross`), and
it also forces consecutive edges to meet only at their shared vertex, so
together with `PolygonSimple` it gives a genuine simple polygon. -/

/-- A polygonal chain is *non-degenerate* when every consecutive triple
    `p₀, p₁, p₂` has nonzero cross product `cross (p₁ - p₀) (p₂ - p₁)` — i.e. no
    three consecutive vertices are collinear.  Applied to the closed form
    `V ++ [V[0], V[1]]` this asserts that *every* cyclic turn of the polygon is a
    genuine (non-flat, non-spike) corner. -/
def polyNondeg : List ℂ → Prop
  | p₀ :: p₁ :: p₂ :: rest =>
      HexArea.cross (p₁ - p₀) (p₂ - p₁) ≠ 0 ∧ polyNondeg (p₁ :: p₂ :: rest)
  | _ => True

@[simp] lemma polyNondeg_nil : polyNondeg [] = True := rfl
@[simp] lemma polyNondeg_singleton (a : ℂ) : polyNondeg [a] = True := rfl
@[simp] lemma polyNondeg_pair (a b : ℂ) : polyNondeg [a, b] = True := rfl

lemma polyNondeg_cons_cons_cons (a b c : ℂ) (rest : List ℂ) :
    polyNondeg (a :: b :: c :: rest) =
      (HexArea.cross (b - a) (c - b) ≠ 0 ∧ polyNondeg (b :: c :: rest)) := rfl

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
    matching ear angle), with the triangle base case.

    **Non-degeneracy hypothesis `hnd`.**  `PolygonSimple` alone does *not* make
    this statement true: it allows three consecutive collinear vertices (a flat
    vertex or a "spike"), for which the disjointness clause is vacuous but the
    turning over/undercounts relative to `2π·sign(area)` (e.g. the spike
    `0, 2, 1`).  The extra hypothesis `polyNondeg (V ++ [V[0], V[1]])` rules
    these out (every cyclic turn is a genuine corner), restoring truth.  It is
    satisfied by the honeycomb embedding via `hexEmbeddedPolygon_polyNondeg`. -/

/-
**Triangle base case of the planar Umlaufsatz.**  For a non-degenerate
    triangle (`HexArea.cross (b-a) (c-b) ≠ 0`, i.e. `a, b, c` not collinear), the
    total cyclic exterior-angle turning `polyWind [a,b,c,a,b]` equals
    `2π · sign (signed area)`.

    Proof: the three turn ratios `r₁=(c-b)/(b-a)`, `r₂=(a-c)/(c-b)`,
    `r₃=(b-a)/(a-c)` have product `1`, so by `Complex.arg_mul_coe_angle` the sum
    of their args is `0` in `Real.Angle`, i.e. a multiple of `2π`.  The three
    triangle cross products `cross (b-a)(c-b) = cross (c-b)(a-c) = cross (a-c)(b-a)`
    are all equal to the signed area `HexArea.shoelace2 [a,b,c]` (via
    `HexArea.shoelace2_triple` and `cross_triangle_eq_cross_edges`), so the three
    `Im rᵢ` share the sign of the area, forcing each `arg rᵢ` strictly into
    `(0,π)` (area > 0) or `(-π,0)` (area < 0).  The sum then lies in `(0,3π)` resp.
    `(-3π,0)` and is a multiple of `2π`, hence `±2π`.  This is the base case of the
    ear-clipping induction for `polygon_umlaufsatz`.
-/
lemma polyWind_triangle (a b c : ℂ)
    (hnd : HexArea.cross (b - a) (c - b) ≠ 0) :
    polyWind [a, b, c, a, b]
      = 2 * Real.pi * (if 0 < HexArea.shoelace2 [a, b, c] then 1 else -1) := by
  split_ifs <;> simp_all +decide [ polyWind ];
  · have h_sum : ∃ k : ℤ, Complex.arg ((c - b) / (b - a)) + Complex.arg ((a - c) / (c - b)) + Complex.arg ((b - a) / (a - c)) = k * (2 * Real.pi) := by
      have h_arg_sum : Complex.exp (Complex.I * (Complex.arg ((c - b) / (b - a)) + Complex.arg ((a - c) / (c - b)) + Complex.arg ((b - a) / (a - c)))) = 1 := by
        have h_arg_sum : Complex.exp (Complex.I * Complex.arg ((c - b) / (b - a))) * Complex.exp (Complex.I * Complex.arg ((a - c) / (c - b))) * Complex.exp (Complex.I * Complex.arg ((b - a) / (a - c))) = 1 := by
          have h_arg_sum : Complex.exp (Complex.I * Complex.arg ((c - b) / (b - a))) = (c - b) / (b - a) / ‖(c - b) / (b - a)‖ ∧ Complex.exp (Complex.I * Complex.arg ((a - c) / (c - b))) = (a - c) / (c - b) / ‖(a - c) / (c - b)‖ ∧ Complex.exp (Complex.I * Complex.arg ((b - a) / (a - c))) = (b - a) / (a - c) / ‖(b - a) / (a - c)‖ := by
            have h_arg_sum : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.I * Complex.arg z) = z / ‖z‖ := by
              intro z hz; rw [ Complex.ext_iff ] ; simp +decide [ Complex.exp_re, Complex.exp_im, mul_comm ] ;
              rw [ Complex.cos_arg, Complex.sin_arg ] <;> aesop;
            apply And.intro;
            · apply h_arg_sum;
              simp_all +decide [ sub_eq_iff_eq_add, HexArea.cross ];
              constructor <;> rintro rfl <;> norm_num at *;
            · apply And.intro;
              · apply h_arg_sum;
                simp_all +decide [ HexArea.cross ];
                exact ⟨ sub_ne_zero_of_ne <| by rintro rfl; exact hnd <| by ring, sub_ne_zero_of_ne <| by rintro rfl; exact hnd <| by ring ⟩;
              · apply h_arg_sum;
                simp_all +decide [ sub_eq_iff_eq_add, HexArea.cross ];
                grind +qlia;
          by_cases ha : b - a = 0 <;> by_cases hb : c - b = 0 <;> by_cases hc : a - c = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
          simp +decide [ mul_left_comm ( b - a ), mul_assoc, ha, hb ];
        convert h_arg_sum using 1 ; push_cast [ ← Complex.exp_add ] ; ring;
      rw [ Complex.exp_eq_one_iff ] at h_arg_sum; obtain ⟨ k, hk ⟩ := h_arg_sum; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
    have h_pos : 0 < Complex.im ((c - b) / (b - a)) ∧ 0 < Complex.im ((a - c) / (c - b)) ∧ 0 < Complex.im ((b - a) / (a - c)) := by
      have h_pos : Complex.normSq (b - a) > 0 ∧ Complex.normSq (c - b) > 0 ∧ Complex.normSq (a - c) > 0 := by
        simp_all +decide [ Complex.normSq, HexArea.cross ];
        exact ⟨ not_le.mp fun h => hnd <| by norm_num [ show b = a by refine' Complex.ext _ _ <;> nlinarith ], not_le.mp fun h => hnd <| by norm_num [ show c = b by refine' Complex.ext _ _ <;> nlinarith ], not_le.mp fun h => hnd <| by norm_num [ show a = c by refine' Complex.ext _ _ <;> nlinarith ] ; ring ⟩;
      simp_all +decide [ Complex.div_im, HexArea.shoelace2_triple, cross_triangle_eq_cross_edges ];
      simp_all +decide [ HexArea.cross ];
      exact ⟨ by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr h_pos.1 ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr h_pos.2.1 ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr h_pos.2.2 ) ] ; linarith ⟩;
    have h_arg_pos : ∀ z : ℂ, 0 < z.im → 0 < Complex.arg z ∧ Complex.arg z < Real.pi := by
      intros z hz_pos
      have h_arg_pos : 0 < Complex.arg z := by
        rw [ Complex.arg ];
        split_ifs <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        · nlinarith;
        · linarith [ Real.neg_pi_div_two_le_arcsin ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.arcsin_le_pi_div_two ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.pi_pos ];
        · linarith
      have h_arg_lt_pi : Complex.arg z < Real.pi := by
        rw [ Complex.arg_lt_pi_iff ] ; aesop
      exact ⟨h_arg_pos, h_arg_lt_pi⟩;
    obtain ⟨ k, hk ⟩ := h_sum; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, h_arg_pos _ h_pos.1, h_arg_pos _ h_pos.2.1, h_arg_pos _ h_pos.2.2 ] ;
  · -- Since the imaginary parts of $r₁$, $r₂$, and $r₃$ are negative, their arguments are in $(-π, 0)$.
    have h_arg_neg : Complex.arg ((c - b) / (b - a)) < 0 ∧ Complex.arg ((a - c) / (c - b)) < 0 ∧ Complex.arg ((b - a) / (a - c)) < 0 := by
      have h_im_neg : HexArea.cross (b - a) (c - b) < 0 := by
        exact lt_of_le_of_ne ( by rw [ HexArea.shoelace2_triple ] at *; linarith [ cross_triangle_eq_cross_edges a b c ] ) hnd;
      have h_im_neg : HexArea.cross (c - b) (a - c) < 0 ∧ HexArea.cross (a - c) (b - a) < 0 := by
        unfold HexArea.cross at *; norm_num [ Complex.ext_iff ] at *; constructor <;> linarith;
      simp_all +decide [ Complex.div_im, HexArea.cross ];
      exact ⟨ by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr <| sub_ne_zero.mpr <| by aesop ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr <| sub_ne_zero.mpr <| by aesop ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr <| sub_ne_zero.mpr <| by aesop ) ] ; linarith ⟩;
    -- Since the arguments are in (-π, 0), their sum is a multiple of 2π.
    have h_sum_mul : ∃ k : ℤ, Complex.arg ((c - b) / (b - a)) + Complex.arg ((a - c) / (c - b)) + Complex.arg ((b - a) / (a - c)) = 2 * Real.pi * k := by
      have h_sum_mul : Complex.exp (Complex.I * (Complex.arg ((c - b) / (b - a)) + Complex.arg ((a - c) / (c - b)) + Complex.arg ((b - a) / (a - c)))) = 1 := by
        have h_exp : Complex.exp (Complex.I * Complex.arg ((c - b) / (b - a))) = (c - b) / (b - a) / ‖(c - b) / (b - a)‖ ∧
                       Complex.exp (Complex.I * Complex.arg ((a - c) / (c - b))) = (a - c) / (c - b) / ‖(a - c) / (c - b)‖ ∧
                       Complex.exp (Complex.I * Complex.arg ((b - a) / (a - c))) = (b - a) / (a - c) / ‖(b - a) / (a - c)‖ := by
                         have h_exp : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.I * Complex.arg z) = z / ‖z‖ := by
                           intro z hz; rw [ mul_comm ] ; rw [ Complex.exp_mul_I ] ; simp +decide [ hz, Complex.normSq_eq_norm_sq, Complex.ext_iff ] ;
                           norm_cast; rw [ Complex.cos_arg, Complex.sin_arg ] <;> aesop;
                         refine' ⟨ h_exp _ _, h_exp _ _, h_exp _ _ ⟩ <;> intro h <;> simp_all +decide [ sub_eq_iff_eq_add ];
        simp_all +decide [ mul_add, Complex.exp_add ];
        field_simp;
        rw [ div_self ] ; simp_all +decide [ sub_eq_iff_eq_add ];
        exact ⟨ ⟨ ⟨ ⟨ by aesop_cat, by aesop_cat ⟩, by aesop_cat ⟩, by aesop_cat ⟩, by aesop_cat ⟩;
      rw [ Complex.exp_eq_one_iff ] at h_sum_mul; obtain ⟨ k, hk ⟩ := h_sum_mul; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
    obtain ⟨ k, hk ⟩ := h_sum_mul; rcases k with ( ⟨ _ | _ | k ⟩ | ⟨ _ | _ | k ⟩ ) <;> norm_num at hk <;> nlinarith [ Real.pi_pos, Complex.neg_pi_lt_arg ( ( c - b ) / ( b - a ) ), Complex.arg_le_pi ( ( c - b ) / ( b - a ) ), Complex.neg_pi_lt_arg ( ( a - c ) / ( c - b ) ), Complex.arg_le_pi ( ( a - c ) / ( c - b ) ), Complex.neg_pi_lt_arg ( ( b - a ) / ( a - c ) ), Complex.arg_le_pi ( ( b - a ) / ( a - c ) ) ] ;

/-- The closing append `V ++ [V[0], V[1]]` (used in the public Umlaufsatz
    statement) equals the index-free form `V ++ V.take 2`.  The latter is much
    easier to manipulate under the ear-clipping induction (no dependent index
    proofs), so the induction is carried out on it and transported back here. -/
lemma closeList_eq (V : List ℂ) (h : 2 ≤ V.length) :
    V ++ [V[0]'(by omega), V[1]'(by omega)] = V ++ V.take 2 := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, V = a :: b :: rest := by
    rcases V with (_ | ⟨a, _ | ⟨b, rest⟩⟩) <;> simp_all
  simp [List.take]

/-
**Local ear-step turning telescoping (mod `2π`).**  Reusable preparation for
    the turning equality inside `polygon_ear_reduction`.  Removing a single
    vertex `b` from between its neighbours `a` and `c` (with a preceding vertex
    `p` and a following vertex `q`) replaces the three local turns at `a`, `b`,
    `c` by the two local turns at `a`, `c` of the merged edge `c - a`, and the
    net turning change is a multiple of `2π`.

    Reason: the moduli are positive reals, so `exp (I · arg z)` equals `z / ‖z‖`
    for `z ≠ 0`, and the product of the three original turn ratios telescopes to
    `(q - c) / (a - p)`, which is exactly the product of the two merged turn
    ratios; hence the difference of the two arg-sums has `exp (I · ·) = 1`, i.e.
    is a multiple of `2π`.  Promoting this to an *exact* equality (`k = 0`) is
    the genuinely geometric content supplied by ear convexity inside
    `polygon_ear_reduction`; this lemma isolates the purely algebraic half.
-/
lemma arg_ear_local_mod (p a b c q : ℂ)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0) :
    ∃ k : ℤ,
      (Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
        + Complex.arg ((q - c) / (c - b)))
      - (Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)))
      = 2 * Real.pi * k := by
  -- By definition of exponentiation, we know that if $e^{i\theta} = 1$, then $\theta$ must be an integer multiple of $2\pi$.
  have h_exp : Complex.exp (Complex.I * (Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a)) + Complex.arg ((q - c) / (c - b)) - (Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))))) = 1 := by
    have h_exp : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.I * Complex.arg z) = z / ‖z‖ := by
      intro z hz; rw [ mul_comm ] ; rw [ Complex.ext_iff ] ; simp +decide [ Complex.exp_re, Complex.exp_im, Complex.cos_arg, Complex.sin_arg, hz ] ;
    simp_all +decide [ Complex.exp_sub, Complex.exp_add, mul_add, add_mul, mul_sub, sub_mul ];
    field_simp;
    exact div_self <| by norm_cast; aesop;
  rw [ Complex.exp_eq_one_iff ] at h_exp ; obtain ⟨ k, hk ⟩ := h_exp ; use k ; norm_num [ Complex.ext_iff ] at hk ⊢ ; linarith

/-! ## Rotation invariance of the cyclic invariants (ear-clipping preparation)

The lemmas in this section are **preparation** for a future proof of the
remaining topological core `polygon_ear_reduction` (still a `sorry` below).  An
ear of a simple polygon can lie at any cyclic position; rotating the vertex
cycle so that the ear becomes the *second* vertex turns the abstract ear-clip
into the concrete list operation `a :: b :: c :: rest ↦ a :: c :: rest`.  For
that reduction to transport the cyclic invariants one needs that both the signed
area `HexArea.shoelace2` and the cyclic turning `polyCycWind` are invariant
under cyclic rotation of the vertex list.  That invariance is what we establish
here (sorry-free).  These results are not yet *consumed* by another declaration
(the core they feed is still open), but they are genuine, reusable progress
toward it and are imported in the `SAWFinal` chain via this file. -/

/-- The cyclic total turning of the vertex cycle `V`: the exterior-angle turning
    of the closed polygon, packaged via the `take 2` closing used throughout the
    Umlaufsatz development. -/
def polyCycWind (V : List ℂ) : ℝ := polyWind (V ++ V.take 2)

lemma polyCycWind_def (V : List ℂ) : polyCycWind V = polyWind (V ++ V.take 2) := rfl

/-
Rotating the vertex cycle by one step preserves the signed area: the
    shoelace functional is a sum over the same cyclic edges.
-/
lemma shoelace2_rotate1 (V : List ℂ) :
    HexArea.shoelace2 (V.rotate 1) = HexArea.shoelace2 V := by
  rcases V with ( _ | ⟨ x, _ | ⟨ y, V ⟩ ⟩ ) <;> simp_all +decide [ List.rotate ];
  induction V <;> simp_all +decide [ HexArea.shoelace2 ];
  · ring;
  · rename_i k hk ih;
    cases hk <;> simp_all +decide [ HexArea.shoelaceOpen ] ; ring;
    grind

/-
The signed area is invariant under any cyclic rotation of the vertex list.
-/
lemma shoelace2_rotate (V : List ℂ) (n : ℕ) :
    HexArea.shoelace2 (V.rotate n) = HexArea.shoelace2 V := by
  induction' n with n ih;
  · norm_num [ List.rotate ];
  · convert shoelace2_rotate1 ( V.rotate n ) using 1;
    · rw [ List.rotate_rotate ];
    · exact ih.symm

/-
Rotating the vertex cycle by one step preserves the cyclic turning: it is a
    sum over the same `V.length` cyclic turns, merely reindexed.  Proof: writing
    `V = a :: t` with `2 ≤ t.length`, both closed forms reduce — via
    `polyWind_append_singleton` — to `polyWind (t ++ [a, t[0]])` plus the single
    turn `arg ((t[1] - t[0]) / (t[0] - a))`.
-/
lemma polyCycWind_rotate1 (V : List ℂ) (h : 3 ≤ V.length) :
    polyCycWind (V.rotate 1) = polyCycWind V := by
  obtain ⟨a, t, ht⟩ : ∃ a t, V = a :: t ∧ 2 ≤ t.length := by
    rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | V ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
  rcases t with ( _ | ⟨ b, _ | ⟨ c, t ⟩ ⟩ ) <;> simp_all +decide [ polyCycWind_def ];
  convert polyWind_append_singleton ( b :: c :: ( t ++ [ a, b ] ) ) _ c using 1 <;> norm_num [ List.length ];
  grind +locals

/-
The cyclic turning is invariant under any cyclic rotation of the vertex
    list.
-/
lemma polyCycWind_rotate (V : List ℂ) (n : ℕ) (h : 3 ≤ V.length) :
    polyCycWind (V.rotate n) = polyCycWind V := by
  induction' n with n ih;
  · norm_num;
  · convert polyCycWind_rotate1 ( V.rotate n ) _ using 1;
    · rw [ List.rotate_rotate ];
    · exact ih.symm;
    · rw [ List.length_rotate ] ; linarith

/-
Membership in the closed-edge list is invariant under rotating the vertex
    cycle: rotation cyclically permutes the closed edges, leaving the set of
    edges (as unordered membership) unchanged.  Preparation for
    `PolygonSimple_rotate`.
-/
lemma mem_closedEdges_rotate (V : List ℂ) (n : ℕ) (e : ℂ × ℂ) :
    e ∈ closedEdges (V.rotate n) ↔ e ∈ closedEdges V := by
  unfold closedEdges; simp +decide [ List.mem_iff_getElem ] ;
  constructor <;> rintro ⟨ i, hi, rfl ⟩;
  · use ( i + n ) % V.length; simp +decide [ List.getElem?_rotate, hi ] ;
    simp +decide [ List.getElem_rotate, Nat.mod_lt ];
    exact ⟨ Nat.mod_lt _ ( by linarith ), by ring ⟩;
  · refine' ⟨ ( i + V.length - n % V.length ) % V.length, _, _ ⟩;
    exact Nat.mod_lt _ ( by linarith );
    simp +decide [ List.getElem_rotate, Nat.mod_eq_of_lt hi ];
    constructor <;> congr 1;
    · rw [ tsub_add_eq_add_tsub ];
      · rw [ Nat.ModEq.symm ];
        exact Nat.mod_eq_of_lt hi;
        simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show n % V.length ≤ i + V.length + n from by linarith [ Nat.zero_le ( n % V.length ), Nat.mod_lt n ( by linarith : 0 < V.length ) ] ) ];
      · exact le_trans ( Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) ) ) ( by linarith );
    · simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub ( show n % V.length ≤ i + V.length from le_trans ( Nat.mod_lt _ ( by linarith ) |> Nat.le_of_lt ) ( by linarith ) ) ];
      ring

/-
Planar simplicity (`PolygonSimple`) is invariant under cyclic rotation of
    the vertex list: `Nodup` is rotation invariant (`List.nodup_rotate`) and the
    edge-disjointness clause quantifies only over closed-edge membership, which
    is rotation invariant by `mem_closedEdges_rotate`.  Preparation for the
    ear-clip-by-rotation route to `polygon_ear_reduction`.
-/
lemma PolygonSimple_rotate (V : List ℂ) (n : ℕ) :
    PolygonSimple (V.rotate n) ↔ PolygonSimple V := by
  simp +decide [ PolygonSimple, List.nodup_rotate ];
  grind +suggestions

/-- The cyclic non-degeneracy predicate: every cyclic turn of the closed polygon
    is a genuine (non-flat, non-spike) corner. -/
def polyCycNondeg (V : List ℂ) : Prop := polyNondeg (V ++ V.take 2)

lemma polyCycNondeg_def (V : List ℂ) : polyCycNondeg V = polyNondeg (V ++ V.take 2) := rfl

/-
Cyclic non-degeneracy is invariant under cyclic rotation of the vertex list:
    the cross products of all `V.length` cyclic turns are the same multiset.
    Preparation for the ear-clip-by-rotation route.
-/
lemma polyCycNondeg_rotate1 (V : List ℂ) (h : 3 ≤ V.length) :
    polyCycNondeg (V.rotate 1) ↔ polyCycNondeg V := by
  have h_rotate :polyCycNondeg (V.rotate 1) ↔ polyNondeg ((V.rotate 1) ++ (V.rotate 1).take 2) := by
    rfl;
  obtain ⟨a, b, c, t, rfl⟩ : ∃ a b c t, V = a :: b :: c :: t := by
    rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | V ⟩ ⟩ ⟩ ) <;> norm_num at *;
  rcases t with ( _ | ⟨ d, t ⟩ ) <;> simp_all +decide [ List.rotate ];
  · simp_all +decide [ polyNondeg_cons_cons_cons, polyCycNondeg_def ];
    tauto;
  · have h_split : ∀ (L : List ℂ), polyNondeg (L ++ [a, b, c]) ↔ polyNondeg (L ++ [a, b]) ∧ HexArea.cross (b - a) (c - b) ≠ 0 := by
      intro L; induction L <;> simp_all +decide [ polyNondeg_cons_cons_cons ] ;
      cases ‹List ℂ› <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
      cases ‹List ℂ› <;> simp_all +decide [ polyNondeg_cons_cons_cons ]; all_goals tauto;
    grind +locals

lemma polyCycNondeg_rotate (V : List ℂ) (n : ℕ) (h : 3 ≤ V.length) :
    polyCycNondeg (V.rotate n) ↔ polyCycNondeg V := by
  induction' n with n ih;
  · norm_num [ List.rotate ];
  · convert polyCycNondeg_rotate1 ( V.rotate n ) _ |> Iff.trans <| ih using 1;
    · rw [ List.rotate_rotate ];
    · rw [ List.length_rotate ] ; linarith

/-- Clipping the second vertex changes the signed area by exactly the signed
    area of the cut-off ear triangle `[a, b, c]`.  Immediate from
    `HexArea.shoelace2_ear` and `HexArea.shoelace2_triple`; this is the algebraic
    backbone of the orientation-preservation clause of `exists_ear_clip` (for a
    *convex* ear the triangle area shares the polygon's orientation, so adding it
    preserves the sign). -/
lemma shoelace2_clip_second (a b c : ℂ) (rest : List ℂ) :
    HexArea.shoelace2 (a :: b :: c :: rest)
      = HexArea.shoelace2 (a :: c :: rest) + HexArea.shoelace2 [a, b, c] := by
  rw [HexArea.shoelace2_ear, HexArea.shoelace2_triple]

/-! ## Closed-edge bookkeeping for an ear clip (preparation for `exists_ear_clip`)

The two lemmas below are **preparation** consumed by the planar-simplicity half
of `exists_ear_clip`.  They isolate the purely combinatorial part of removing
the second vertex `b` from a closed cycle `a :: b :: c :: rest`: its closed
edges are the two ear edges `(a,b), (b,c)` followed by a *shared tail*
`M := (c :: rest).zip (rest ++ [a])` (the far edges), and the clipped cycle
`a :: c :: rest` has exactly the new diagonal `(a,c)` followed by the *same*
tail `M`.  This reduces planar-simplicity preservation to a single new
disjointness obligation — that the diagonal `a–c` misses every far edge — while
the far/far disjointness is inherited verbatim from the original polygon. -/

/-
**Closed-edge clip identity.**  Removing the second vertex `b` leaves the
    far edges `M := (c :: rest).zip (rest ++ [a])` untouched, replacing the two
    ear edges `(a,b), (b,c)` by the single diagonal `(a,c)`.  Pure list algebra
    (`closedEdges = V.zip (V.rotate 1)` and `rotate 1` of a `cons`).  Preparation
    for `PolygonSimple_clip` / `exists_ear_clip`.
-/
lemma closedEdges_clip (a b c : ℂ) (rest : List ℂ) :
    closedEdges (a :: b :: c :: rest)
        = (a, b) :: (b, c) :: (c :: rest).zip (rest ++ [a]) ∧
    closedEdges (a :: c :: rest)
        = (a, c) :: (c :: rest).zip (rest ++ [a]) := by
  unfold closedEdges; aesop;

/-
**Planar simplicity is preserved by an ear clip, given diagonal
    disjointness.**  If the cycle `a :: b :: c :: rest` is planar-simple and the
    new diagonal `a–c` is disjoint from every far edge `e ∈ M` that shares no
    endpoint with it, then the clipped cycle `a :: c :: rest` is planar-simple.

    The `Nodup` clause is inherited (`a :: c :: rest` is a sublist of
    `a :: b :: c :: rest`); the far/far disjointness is inherited verbatim (the
    far edges `M` are a common suffix by `closedEdges_clip`); and the only new
    obligation — the diagonal against the far edges — is exactly `hdiag`.
    Preparation for `exists_ear_clip`: producing `hdiag` from an empty convex
    ear is the remaining topological core.
-/
lemma PolygonSimple_clip (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hdiag : ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
       Disjoint (segment ℝ a c) (segment ℝ e.1 e.2)) :
    PolygonSimple (a :: c :: rest) := by
  constructor;
  · have := hsimple.1; simp_all +decide [ List.nodup_cons ] ;
  · obtain ⟨h₁, h₂⟩ := hsimple;
    simp +decide [ closedEdges ] at *;
    grind +splitIndPred

/-- **Same-side emptiness gives diagonal disjointness.**  If every far edge `e`
    of the clip has *both* endpoints strictly on the same side of the base line
    `a–c` (the side test product `cross (c-a) (e.1-a) * cross (c-a) (e.2-a)` is
    positive), then the diagonal `a–c` is disjoint from every far edge that
    shares no endpoint with it — exactly the `hdiag` hypothesis of
    `PolygonSimple_clip`.  Pointwise application of
    `HexArea.segment_disjoint_of_strictSameSide` (with `p,q := a,c`).  This is
    the bridge from the empty-ear same-side condition to planar-simplicity
    preservation; producing the same-side condition from an empty convex ear is
    the remaining topological content of `exists_ear_clip`. -/
lemma diag_disjoint_of_far_sameSide (a c : ℂ) (rest : List ℂ)
    (h : ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       0 < HexArea.cross (c - a) (e.1 - a) * HexArea.cross (c - a) (e.2 - a)) :
    ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
       Disjoint (segment ℝ a c) (segment ℝ e.1 e.2) := by
  intro e he _ _ _ _
  exact HexArea.segment_disjoint_of_strictSameSide a c e.1 e.2 (h e he)

/-- **Same-side emptiness gives diagonal disjointness (guarded form).**  The
    satisfiable variant of `diag_disjoint_of_far_sameSide`: the same-side product
    is only required for the *guarded* far edges (those sharing no endpoint with
    the diagonal `a`–`c`).  This is exactly the form a genuine ear can supply —
    every far vertex of an empty convex ear lies strictly on the far side of the
    diagonal `a`–`c`, so each guarded far edge has both endpoints strictly on the
    same side — and it directly yields the diagonal-disjointness hypothesis of
    `PolygonSimple_clip`.  Pointwise application of
    `HexArea.segment_disjoint_of_strictSameSide`.  This makes the remaining
    topological gap (`exists_front_ear`) an *algebraic* cross-product sign
    condition rather than a segment-disjointness condition. -/
lemma diag_disjoint_of_far_sameSide' (a c : ℂ) (rest : List ℂ)
    (h : ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
       0 < HexArea.cross (c - a) (e.1 - a) * HexArea.cross (c - a) (e.2 - a)) :
    ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
       Disjoint (segment ℝ a c) (segment ℝ e.1 e.2) := by
  intro e he h1 h2 h3 h4
  exact HexArea.segment_disjoint_of_strictSameSide a c e.1 e.2 (h e he h1 h2 h3 h4)

/-- **Cons-triple normal form of any rotation of a length-≥3 cycle.**  Any
    rotation `V.rotate r` of a vertex cycle with at least three vertices has the
    explicit head form `a :: b :: c :: rest`.  This is the bookkeeping step that
    lets `exists_ear_clip` present the chosen ear (at cyclic position `r`) in the
    concrete clipped-cons shape `a :: b :: c :: rest ↦ a :: c :: rest`.
    Preparation for `exists_ear_clip`. -/
lemma rotate_cons_triple (V : List ℂ) (h : 3 ≤ V.length) (r : ℕ) :
    ∃ a b c rest, V.rotate r = a :: b :: c :: rest := by
  have hlen : (V.rotate r).length = V.length := List.length_rotate ..
  rcases hrot : V.rotate r with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rw [hrot] at hlen; simp at hlen; omega
  · rw [hrot] at hlen; simp at hlen; omega
  · rw [hrot] at hlen; simp at hlen; omega
  · exact ⟨a, b, c, rest, rfl⟩

/-
**Exact local turning preservation for an ear clip (range form).**  Removing
    the middle vertex `b` from between its neighbours `a, c` (with preceding
    vertex `p` and following vertex `q`) replaces the three local turns at
    `a, b, c` by the two local turns at `a, c` of the merged edge, and — *given*
    that the three relevant partial arg-sums stay within `(-π, π]` — the net
    turning is exactly preserved (the `k = 0` case of `arg_ear_local_mod`).

    The range hypotheses `hr1, hr2, hr3` are exactly what a *convex* ear of a
    *simple* polygon supplies; isolating the analytic identity here (pure
    `Complex.arg_mul` telescoping: both sides equal `arg ((q-c)/(a-p))`) reduces
    the turning-preservation clause of `exists_ear_clip` to producing those
    bounds from convexity.  Preparation for `exists_ear_clip`.
-/
lemma arg_ear_local_exact (p a b c q : ℂ)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hr1 : Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
              ∈ Set.Ioc (-Real.pi) Real.pi)
    (hr2 : Complex.arg ((c - b) / (a - p)) + Complex.arg ((q - c) / (c - b))
              ∈ Set.Ioc (-Real.pi) Real.pi)
    (hr3 : Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))
              ∈ Set.Ioc (-Real.pi) Real.pi) :
    (Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
        + Complex.arg ((q - c) / (c - b)))
      = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)) := by
  rw [ ← Complex.arg_mul ] <;> norm_num [ hpa, hab, hbc, hcq, hca ];
  · rw [ ← Complex.arg_mul, ← Complex.arg_mul ];
    all_goals simp_all +decide [ div_eq_mul_inv ];
    grind +qlia;
  · exact hr1

/-- **Open-chain local turning difference of an ear clip.**  On an open polygonal
    chain `p :: a :: b :: c :: q :: rest`, removing the middle vertex `b`
    changes the total exterior-angle turning `polyWind` by exactly the local
    5-point difference at the ear (with predecessor `p` and successor `q`): all
    turns from `c` onward are shared and cancel.  Combined with
    `arg_ear_local_exact` (which makes that difference vanish under convexity
    range bounds) this is the turning-preservation step of `exists_ear_clip`.
    Pure `polyWind_cons_cons_cons` unfolding.  Preparation for
    `exists_ear_clip`. -/
lemma polyWind_clip_step (p a b c q : ℂ) (rest : List ℂ) :
    polyWind (p :: a :: b :: c :: q :: rest)
      = polyWind (p :: a :: c :: q :: rest)
        + ((Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
              + Complex.arg ((q - c) / (c - b)))
           - (Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)))) := by
  simp only [polyWind_cons_cons_cons]
  ring

/-- **Planar simplicity is preserved by an ear clip, from the far same-side
    condition (SUPERSEDED form, kept as recorded prep).**  Specialisation of
    `PolygonSimple_clip` in which the diagonal-disjointness hypothesis is
    produced from a *uniform same-side* condition on the far edges via
    `diag_disjoint_of_far_sameSide`.

    **Why it is no longer the consumed interface.**  Its hypothesis `h` requires
    a *strictly positive* side-product for **every** far edge
    `e ∈ (c :: rest).zip (rest ++ [a])`.  But the very first far edge is
    `(c, rest.head)`, whose first endpoint is `c`, giving
    `cross (c-a) (c-a) = 0` and hence side-product `0`, never `> 0`.  So `h` is
    in fact **unsatisfiable**, and an ear cannot supply it.  The genuine,
    satisfiable interface that `exists_front_ear` / `exists_ear_rotation` now
    consume is the per-edge *diagonal-disjointness* clause of `PolygonSimple_clip`
    directly (with shared-endpoint guards), proved per far edge from the
    same-side test via `HexArea.segment_disjoint_of_strictSameSide` only on the
    edges that share no endpoint with the diagonal.  This lemma is retained as a
    correct (but vacuously-hypothesised) statement and as documentation of that
    dead branch. -/
lemma PolygonSimple_clip_of_far_sameSide (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (h : ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       0 < HexArea.cross (c - a) (e.1 - a) * HexArea.cross (c - a) (e.2 - a)) :
    PolygonSimple (a :: c :: rest) :=
  PolygonSimple_clip a b c rest hsimple (diag_disjoint_of_far_sameSide a c rest h)

/-
**Cyclic turning is preserved by an ear clip (bookkeeping core, range
    form).**  For a cycle `a :: b :: c :: rest` with `rest` nonempty (so the
    closing `take 2` lands on `[a,b]` / `[a,c]`), removing the apex `b` leaves
    the cyclic total turning `polyCycWind` unchanged, *provided* the three
    relevant partial arg-sums at the ear stay within `(-π, π]` — exactly the
    bounds a convex ear of a simple polygon supplies (`arg_ear_local_exact`).
    Here `p` is the cyclic predecessor of `a` (`rest.getLast?`) and `q` the
    cyclic successor of `c` (`rest.head?`).  Pure `polyWind` bookkeeping: both
    closed forms peel via `polyWind_cons_cons_cons` and
    `polyWind_append_singleton` to a shared middle `polyWind (c :: rest ++ [a])`
    plus the local ear turns, whose difference vanishes by
    `arg_ear_local_exact`.  This extracts the turning-preservation clause of
    `exists_ear_rotation` from its topological core; producing the range bounds
    from a convex ear is the remaining content.
-/
lemma polyCycWind_clip_eq (a b c p q : ℂ) (rest : List ℂ)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hr1 : Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
              ∈ Set.Ioc (-Real.pi) Real.pi)
    (hr2 : Complex.arg ((c - b) / (a - p)) + Complex.arg ((q - c) / (c - b))
              ∈ Set.Ioc (-Real.pi) Real.pi)
    (hr3 : Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))
              ∈ Set.Ioc (-Real.pi) Real.pi) :
    polyCycWind (a :: c :: rest) = polyCycWind (a :: b :: c :: rest) := by
  cases rest <;> simp_all +decide [ polyCycWind ];
  rename_i k hk;
  have := arg_ear_local_exact p a b c q hpa hab hbc hcq hca hr1 hr2 hr3; simp_all +decide [ polyWind_cons_cons_cons ] ;
  have := polyWind_append_singleton ( c :: q :: ( hk ++ [ a ] ) ) ( by simp +decide [ List.length ] ) b; have := polyWind_append_singleton ( c :: q :: ( hk ++ [ a ] ) ) ( by simp +decide [ List.length ] ) c; simp_all +decide [ List.getLast? ] ;
  grind +qlia

/-- **Cyclic turning is preserved by an ear clip — identity form (the genuine,
    TRUE interface).**  Same conclusion as `polyCycWind_clip_eq`, but it takes
    directly the *local turning identity* of the ear
      `arg((b-a)/(a-p)) + arg((c-b)/(b-a)) + arg((q-c)/(c-b))`
         `= arg((c-a)/(a-p)) + arg((q-c)/(c-a))`
    instead of the three `(-π, π]` partial-sum range bounds.

    **Why this replaces the range-bounds interface.**  The three
    `Set.Ioc (-π) π` bounds (`ear_turning_bounds`) are *false* in general — the
    third bound `arg((c-a)/(a-p)) + arg((q-c)/(c-a)) ∈ (-π, π]` is the sum of two
    of the three exterior turns of the clipped triangle, which for any genuine
    triangle sum to `2π − (third turn) ∈ (π, 2π)`, hence exceed `π`.  The bounds
    were only ever a *sufficient* route to the local identity; the identity
    itself is the true, weaker fact that the ear clip actually needs, and it
    holds for an empty ear of a simple polygon (the two clipped steps do not
    wind).  Pure `polyWind` bookkeeping, identical to `polyCycWind_clip_eq`
    except the local identity is supplied as `hident`. -/
lemma polyCycWind_clip_eq_of_identity (a b c p q : ℂ) (rest : List ℂ)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hident :
        Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
            + Complex.arg ((q - c) / (c - b))
          = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))) :
    polyCycWind (a :: c :: rest) = polyCycWind (a :: b :: c :: rest) := by
  cases rest <;> simp_all +decide [ polyCycWind ];
  rename_i k hk;
  have := hident; simp_all +decide [ polyWind_cons_cons_cons ] ;
  have := polyWind_append_singleton ( c :: q :: ( hk ++ [ a ] ) ) ( by simp +decide [ List.length ] ) b; have := polyWind_append_singleton ( c :: q :: ( hk ++ [ a ] ) ) ( by simp +decide [ List.length ] ) c; simp_all +decide [ List.getLast? ] ;
  grind +qlia

/-- **Orientation is preserved by an ear clip (arithmetic core).**  By
    `shoelace2_clip_second` the signed area of the un-clipped cycle splits as
    `shoelace2 (a::b::c::rest) = shoelace2 (a::c::rest) + shoelace2 [a,b,c]`.
    Hence if the cut-off ear triangle `[a,b,c]` has the *same orientation* as
    the clipped cycle (`0 < shoelace2 [a,b,c] ↔ 0 < shoelace2 (a::c::rest)`) the
    full cycle has that orientation too.  Pure arithmetic on the area splitting;
    this extracts the orientation clause of `exists_ear_rotation` from its
    topological core (the convexity input `0 < shoelace2 [a,b,c] ↔ …`).
    Consumes `shoelace2_clip_second`. -/
lemma shoelace2_orient_clip (a b c : ℂ) (rest : List ℂ)
    (h : (0:ℝ) < HexArea.shoelace2 [a, b, c]
            ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) :
    (0:ℝ) < HexArea.shoelace2 (a :: b :: c :: rest)
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest) := by
  rw [shoelace2_clip_second]
  constructor
  · intro hfull
    by_contra hclip
    have htri : ¬ (0:ℝ) < HexArea.shoelace2 [a, b, c] := fun ht => hclip (h.mp ht)
    push_neg at hclip htri
    linarith
  · intro hclip
    have htri : (0:ℝ) < HexArea.shoelace2 [a, b, c] := h.mpr hclip
    linarith

/-
**A guarded far edge is disjoint from the two ear edges `a–b`, `b–c`
    (simplicity bookkeeping).**  In a planar-simple closed cycle
    `a :: b :: c :: rest`, any far edge `e ∈ (c :: rest).zip (rest ++ [a])`
    sharing no endpoint with the diagonal vertices `a`, `c` also shares no
    endpoint with the apex `b` (by `Nodup`), hence — being a *non-adjacent*
    closed edge — is disjoint as a segment from both ear edges `a–b` and `b–c`.
    Pure `closedEdges` / `PolygonSimple` bookkeeping (`closedEdges_clip`,
    `List.of_mem_zip`).  This is the simplicity input consumed by
    `diag_disjoint_of_empty_corner`: a far edge cannot cross the corner triangle
    boundary along its `a–b` / `b–c` sides.
-/
lemma far_edge_disjoint_earEdges (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (e : ℂ × ℂ) (he : e ∈ (c :: rest).zip (rest ++ [a]))
    (ha1 : a ≠ e.1) (ha2 : a ≠ e.2) (hc1 : c ≠ e.1) (hc2 : c ≠ e.2) :
    Disjoint (segment ℝ a b) (segment ℝ e.1 e.2) ∧
    Disjoint (segment ℝ b c) (segment ℝ e.1 e.2) := by
  have hnd : b ∉ c :: rest ∧ b ∉ rest ++ [a] := by
    cases hsimple ; aesop;
  have := hsimple.2;
  have := List.mem_iff_get.mp he; obtain ⟨ k, hk ⟩ := this; simp_all +decide [ closedEdges ] ;
  grind +splitImp

/-
**Diagonal disjointness from an empty closed corner (pure-geometry heart of
    the Jordan-segment piece).**  Stated for *single points*, free of lists.  If
    the corner triangle `a, b, c` is non-degenerate, the far-edge endpoints `u`,
    `w` are *not strictly inside* the triangle and *not on the closed diagonal
    segment* `a–c`, and the edge `u–w` is disjoint from both polygon edges
    `a–b`, `b–c`, then the diagonal `a–c` is disjoint from `u–w`.

    Proof (the genuine Jordan-curve-segment argument): suppose `z` lies on both
    `a–c` and `u–w`.  If `u, w` are strictly on the same side of line `a–c`, the
    whole edge is, contradicting `z ∈ a–c` (use
    `HexArea.segment_disjoint_of_strictSameSide`).  Otherwise `u–w` crosses line
    `a–c`; the portion of `u–w` on the apex (`b`) side of `a–c` near `z` lies in
    the interior of triangle `a,b,c`, so following it to its apex-side endpoint
    it must leave the triangle either through edge `a–b` or `b–c` (contradicting
    `hDab` / `hDbc`), at an endpoint strictly inside (contradicting
    `hu_in`/`hw_in`), or on the diagonal (contradicting `hu_diag`/`hw_diag`);
    the degenerate collinear case puts `a` or `c` on `u–w`, again contradicting
    `hDab`/`hDbc`.  Absent from Mathlib.

    **Now PROVED sorry-free** (previously the Jordan-segment gap), using the
    constructive plane-geometry toolkit in `RequestProject.SAWUmlaufCorner`:
    `HexArea.corner_exit_point` (the explicit first-crossing argument for the
    generic case) and `HexArea.collinear_diag_a_mem` (the degenerate collinear
    case), together with `HexArea.mem_segment_ab_of_cross` /
    `mem_segment_bc_of_cross` and `HexArea.exists_real_smul_of_cross_zero`. -/
lemma seg_diagonal_disjoint_of_corner (a b c u w : ℂ)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hu_in : ¬ HexArea.inTriangleStrict a b c u)
    (hw_in : ¬ HexArea.inTriangleStrict a b c w)
    (hu_diag : u ∉ segment ℝ a c) (hw_diag : w ∉ segment ℝ a c)
    (hDab : Disjoint (segment ℝ a b) (segment ℝ u w))
    (hDbc : Disjoint (segment ℝ b c) (segment ℝ u w)) :
    Disjoint (segment ℝ a c) (segment ℝ u w) := by
  apply Set.disjoint_left.mpr;
  intro z hz_ac hz_uw
  have hzline : HexArea.cross (c - a) (z - a) = 0 :=
    HexArea.cross_eq_zero_of_mem_segment a c z hz_ac
  have hzac : HexArea.cross (a - c) (z - c) = 0 := by
    convert HexArea.cross_eq_zero_of_mem_segment c a z ( segment_symm ℝ a c ▸ hz_ac ) using 1
  have hzab : 0 < HexArea.cross (b - a) (z - a) * HexArea.cross (b - a) (c - b) := by
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, z = (1 - t) • a + t • c := by
      rw [ segment_eq_image ] at hz_ac; aesop;
    by_cases ht_zero : t = 0 <;> by_cases ht_one : t = 1 <;> simp_all +decide [ HexArea.cross ];
    · exact hDab.le_bot ⟨ left_mem_segment _ _ _, hz_uw ⟩;
    · exact False.elim <| hDbc.le_bot ⟨ by exact right_mem_segment ℝ _ _, hz_uw ⟩;
    · nlinarith [ mul_self_pos.mpr ht_zero, mul_self_pos.mpr ( sub_ne_zero.mpr ht_one ), mul_self_pos.mpr hndtri, mul_pos ( sub_pos.mpr ( lt_of_le_of_ne ht.1.1 ( Ne.symm ht_zero ) ) ) ( sub_pos.mpr ( lt_of_le_of_ne ht.1.2 ht_one ) ) ]
  have hzbc : 0 < HexArea.cross (c - b) (z - b) * HexArea.cross (b - a) (c - b) := by
    obtain ⟨t, ht⟩ : ∃ t : ℝ, z = (1 - t) • a + t • c ∧ 0 ≤ t ∧ t ≤ 1 := by
      rw [ segment_eq_image ] at hz_ac; obtain ⟨ t, ht, rfl ⟩ := hz_ac; exact ⟨ t, rfl, ht.1, ht.2 ⟩ ;
    by_cases ht0 : t = 0 <;> by_cases ht1 : t = 1 <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · simp_all +decide [ HexArea.cross ];
    · exact hDbc.le_bot ⟨ right_mem_segment ℝ b c, hz_uw ⟩;
    · norm_num [ HexArea.cross ] at *;
      nlinarith [ mul_self_pos.mpr hndtri, mul_self_pos.mpr ( sub_ne_zero.mpr ht0 ), mul_self_pos.mpr ( sub_ne_zero.mpr ht1 ) ];
  -- Extract `s` with `z = (1-s)•u + s•w`, `s ∈ [0,1]` (from `segment_eq_image` on `hz_uw`); `z ≠ u ⇒ s > 0` (z ∈ segment ac but u ∉ segment ac ⇒ z ≠ u, from `hu_diag`), `z ≠ w ⇒ s < 1` (from `hw_diag`).
  obtain ⟨s, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = (1 - s) • u + s • w := by
    rw [ segment_eq_image ] at hz_uw; obtain ⟨ s, hs, rfl ⟩ := hz_uw; exact ⟨ s, hs.1, hs.2, rfl ⟩ ;
  have hs_pos : 0 < s := by
    contrapose! hu_diag;
    cases le_antisymm hu_diag hs.1 ; aesop
  have hs_lt_one : s < 1 := by
    cases lt_or_eq_of_le hs.2.1 <;> simp_all +decide [ segment_eq_image ];
    exact hw_diag _ hz_ac.choose_spec.1.1 hz_ac.choose_spec.1.2 hz_ac.choose_spec.2
  have hz_minus_c : z - c = (1 - s) • (u - c) + s • (w - c) := by
    simp +decide [ hs.2.2, smul_sub ] ; ring;
  -- Multiply by `O`: with `Pu := cross (a-c)(u-c) * O`, `Pw := cross (a-c)(w-c) * O`, get `(1-s)*Pu + s*Pw = 0`, `0 < s < 1`.
  set Pu := HexArea.cross (a - c) (u - c) * HexArea.cross (b - a) (c - b)
  set Pw := HexArea.cross (a - c) (w - c) * HexArea.cross (b - a) (c - b)
  have hPuPw : (1 - s) * Pu + s * Pw = 0 := by
    convert congr_arg ( fun x : ℝ => x * HexArea.cross ( b - a ) ( c - b ) ) hzac using 1 ; ring;
    · simp +zetaDelta at *;
      rw [ show -c + z = ( 1 - s ) * ( u - c ) + s * ( w - c ) by linear_combination' hz_minus_c ] ; norm_num [ HexArea.cross ] ; ring;
    · ring;
  by_cases hPu : 0 < Pu;
  · have := HexArea.corner_exit_point a b c z u hndtri hzab hzbc hzac hPu hu_in;
    rcases this with ( ⟨ y, hy₁, hy₂ ⟩ | ⟨ y, hy₁, hy₂ ⟩ ) <;> [ exact hDab.le_bot ⟨ hy₂, by exact Convex.segment_subset ( convex_segment u w ) hz_uw ( left_mem_segment ℝ u w ) hy₁ ⟩ ; exact hDbc.le_bot ⟨ hy₂, by exact Convex.segment_subset ( convex_segment u w ) hz_uw ( left_mem_segment ℝ u w ) hy₁ ⟩ ];
  · by_cases hPw : 0 < Pw;
    · have := HexArea.corner_exit_point a b c z w hndtri hzab hzbc hzac hPw hw_in;
      rcases this with ( ⟨ y, hy₁, hy₂ ⟩ | ⟨ y, hy₁, hy₂ ⟩ ) <;> simp_all +decide [ Set.disjoint_left ];
      · apply hDab hy₂;
        rw [ segment_eq_image ] at *;
        rcases hy₁ with ⟨ θ, hθ, rfl ⟩ ; use ( 1 - θ ) * s + θ; simp +decide [ *, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ] ;
        exact ⟨ ⟨ by nlinarith [ hθ.1, hθ.2 ], by nlinarith [ hθ.1, hθ.2 ] ⟩, by ring ⟩;
      · refine' hDbc hy₂ _;
        rw [ segment_eq_image ] at *;
        rcases hy₁ with ⟨ θ, hθ, rfl ⟩ ; use ( 1 - θ ) * s + θ; simp_all +decide [ sub_smul, add_smul ] ; ring;
        exact ⟨ ⟨ by nlinarith, by nlinarith ⟩, trivial ⟩;
    · -- Since $Pu \leq 0$ and $Pw \leq 0$, we have $Pu = 0$ and $Pw = 0$.
      have hPu_zero : Pu = 0 := by
        nlinarith
      have hPw_zero : Pw = 0 := by
        grind;
      -- Since $Pu = 0$ and $Pw = 0$, we have $cross (a-c)(u-c) = 0$ and $cross (a-c)(w-c) = 0$.
      have hPu_zero' : HexArea.cross (c - a) (u - a) = 0 := by
        simp +zetaDelta at *;
        simp_all +decide [ HexArea.cross ];
        linarith
      have hPw_zero' : HexArea.cross (c - a) (w - a) = 0 := by
        simp_all +decide [ HexArea.cross ];
        grind;
      apply HexArea.collinear_diag_a_mem a c u w z (by
      intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;) hPu_zero' hPw_zero' hz_ac (by
      rintro rfl; simp_all +decide [ HexArea.cross ] ;) (by
      rintro rfl; simp_all +decide [ HexArea.cross ] ;
      grind +splitIndPred) hz_uw hu_diag hw_diag |> fun h => hDab |> fun h' => h'.le_bot ⟨left_mem_segment ℝ a b, h⟩

/-- **An empty corner triangle gives a disjoint diagonal (the Jordan-segment
    piece of the ear clip).**  If the closed cycle `a :: b :: c :: rest` is
    planar-simple, its corner triangle `a, b, c` is non-degenerate
    (`cross (b-a) (c-b) ≠ 0`) with `c ≠ a`, and is *empty* — no far vertex
    `x ∈ rest` lies strictly inside it (`hempty`) nor on the closed diagonal
    `a–c` (`hdiagempty`) — then the diagonal `a–c` is disjoint, as a segment,
    from every far edge `e ∈ (c :: rest).zip (rest ++ [a])` sharing no endpoint
    with it — exactly the `hdiag` hypothesis of `PolygonSimple_clip`.

    Sorry-free assembly: the far-edge endpoints lie in `rest` (guards), so
    `hempty`/`hdiagempty` apply to them; `far_edge_disjoint_earEdges` supplies
    edge disjointness from `a–b`, `b–c`; the pure-geometry heart
    `seg_diagonal_disjoint_of_corner` concludes.  Recorded partial progress:
    consumed by `exists_front_ear` below. -/
lemma diag_disjoint_of_empty_corner (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0) (hca : c - a ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiagempty : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
       Disjoint (segment ℝ a c) (segment ℝ e.1 e.2) := by
  intro e he ha1 ha2 hc1 hc2
  obtain ⟨he1, he2⟩ := List.of_mem_zip he
  have hu_rest : e.1 ∈ rest := by
    rcases List.mem_cons.mp he1 with h | h
    · exact absurd h.symm hc1
    · exact h
  have hw_rest : e.2 ∈ rest := by
    rcases List.mem_append.mp he2 with h | h
    · exact h
    · simp only [List.mem_singleton] at h; exact absurd h.symm ha2
  obtain ⟨hDab, hDbc⟩ :=
    far_edge_disjoint_earEdges a b c rest hsimple e he ha1 ha2 hc1 hc2
  exact seg_diagonal_disjoint_of_corner a b c e.1 e.2 hndtri
    (hempty _ hu_rest) (hempty _ hw_rest)
    (hdiagempty _ hu_rest) (hdiagempty _ hw_rest) hDab hDbc

/-
**Cyclic non-degeneracy is preserved by an ear clip (combinatorial glue).**
    Removing the ear `b` from the cyclic polygon `a :: b :: c :: rest` replaces
    the three corners at `a` (`p,a,b`), `b` (`a,b,c`) and `c` (`b,c,q`) by the
    two new diagonal corners at `a` (`p,a,c`) and `c` (`a,c,q`), where `p` is
    the cyclic predecessor of `a` (the last vertex of `rest`) and `q` is the
    cyclic successor of `c` (the head of `rest`); every other cyclic corner is
    untouched.  Hence if the original cycle is cyclically non-degenerate
    (`hnd`) and the two new diagonal corners are non-flat
    (`hpa : cross (a-p) (c-a) ≠ 0`, `hcq : cross (c-a) (q-c) ≠ 0`), the clipped
    cycle `a :: c :: rest` is cyclically non-degenerate too.

    Pure list/`polyNondeg` bookkeeping (the two closing forms `… ++ [a,b]` and
    `… ++ [a,c]` share every triple except the two diagonal ones).  This is the
    combinatorial brick that turns the geometric non-flatness facts
    `HexArea.clip_turn_at_a_ne_zero` / `HexArea.clip_turn_at_c_ne_zero` into the
    `polyCycNondeg (a :: c :: rest)` clause required by
    `exists_empty_convex_ear_avoiding`.  Recorded preparation.
-/
lemma polyCycNondeg_clip (a b c p q : ℂ) (rest : List ℂ)
    (hq : rest.head? = some q) (hp : rest.getLast? = some p)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hpa : HexArea.cross (a - p) (c - a) ≠ 0)
    (hcq : HexArea.cross (c - a) (q - c) ≠ 0) :
    polyCycNondeg (a :: c :: rest) := by
  rcases rest with ( _ | ⟨ q, _ | ⟨ p, rest ⟩ ⟩ ) <;> simp_all +decide [ polyCycNondeg_def ];
  · simp_all +decide [ polyNondeg_cons_cons_cons ];
  · have h_polyNondeg : ∀ (L : List ℂ) (x y : ℂ), polyNondeg (L ++ [a, y]) → HexArea.cross (a - L.getLast!) (x - a) ≠ 0 → polyNondeg (L ++ [a, x]) := by
      intros L x y hL hxy
      induction' L with L ih generalizing x y;
      · trivial;
      · rcases ih with ( _ | ⟨ a, _ | ⟨ b, ih ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
        grind;
    grind +locals

/-
**A chosen vertex can be rotated to the middle (second) cyclic position.**
    If `v` is a vertex of the cycle `V` and `3 ≤ V.length`, some cyclic rotation
    of `V` has the form `a :: v :: c :: rest`, i.e. it places `v` at index `1`
    with its cyclic predecessor `a` at the front and cyclic successor `c` next.
    Pure `List.rotate` index bookkeeping (`List.head?_rotate`,
    `List.getElem?`).  This is the combinatorial brick that lets the ear search
    normalise the extreme (lex-min) vertex to the ear-tip position required by
    `exists_empty_convex_ear_avoiding`.  Recorded preparation.
-/
lemma exists_rotate_mid (V : List ℂ) (v : ℂ) (hv : v ∈ V) (h3 : 3 ≤ V.length) :
    ∃ (r : ℕ) (a c : ℂ) (rest : List ℂ), V.rotate r = a :: v :: c :: rest := by
  obtain ⟨ i, hi ⟩ := List.mem_iff_getElem.mp hv;
  -- Choose the rotation amount r := (i + V.length - 1) % V.length.
  set r := (i + V.length - 1) % V.length;
  -- By definition of rotation, we have that (V.rotate r)[1]? = some v.
  have h_rotate : (V.rotate r)[1]? = some v := by
    rw [ List.getElem?_rotate ];
    · convert hi.2 ▸ List.getElem?_eq_getElem ( show i < V.length from hi.1 ) using 1;
      rw [ show ( 1 + r ) % V.length = i % V.length from ?_ ];
      · rw [ Nat.mod_eq_of_lt hi.1 ];
      · simp +zetaDelta at *;
        rw [ add_tsub_cancel_of_le ( by linarith [ hi.1 ] ) ] ; norm_num [ Nat.add_mod, Nat.mod_eq_of_lt hi.1 ];
    · linarith;
  rcases n : V.rotate r with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, rest ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  · replace n := congr_arg List.length n ; simp_all +decide;
  · exact ⟨ r, a, c, rest, n ⟩

/-
**Empty-corner ⟹ full ear data (the assembler / bookkeeping step).**
    Given a corner `a, b, c` of the cyclic polygon `a :: b :: c :: rest` that is
    *empty* (no far vertex strictly inside the triangle (`hempty`) nor on the
    closed diagonal `a–c` (`hdiag`)), whose two **clip corners** are non-flat
    (`hclipa : cross (a-p) (c-a) ≠ 0`, `hclipc : cross (c-a) (q-c) ≠ 0`, with
    `p` the cyclic predecessor of `a` and `q` the cyclic successor of `c`), and
    whose ear triangle shares the clip orientation (`horient`), this assembles
    the full post-rotation ear-data conjunction required by
    `exists_empty_convex_ear_avoiding`.

    All twelve clauses are pure bookkeeping over the already-proved bricks: the
    five cyclic edge non-degeneracies and `cross (b-a) (c-b) ≠ 0` are read off
    `polyCycNondeg (a :: b :: c :: rest)`; `c - a ≠ 0` is forced by `hclipa`
    (a zero second factor makes the cross vanish); and the clipped cycle's
    non-degeneracy `polyCycNondeg (a :: c :: rest)` is exactly `polyCycNondeg_clip`.
    This factors the genuine remaining content of the Umlaufsatz core down to
    the *search* for such an empty non-flat corner.  Consumed by
    `exists_empty_convex_ear_avoiding` below.
-/
lemma ear_data_of_empty_corner (a b c p q : ℂ) (rest : List ℂ)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hclipa : HexArea.cross (a - p) (c - a) ≠ 0)
    (hclipc : HexArea.cross (c - a) (q - c) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))) :
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  refine' ⟨ hp, hq, _, _, _, _, _, _, hempty, hdiag, _, horient ⟩;
  all_goals contrapose! hclipa; simp_all +decide [ HexArea.cross ];
  · contrapose! hnd; simp_all +decide [ sub_eq_iff_eq_add, polyCycNondeg_def, polyNondeg_cons_cons_cons ] ;
    unfold HexArea.cross; aesop;
  · simp_all +decide [ polyCycNondeg_def, polyNondeg_cons_cons_cons ];
    simp_all +decide [ HexArea.cross ];
  · contrapose! hnd; simp_all +decide [ polyCycNondeg_def, polyNondeg_cons_cons_cons ] ;
    unfold HexArea.cross; aesop;
  · contrapose! hclipa;
    exact polyCycNondeg_clip a b c p q rest hq hp hnd hclipa hclipc

/- **The Meisters empty-corner search (the single remaining open core).**
    A simple, non-degenerate polygon with `≥ 4` vertices and any forbidden
    vertex `z` has a cyclic rotation `V.rotate r = a :: b :: c :: rest` whose
    middle vertex `b ≠ z` spans an *empty* corner triangle `a b c` (no far
    vertex strictly inside (`hempty`) and none on the closed diagonal `a–c`
    (`hdiag`)), whose two clip corners `(p,a,c)`, `(a,c,q)` are non-flat
    (`cross (a-p) (c-a) ≠ 0`, `cross (c-a) (q-c) ≠ 0`), and whose ear triangle
    shares the clip orientation.

    This is the *geometric heart* of the discrete Umlaufsatz — the Meisters
    "two-ears" theorem in its inductive forbidden-vertex packaging — and is the
    only remaining `sorry` in the whole Umlaufsatz chain.  Intended route:
    strong induction on `V.length`; choose the lex-minimal (hence convex)
    vertex via `HexArea.exists_lex_min_mem` / `lexMin_not_inTriangleStrict` and
    rotate it to the middle via `exists_rotate_mid`; if its corner is empty use
    it (or a cyclic neighbour, to dodge `z`); otherwise pivot to the vertex
    farthest from the base diagonal (`HexArea.exists_max_cross`,
    `farthest_region_empty`, `inTriangleStrict_pos_nest`,
    `subTri_axc_orient_pos`, `inTriangleStrict_apex_sameSide`), split along the
    resulting interior diagonal and recurse on the strictly shorter
    sub-polygons.  This is Jordan-curve-theorem-level content absent from
    Mathlib.  Consumed by `exists_empty_convex_ear_avoiding`. -/
/-- **The conclusion predicate of the Meisters empty-corner search.**  This is
    the existential conclusion of `exists_empty_corner_avoiding` packaged as a
    named predicate so the strong-induction wrapper and the geometric reduction
    step can both refer to it (and to the induction hypothesis quantified over
    it).  It unfolds *definitionally* to the original existential, so all
    downstream consumers that `obtain` against `exists_empty_corner_avoiding`
    are unaffected. -/
def EmptyCornerData (V : List ℂ) (z : ℂ) : Prop :=
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      HexArea.cross (a - p) (c - a) ≠ 0 ∧ HexArea.cross (c - a) (q - c) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))

/-- **Cyclic edge predicate.**  `x` and `y` are endpoints of a cyclic edge of
    the closed polygon with vertex cycle `V` (in either order).  This is the
    "forbidden adjacent pair" carried by the genuine Meisters TWO-ears induction
    `meisters_reduction2`: the single-forbidden form `EmptyCornerData` is *not*
    strong enough to drive the split-and-recurse induction (a returned
    sub-polygon ear may sit at *either* endpoint of the cut diagonal, and a
    single forbidden vertex can exclude only one of them).  The correct
    inductive invariant forbids the *whole cut edge* — which is always a genuine
    cyclic edge of the strictly-shorter sub-polygon, so the recursion stays
    within this predicate. -/
def IsCycEdge (V : List ℂ) (x y : ℂ) : Prop :=
    (x, y) ∈ closedEdges V ∨ (y, x) ∈ closedEdges V

/-- **The TWO-forbidden-vertex empty-corner predicate (the sound inductive
    invariant).**  Identical to `EmptyCornerData` but the empty-ear tip `b`
    avoids *both* forbidden vertices `z1, z2`.  Together with the side condition
    `z1 = z2 ∨ IsCycEdge V z1 z2` this is exactly the inductive packaging of
    Meisters' two-ears theorem that the split-and-recurse induction preserves:
    the interior branch recurses on a sub-polygon forbidding the cut diagonal
    `{b, w}` (a cyclic edge of that sub-polygon), and the empty branch recurses
    on the clip forbidding the clip diagonal `{a, c}` (a cyclic edge of the
    clip).  The single-forbidden `EmptyCornerData` is recovered by taking
    `z1 = z2 = z` (see `EmptyCornerData_of_two`). -/
def EmptyCornerData2 (V : List ℂ) (z1 z2 : ℂ) : Prop :=
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z1 ∧ b ≠ z2 ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      HexArea.cross (a - p) (c - a) ≠ 0 ∧ HexArea.cross (c - a) (q - c) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))

/-- The single-forbidden `EmptyCornerData` is the diagonal case `z1 = z2` of the
    two-forbidden predicate. -/
lemma EmptyCornerData_of_two (V : List ℂ) (z : ℂ) (h : EmptyCornerData2 V z z) :
    EmptyCornerData V z := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, hbz, _, hp, hq, hpa, hqc, hempty, hdiag,
      horient⟩ := h
  exact ⟨r, a, b, c, p, q, rest, hrot, hbz, hp, hq, hpa, hqc, hempty, hdiag,
    horient⟩

/-
**Meisters Step 1 (the convex extreme-vertex setup), proved sorry-free.**
    Any polygon with `≥ 3` vertices has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose middle vertex `b` is the
    lexicographically minimal (leftmost-lowest) vertex of `V`, hence a *convex*
    corner: `b` is never in the strict interior of any triangle spanned by three
    vertices of `V`.  This packages the first step of the Meisters ear search
    (`exists_lex_min_mem` + `lexMin_not_inTriangleStrict` + `exists_rotate_mid`)
    as a single reusable rotation lemma to be consumed by the eventual proof of
    `meisters_reduction`.  It is intentionally not yet referenced by another
    declaration only because the geometric core it feeds is still open — this is
    recorded partial progress, not a dead branch.
-/
lemma exists_lexmin_mid_rotation (V : List ℂ) (h3 : 3 ≤ V.length) :
    ∃ (r : ℕ) (a b c : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ∈ V ∧
      (∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b) ∧
      (∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w) ∧
      (∃ d : ℂ, ∀ y ∈ V, y ≠ b → 0 < HexArea.cdot d (y - b)) := by
  -- By `exists_lex_min_mem`, there exists a lexicographically minimal vertex `v` in `V`.
  obtain ⟨v, hv_mem, hv_lex_min⟩ : ∃ v ∈ V, ∀ w ∈ V, v.re < w.re ∨ (v.re = w.re ∧ v.im ≤ w.im) := by
    obtain ⟨ v, hv ⟩ := HexArea.exists_lex_min_mem V ( by aesop_cat );
    use v;
  obtain ⟨ r, a, c, rest, hr ⟩ := exists_rotate_mid V v hv_mem h3;
  refine' ⟨ r, a, v, c, rest, hr, hv_mem, _, _, _ ⟩;
  · intros x y w hx hy hw h_in_triangle;
    apply HexArea.lexMin_not_inTriangleStrict V v hv_lex_min x y w hx hy hw h_in_triangle
  · intros u w hu hw hvu hvw;
    exact HexArea.lexMin_not_mem_segment V v hv_lex_min u w hu hw hvu hvw
  · exact HexArea.exists_dir_of_lexMin V v hv_lex_min

/-- **Farthest interior vertex (a true, reusable building block).**  If the
    corner triangle `a, b, c` contains at least one vertex of `rest` in its
    strict interior, then among those interior vertices there is one, `w`, that
    is *farthest from the base diagonal* `a–c` (maximising `cross (c-a) (·-a)`).
    This is exactly the pivot vertex of Meisters' diagonal split.  Proved
    sorry-free from `HexArea.exists_max_cross` applied to the sublist of
    interior vertices.  Consumed by `meisters_reduction` (interior branch). -/
lemma exists_farthest_interior (a b c : ℂ) (rest : List ℂ)
    (hne : ∃ x ∈ rest, HexArea.inTriangleStrict a b c x) :
    ∃ w ∈ rest, HexArea.inTriangleStrict a b c w ∧
      ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) ≤ HexArea.cross (c - a) (w - a) := by
  classical
  set S : List ℂ := rest.filter (fun x => decide (HexArea.inTriangleStrict a b c x)) with hS
  have hSne : S ≠ [] := by
    obtain ⟨x, hx, hxin⟩ := hne
    intro hSempty
    have : x ∈ S := by
      rw [hS, List.mem_filter]; exact ⟨hx, by simpa using hxin⟩
    rw [hSempty] at this; simpa using this
  obtain ⟨w, hwS, hwmax⟩ := HexArea.exists_max_cross (c - a) a S hSne
  have hwrest : w ∈ rest := by
    have := (List.mem_filter.mp (hS ▸ hwS)).1; exact this
  have hwin : HexArea.inTriangleStrict a b c w := by
    have := (List.mem_filter.mp (hS ▸ hwS)).2; simpa using this
  refine ⟨w, hwrest, hwin, ?_⟩
  intro y hy hyin
  apply hwmax
  rw [hS, List.mem_filter]; exact ⟨hy, by simpa using hyin⟩

/-- **Orientation-robust farthest interior vertex (the pivot consumed by
    `interior_chord_is_diagonal`).**  Like `exists_farthest_interior`, but the
    selected `w` maximises the *orientation-normalised* `b`-weight
    `cross (c-a) (·-a) * cross (c-a) (b-a)` rather than the bare signed distance
    `cross (c-a) (·-a)`.  This is the genuinely "farthest from `a–c`" pivot for
    *both* triangle orientations (see the orientation note on
    `interior_chord_is_diagonal`); `exists_farthest_interior` coincides with it
    only when `cross (c-a) (b-a) > 0`.  Proved sorry-free by applying
    `HexArea.exists_max_cross` in the rescaled direction
    `d := cross (c-a) (b-a) • (c-a)`, for which
    `cross d (·-a) = cross (c-a) (·-a) * cross (c-a) (b-a)`. -/
lemma exists_farthest_interior_oriented (a b c : ℂ) (rest : List ℂ)
    (hne : ∃ x ∈ rest, HexArea.inTriangleStrict a b c x) :
    ∃ w ∈ rest, HexArea.inTriangleStrict a b c w ∧
      ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) * HexArea.cross (c - a) (b - a)
          ≤ HexArea.cross (c - a) (w - a) * HexArea.cross (c - a) (b - a) := by
  classical
  set S : List ℂ := rest.filter (fun x => decide (HexArea.inTriangleStrict a b c x)) with hS
  have hSne : S ≠ [] := by
    obtain ⟨x, hx, hxin⟩ := hne
    intro hSempty
    have : x ∈ S := by
      rw [hS, List.mem_filter]; exact ⟨hx, by simpa using hxin⟩
    rw [hSempty] at this; simpa using this
  obtain ⟨w, hwS, hwmax⟩ :=
    HexArea.exists_max_cross (HexArea.cross (c - a) (b - a) • (c - a)) a S hSne
  have hconv : ∀ x : ℂ,
      HexArea.cross (HexArea.cross (c - a) (b - a) • (c - a)) (x - a)
        = HexArea.cross (c - a) (x - a) * HexArea.cross (c - a) (b - a) := by
    intro x; unfold HexArea.cross; simp [Complex.ext_iff]; ring
  have hwrest : w ∈ rest := (List.mem_filter.mp (hS ▸ hwS)).1
  have hwin : HexArea.inTriangleStrict a b c w := by
    have := (List.mem_filter.mp (hS ▸ hwS)).2; simpa using this
  refine ⟨w, hwrest, hwin, ?_⟩
  intro y hy hyin
  have := hwmax y (by rw [hS, List.mem_filter]; exact ⟨hy, by simpa using hyin⟩)
  rw [hconv, hconv] at this
  exact this

/-- **A point off the supporting line of a segment is not on the segment.**  If
    `cross (c - a) (x - a) ≠ 0` (i.e. `x` is not collinear with `a` and `c`)
    then `x ∉ segment ℝ a c`.  Reusable building block for the diagonal-clearness
    clause of `EmptyCornerData`. -/
lemma not_mem_segment_of_cross_ne (a c x : ℂ)
    (h : HexArea.cross (c - a) (x - a) ≠ 0) : x ∉ segment ℝ a c := by
  intro hx
  rw [segment_eq_image] at hx
  obtain ⟨t, _, rfl⟩ := hx
  apply h
  simp only [HexArea.cross, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-
**The standard segment-crossing criterion.**  If `c` and `d` are on
    strictly opposite sides of the line `a–b` (`cross (b-a)(c-a)` and
    `cross (b-a)(d-a)` have opposite signs, i.e. their product is negative) and
    `a` and `b` are on strictly opposite sides of the line `c–d`, then the closed
    segments `[a,b]` and `[c,d]` meet (they are not disjoint).  The common point
    is the unique intersection of the two (non-parallel) supporting lines, given
    by Cramer's rule; the opposite-side hypotheses force its two parameters into
    `(0,1)`.  Reusable; consumed by `quad_diagonal_interior`.
-/
lemma segments_cross (a b c d : ℂ)
    (h1 : HexArea.cross (b - a) (c - a) * HexArea.cross (b - a) (d - a) < 0)
    (h2 : HexArea.cross (d - c) (a - c) * HexArea.cross (d - c) (b - c) < 0) :
    ¬ Disjoint (segment ℝ a b) (segment ℝ c d) := by
  -- Let $u = \text{cross}(b-a, c-a)$ and $v = \text{cross}(b-a, d-a)$.
  set u := HexArea.cross (b - a) (c - a)
  set v := HexArea.cross (b - a) (d - a);
  -- By definition of $u$ and $v$, we know that $u \neq 0$ and $v \neq 0$, and $u \neq v$.
  have hu_ne_zero : u ≠ 0 := by
    aesop_cat
  have hv_ne_zero : v ≠ 0 := by
    aesop
  have hu_ne_v : u ≠ v := by
    nlinarith [ mul_self_pos.2 hu_ne_zero, mul_self_pos.2 hv_ne_zero ];
  -- Let $s = \frac{u}{u - v}$ and $t = \frac{u'}{u' - v'}$, where $u' = \text{cross}(d-c, a-c)$ and $v' = \text{cross}(d-c, b-c)$.
  set u' := HexArea.cross (d - c) (a - c)
  set v' := HexArea.cross (d - c) (b - c)
  set s := u / (u - v)
  set t := u' / (u' - v');
  -- By definition of $s$ and $t$, we know that $0 < s < 1$ and $0 < t < 1$.
  have hs_bounds : 0 < s ∧ s < 1 := by
    cases lt_or_gt_of_ne hu_ne_zero <;> cases lt_or_gt_of_ne hv_ne_zero <;> constructor <;> nlinarith [ div_mul_cancel₀ u ( sub_ne_zero_of_ne hu_ne_v ) ]
  have ht_bounds : 0 < t ∧ t < 1 := by
    by_cases hu'_pos : 0 < u';
    · exact ⟨ div_pos hu'_pos ( by nlinarith ), by rw [ div_lt_iff₀ ] <;> nlinarith ⟩;
    · exact ⟨ div_pos_of_neg_of_neg ( lt_of_le_of_ne ( le_of_not_gt hu'_pos ) ( by aesop_cat ) ) ( by nlinarith ), by rw [ div_lt_iff_of_neg ] <;> nlinarith ⟩;
  -- By definition of $s$ and $t$, we know that $P = c + s • (d - c)$ and $P = a + t • (b - a)$.
  have hP_eq : c + s • (d - c) = a + t • (b - a) := by
    simp +zetaDelta at *;
    rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, add_div', add_div' ];
    · rw [ div_eq_div_iff ] <;> norm_cast;
      · norm_num [ Complex.ext_iff, HexArea.cross ] at *;
        constructor <;> ring;
      · exact sub_ne_zero_of_ne hu_ne_v;
      · exact sub_ne_zero_of_ne <| by aesop_cat;
    · exact_mod_cast sub_ne_zero_of_ne <| by aesop;
    · exact_mod_cast sub_ne_zero_of_ne hu_ne_v;
  rw [ Set.not_disjoint_iff ];
  use c + s • (d - c);
  rw [ segment_eq_image', segment_eq_image' ];
  exact ⟨ ⟨ t, ⟨ by linarith, by linarith ⟩, hP_eq.symm ⟩, ⟨ s, ⟨ by linarith, by linarith ⟩, rfl ⟩ ⟩

/-
**The interior-diagonal dichotomy for a simple quadrilateral (the genuine
    `n = 4` Jordan content).**  For a non-degenerate simple quadrilateral
    `a, b, c, d` (the four consecutive triples non-collinear, and the two pairs
    of opposite edges `a–b`/`c–d` and `b–c`/`d–a` disjoint), at least one of the
    two diagonals is *interior*: either `b, d` are on strictly opposite sides of
    the line `a–c`, or `a, c` are on strictly opposite sides of the line `b–d`.
    The edge-disjointness hypotheses are essential (a self-intersecting
    quadrilateral has neither diagonal interior).  Consumed by
    `meisters_reduction_quad`.
-/
lemma quad_diagonal_interior (a b c d : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (hdisj1 : Disjoint (segment ℝ a b) (segment ℝ c d))
    (hdisj2 : Disjoint (segment ℝ b c) (segment ℝ d a)) :
    HexArea.cross (c - a) (b - a) * HexArea.cross (c - a) (d - a) < 0 ∨
      HexArea.cross (d - b) (a - b) * HexArea.cross (d - b) (c - b) < 0 := by
  by_contra h;
  obtain ⟨z, x, y, w, hz, hx, hy, hw⟩ : ∃ z x y w : ℝ, z = HexArea.cross (b - a) (c - a) ∧ x = HexArea.cross (c - a) (d - a) ∧ y = HexArea.cross (d - b) (a - b) ∧ w = HexArea.cross (c - b) (d - b) ∧ z ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ w ≠ 0 := by
    simp_all +decide [ HexArea.cross ];
    grind;
  have h_signs : x * z < 0 ∧ y * w < 0 := by
    simp_all +decide [ mul_comm, HexArea.cross ];
    exact ⟨ lt_of_le_of_ne ( by linarith ) ( by aesop ), lt_of_le_of_ne ( by linarith ) ( by aesop ) ⟩;
  have h_cases : (z * y < 0 ∧ x * w < 0) ∨ (w * z < 0 ∧ y * x < 0) := by
    cases lt_or_gt_of_ne hw.2.1 <;> cases lt_or_gt_of_ne hw.2.2.1 <;> cases lt_or_gt_of_ne hw.2.2.2.1 <;> cases lt_or_gt_of_ne hw.2.2.2.2 <;> first | left; constructor <;> nlinarith | right; constructor <;> nlinarith;
  cases' h_cases with h_case1 h_case2;
  · apply segments_cross a b c d;
    · simp_all +decide [ HexArea.cross ];
      nlinarith;
    · convert h_case1.2 using 1 ; ring;
      rw [ hx, hw.1 ] ; unfold HexArea.cross; norm_num [ Complex.ext_iff ] ; ring;
    · exact hdisj1;
  · apply segments_cross b c d a;
    · simp_all +decide [ HexArea.cross ];
      nlinarith;
    · unfold HexArea.cross at *; norm_num [ Complex.ext_iff ] at *;
      grind;
    · exact hdisj2

/-
**The quadrilateral base case of the Meisters search.**  A simple,
    non-degenerate polygon with exactly four vertices, together with any
    forbidden vertex `z`, has an empty corner avoiding `z`.  This is the genuine
    base case of the strong induction in `exists_empty_corner_avoiding_aux`: a
    split of a quadrilateral produces length-3 sub-polygons, to which the
    induction hypothesis (which requires `≥ 4` vertices) does not apply, so the
    quadrilateral must be handled directly by the (finite) two-ears fact for
    quadrilaterals.

    **Retained as reference (not on the critical path).**  The single-forbidden
    base case is now *superseded* by the two-forbidden `meisters_reduction_quad2`
    (which the sound induction `meisters_reduction2` actually consumes).  This
    proof is kept because the four ear-package proofs `quad_ear_at_a/b/c/d` (and
    hence `meisters_reduction_quad2`) are modelled directly on its four
    finite branches; it documents the geometry and is preparation for future
    reuse.
-/
lemma meisters_reduction_quad (V : List ℂ) (h4 : V.length = 4)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z : ℂ) :
    EmptyCornerData V z := by
  rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | V ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  -- Extract the four consecutive-triple non-degeneracies from `hnd`.
  obtain ⟨hab, hbc, hcd, hda⟩ : HexArea.cross (b - a) (c - b) ≠ 0 ∧ HexArea.cross (c - b) (d - c) ≠ 0 ∧ HexArea.cross (d - c) (a - d) ≠ 0 ∧ HexArea.cross (a - d) (b - a) ≠ 0 := by
    unfold polyCycNondeg at hnd; simp_all +decide [ polyNondeg ] ;
  obtain ⟨hdisj1, hdisj2⟩ : Disjoint (segment ℝ a b) (segment ℝ c d) ∧ Disjoint (segment ℝ b c) (segment ℝ d a) := by
    have := hsimple.2; simp_all +decide [ closedEdges ] ;
    grind +locals;
  obtain H | H := quad_diagonal_interior a b c d hab hbc hcd hda hdisj1 hdisj2;
  · by_cases hbz : b = z;
    · use 2, c, d, a, b, b, [b];
      simp_all +decide [ HexArea.inTriangleStrict ];
      refine' ⟨ _, _, _, _, _, _ ⟩;
      all_goals norm_num [ HexArea.cross, HexArea.shoelace2 ] at *;
      any_goals contrapose! hab; linarith;
      · grind;
      · constructor <;> intros <;> nlinarith;
      · exact fun h => hab <| by rw [ segment_eq_image ] at h; obtain ⟨ t, ht, rfl ⟩ := h; norm_num; ring;
      · constructor <;> intro <;> nlinarith;
    · refine' ⟨ 0, a, b, c, d, d, [ d ], _, _, _, _ ⟩ <;> simp_all +decide [ List.rotate ];
      refine' ⟨ _, _, _, _, _ ⟩;
      · grind +suggestions;
      · unfold HexArea.cross at * ; simp_all +decide [ Complex.ext_iff ];
        grind;
      · exact fun h => H.not_ge <| by nlinarith [ HexArea.inTriangleStrict_apex_sameSide a b c d h ] ;
      · exact not_mem_segment_of_cross_ne a c d ( by aesop );
      · unfold HexArea.shoelace2; simp +decide [ HexArea.cross ] ;
        unfold HexArea.cross at H; simp_all +decide [ Complex.ext_iff ] ;
        constructor <;> intro <;> nlinarith;
  · by_cases hcz : c = z;
    · use 3, d, a, b, c, c, [c];
      simp_all +decide [ HexArea.inTriangleStrict ];
      refine' ⟨ _, _, _, _, _ ⟩;
      · rintro rfl; simp_all +decide [ HexArea.cross ];
        grind;
      · simp_all +decide [ HexArea.cross ];
        grind;
      · simp_all +decide [ HexArea.cross ];
        grind +qlia;
      · unfold HexArea.cross at *; norm_num [ Complex.ext_iff ] at *;
        constructor <;> intros <;> nlinarith;
      · constructor;
        · intro h;
          obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := h;
          simp_all +decide [ HexArea.cross ];
          grind;
        · unfold HexArea.shoelace2; simp +decide [ HexArea.cross ] ;
          unfold HexArea.cross at *; norm_num [ Complex.ext_iff ] at *;
          constructor <;> intro <;> nlinarith;
    · use 1, b, c, d, a, a, [a];
      unfold HexArea.inTriangleStrict; simp_all +decide [ HexArea.cross ] ;
      refine' ⟨ _, _, _, _, _ ⟩;
      · grind +qlia;
      · grind;
      · constructor <;> intros <;> nlinarith;
      · exact fun h => hda <| by rw [ segment_eq_image ] at h; obtain ⟨ t, ht, rfl ⟩ := h; norm_num [ Complex.ext_iff ] at *; nlinarith;
      · unfold HexArea.shoelace2; simp +decide [ HexArea.cross ] ;
        constructor <;> intro <;> nlinarith

/- **The geometric reduction step of the Meisters two-ears search (the single
    remaining open core, now carrying the strong-induction hypothesis).**
    Given the simple, non-degenerate polygon `V` (`≥ 4` vertices), a forbidden
    vertex `z`, and the induction hypothesis `IH` providing an empty corner
    (avoiding any forbidden vertex) for every *strictly shorter* simple
    non-degenerate polygon, `V` itself has an empty corner avoiding `z`.

    This isolates the genuine Jordan-curve-theorem-level geometric content of
    the Umlaufsatz: the convex-vertex / farthest-interior-vertex dichotomy, the
    interior-diagonal split, and the `PolygonSimple` preservation under the
    split.  The (purely combinatorial) strong-induction plumbing that discharges
    `IH` is handled sorry-free by `exists_empty_corner_avoiding_aux` below.
    Intended route: as documented on `exists_empty_corner_avoiding` —
    lex-minimal convex vertex (`HexArea.exists_lex_min_mem`,
    `lexMin_not_inTriangleStrict`, `exists_rotate_mid`); if its corner is empty
    use it (or a cyclic neighbour, to dodge `z`); otherwise pivot to the
    farthest interior vertex (`HexArea.exists_max_cross`, `farthest_region_empty`,
    `inTriangleStrict_pos_nest`, `subTri_axc_orient_pos`,
    `inTriangleStrict_apex_sameSide`), split along the resulting interior
    diagonal via `chordLeft`/`chordRight` and recurse through `IH` on the
    strictly shorter sub-polygon avoiding the shared diagonal endpoint. -/

/-- **Clean direct empty-ear assembly (sorry-free, reusable).**  When the convex
    apex `b` of the rotated cycle `V.rotate r = a :: b :: c :: rest` is already a
    *bona-fide* empty ear avoiding `z` — i.e. `b ≠ z`, the corner is empty
    (`hempty`), no far vertex sits on the closed diagonal `a–c` (`hdiag`), the
    two diagonal-endpoint neighbours `p` (last of `rest`) and `q` (head of
    `rest`) lie strictly off the *line* `a–c` (`hpline`, `hqline`), and the ear
    triangle shares the clip orientation (`horient`) — the `EmptyCornerData`
    package is assembled directly.  The two clip-turn non-degeneracies are
    produced from `hpline`/`hqline` by `HexArea.clip_turn_at_a_ne_zero` and
    `HexArea.clip_turn_at_c_ne_zero`.  This isolates the purely combinatorial
    assembly of the empty branch from its genuine Jordan content (establishing
    `hpline`, `hqline`, `hdiag`, `horient`, and the `b ≠ z` dodge), and is
    consumed by `meisters_reduction_empty` to discharge its clean case. -/
lemma empty_ear_direct (V : List ℂ) (z : ℂ) (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (p q : ℂ) (hrot : V.rotate r = a :: b :: c :: rest) (hbz : b ≠ z)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpline : HexArea.cross (c - a) (p - a) ≠ 0)
    (hqline : HexArea.cross (c - a) (q - a) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))) :
    EmptyCornerData V z :=
  ⟨r, a, b, c, p, q, rest, hrot, hbz, hp, hq,
    HexArea.clip_turn_at_a_ne_zero a c p hpline,
    HexArea.clip_turn_at_c_ne_zero a c q hqline,
    hempty, hdiag, horient⟩

/-- **Clip preservation of simplicity and non-degeneracy (reusable brick).**
    When the convex corner `a, b, c` of a simple, cyclically non-degenerate
    cycle `a :: b :: c :: rest` is *empty* — no far vertex strictly inside
    (`hempty`) nor on the closed diagonal `a–c` (`hdiag`) — and the two diagonal
    clip-turns are non-flat (`hpa`, `hcq`), the clipped cycle `a :: c :: rest`
    is again `PolygonSimple` and `polyCycNondeg`.  Pure assembly of the existing
    bricks `diag_disjoint_of_empty_corner` + `PolygonSimple_clip` and
    `polyCycNondeg_clip`.  This is the combinatorial half of the empty-branch
    recurse-and-lift step (it produces exactly the two `IH` hypotheses needed to
    recurse on the strictly-shorter clip); the genuine remaining Jordan content
    is the *lift* of the returned sub-polygon ear back to `V`. -/
lemma clip_simple_nondeg_of_empty (a b c p q : ℂ) (rest : List ℂ)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hsrot : PolygonSimple (a :: b :: c :: rest))
    (hndrot : polyCycNondeg (a :: b :: c :: rest))
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0) (hca : c - a ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (hpa : HexArea.cross (a - p) (c - a) ≠ 0)
    (hcq : HexArea.cross (c - a) (q - c) ≠ 0) :
    PolygonSimple (a :: c :: rest) ∧ polyCycNondeg (a :: c :: rest) :=
  ⟨PolygonSimple_clip a b c rest hsrot
      (diag_disjoint_of_empty_corner a b c rest hsrot hndtri hca hempty hdiag),
   polyCycNondeg_clip a b c p q rest hq hp hndrot hpa hcq⟩

/-
**Interior-ear rotation/insertion lift (pure list combinatorics, reusable).**
    The combinatorial heart of the empty-branch (and interior-branch) ear lift.
    Suppose the clip cycle `a :: c :: rest` has a cyclic rotation whose tail
    `rest'` contains the `a–c` junction in its *interior*, i.e. `rest'` decomposes
    as `s ++ a :: c :: t`, exhibiting a clip ear `a' b' c'` that is *not* adjacent
    to the junction.  Re-inserting the convex apex `b` between `a` and `c`
    recovers a genuine rotation of the full cycle `a :: b :: c :: rest` with the
    *same* ear `a' b' c'` and tail `s ++ a :: b :: c :: t`.  The uniqueness
    hypotheses `hac : a ≠ c` and `hanr : a ∉ rest` guarantee that the `a :: c`
    appearing in `rest'` is genuinely the junction (so inserting `b` there is the
    inverse of the clip operation).  This is the clean *interior* case of the
    lift; the boundary case (ear adjacent to the junction, so `a'` or `c'` is
    `a`/`c`) is handled separately.  **Preparation toward** the open lifts
    `empty_branch_good_lift` and `meisters_reduction_interior2`: it supplies the
    rotation witness `V.rotate r'' = a' :: b' :: c' :: (s ++ a :: b :: c :: t)`
    needed there, so it is NOT a dead branch.
-/
lemma clip_ear_lift_interior (a b c a' b' c' : ℂ) (rest s t : List ℂ) (r' : ℕ)
    (hac : a ≠ c) (hanr : a ∉ rest)
    (hrot' : (a :: c :: rest).rotate r'
        = a' :: b' :: c' :: (s ++ a :: c :: t)) :
    ∃ r'', (a :: b :: c :: rest).rotate r''
        = a' :: b' :: c' :: (s ++ a :: b :: c :: t) := by
  -- Rotate both sides of `hrot'` by an extra `3 + s.length` to bring the junction `a :: c` of `M` to the front.
  set m := r' + 3 + s.length
  have hrotm : (a :: c :: rest).rotate m = a :: c :: (t ++ a' :: b' :: c' :: s) := by
    convert congr_arg ( fun l => l.rotate ( 3 + s.length ) ) hrot' using 1;
    · rw [ List.rotate_rotate ];
      rw [ ← add_assoc ];
    · simp +decide [ add_comm, List.rotate ];
      rw [ Nat.mod_eq_of_lt ] <;> simp +arith +decide;
  -- Since `a ≠ c` and `a ∉ rest`, the element `a` occurs in `a :: c :: rest` only at index 0; as `a` is also `m % n`-th element, we get `m % n = 0`. Hence `L.rotate m = L.rotate (m % n) = L.rotate 0 = L = a :: c :: rest`. Comparing with `a :: c :: (t ++ a' :: b' :: c' :: s)` and stripping the common `a :: c ::` prefix gives `rest = t ++ a' :: b' :: c' :: s`.
  have hrest : rest = t ++ a' :: b' :: c' :: s := by
    have hrotm_eq : (a :: c :: rest)[m % (a :: c :: rest).length]'(by
    exact Nat.mod_lt _ ( by simp +decide )) = a := by
      convert congr_arg ( fun x : List ℂ => x[0]! ) hrotm using 1;
      simp +decide [ List.getElem_rotate ]
    generalize_proofs at *;
    rcases n : m % ( a :: c :: rest ).length with ( _ | _ | n ) <;> simp_all +decide [ List.get ];
    · simp_all +decide [ List.rotate ];
    · exact False.elim <| hanr <| hrotm_eq ▸ List.getElem_mem _;
  use 3 + t.length; simp_all +decide [ List.rotate ] ;
  rw [ Nat.mod_eq_of_lt ] <;> simp +arith +decide [ List.drop_append, List.take_append ]

/-
**Apex re-insertion across a clip rotation, GENERAL prefix form.**  The
    arbitrary-prefix generalisation of `clip_ear_lift_interior`: whenever a
    rotation of the clip `a :: c :: rest` exhibits the junction `a :: c`
    consecutively as `pre ++ a :: c :: suf`, re-inserting the apex `b` between
    that `a` and `c` is realised by a rotation of the full cycle
    `a :: b :: c :: rest`, giving `pre ++ a :: b :: c :: suf`.  Taking
    `pre = a' :: b' :: c' :: s` recovers `clip_ear_lift_interior`; taking
    `pre = [a', b']` (resp. rotating so the junction is internal) covers the two
    boundary-seam configurations of `boundary_seam_split`.  Pure list surgery
    (the same `a`-occurs-only-at-index-0 argument), absent from Mathlib.
    Preparation consumed by the boundary-seam lift below — NOT a dead branch.
-/
lemma clip_ear_lift_general (a b c : ℂ) (rest pre suf : List ℂ) (r' : ℕ)
    (hac : a ≠ c) (hanr : a ∉ rest)
    (hrot' : (a :: c :: rest).rotate r' = pre ++ a :: c :: suf) :
    ∃ r'', (a :: b :: c :: rest).rotate r'' = pre ++ a :: b :: c :: suf := by
  -- From the rotation form of `a :: c :: rest`, we derive that `rest = suf ++ pre`.
  have hrest : rest = suf ++ pre := by
    have hrest : (a :: c :: rest).rotate (r' + pre.length) = a :: c :: (suf ++ pre) := by
      convert congr_arg ( fun x => x.rotate pre.length ) hrot' using 1 <;> simp +decide [ List.rotate_rotate ];
    have hrest : (a :: c :: rest)[(r' + pre.length) % (a :: c :: rest).length]'(by
    exact Nat.mod_lt _ ( by simp +decide )) = a := by
      convert congr_arg ( fun x : List ℂ => x[0]! ) hrest using 1;
      simp +decide [ List.getElem_rotate ]
    generalize_proofs at *;
    rcases n : ( r' + pre.length ) % List.length ( a :: c :: rest ) with ( _ | _ | n ) <;> simp_all +decide [ List.get ];
    · have := Nat.dvd_of_mod_eq_zero n; obtain ⟨ k, hk ⟩ := this; simp_all +decide [ List.rotate ] ;
    · exact False.elim <| hanr <| hrest ▸ List.getElem_mem _;
  use 3 + suf.length; simp +decide [ List.rotate, hrest ] ;
  rcases pre with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, pre ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ]

/-
**Signed-area additivity for a mid-list apex insertion (pure, reusable).**
    Inserting the apex `b` between consecutive vertices `a, c` anywhere in a
    cycle changes the signed area by exactly the triangle term
    `shoelace2 [a, b, c]`.  This is the mid-list generalisation of
    `shoelace2_clip_second` (the front case), obtained by rotation-invariance
    (`shoelace2_rotate`) bringing the `a :: b :: c` block to the front and then
    applying `shoelace2_clip_second`.  **Preparation toward** the orientation
    transfer of `clip_ear_lift_interior`'s output: it lets the ear-orientation
    `iff` for the lifted `V`-clip be derived from the clip's, so it is NOT a
    dead branch.
-/
lemma shoelace2_insert_mid (pre suf : List ℂ) (a b c : ℂ) :
    HexArea.shoelace2 (pre ++ a :: b :: c :: suf)
      = HexArea.shoelace2 (pre ++ a :: c :: suf) + HexArea.shoelace2 [a, b, c] := by
  induction pre <;> simp_all +decide [ HexArea.shoelace2 ];
  · unfold HexArea.cross; ring;
  · cases ‹List ℂ› <;> simp_all +decide [ HexArea.shoelaceOpen ]; all_goals grind

/-
**Membership transfer for a 3-prefix rotation (reusable).**  If a rotation
    of `L` has prefix `a' :: b' :: c'`, then `a', b', c'` and every element of
    the remaining tail `rest'` are members of `L`.  Pure `List.mem_rotate`
    bookkeeping; consumed by `empty_branch_good_lift`.
-/
lemma rotate_cons3_mem (L : List ℂ) (a' b' c' : ℂ) (rest' : List ℂ) (r' : ℕ)
    (h : L.rotate r' = a' :: b' :: c' :: rest') :
    a' ∈ L ∧ b' ∈ L ∧ c' ∈ L ∧ (∀ x ∈ rest', x ∈ L) := by
  -- Since L.rotate r' is equal to a' :: b' :: c' :: rest', each element in this list is in L.
  have h_mem : ∀ x ∈ a' :: b' :: c' :: rest', x ∈ L := by
    exact fun x hx => by rw [ ← h ] at hx; exact List.mem_rotate.mp hx;
  aesop

/-
**Ear non-degeneracy from cyclic non-degeneracy (reusable).**  If `M` is
    cyclically non-degenerate and a rotation of `M` has prefix
    `a' :: b' :: c'`, the corner turn at `b'` is non-flat.  From
    `polyCycNondeg_rotate` and the head clause of `polyNondeg`; consumed by
    `empty_branch_good_lift`.
-/
lemma polyCycNondeg_rotate_head (M : List ℂ) (a' b' c' : ℂ) (rest' : List ℂ)
    (r' : ℕ) (h3 : 3 ≤ M.length) (hMn : polyCycNondeg M)
    (h : M.rotate r' = a' :: b' :: c' :: rest') :
    HexArea.cross (b' - a') (c' - b') ≠ 0 := by
  have h_polyNondeg : polyNondeg (M.rotate r' ++ List.take 2 (M.rotate r')) := by
    exact polyCycNondeg_rotate M r' h3 |>.2 hMn;
  unfold polyNondeg at h_polyNondeg; aesop;

/-
**The forbidden pair lies among the corner vertices (reusable).**  Given the
    convex-corner rotation `V.rotate r = a :: b :: c :: rest` of a simple
    polygon, if `b` is one of the forbidden vertices `z1, z2` and `z1, z2` are
    either equal or a cyclic edge of `V`, then both forbidden vertices lie in
    `{a, b, c}`: the only cyclic neighbours of `b` in `V` are `a` and `c`.
    Consumed by `empty_branch_good_lift` (to show every `rest`-vertex avoids
    both forbidden vertices).
-/
lemma forbidden_subset_corner (V : List ℂ) (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple V) (hrot : V.rotate r = a :: b :: c :: rest)
    (z1 z2 : ℂ) (hadj : z1 = z2 ∨ IsCycEdge V z1 z2) (hbf : b = z1 ∨ b = z2) :
    (z1 = a ∨ z1 = b ∨ z1 = c) ∧ (z2 = a ∨ z2 = b ∨ z2 = c) := by
  have hrot_nodup : List.Nodup (a :: b :: c :: rest) := by
    rw [ ← hrot, List.nodup_rotate ] ; exact hsimple.1;
  obtain ⟨hbf1, hbf2⟩ : z1 = z2 ∨ (IsCycEdge (a :: b :: c :: rest) z1 z2) := by
    convert hadj using 1;
    simp +decide [ ← hrot, IsCycEdge ];
    grind +suggestions;
  · grind;
  · unfold IsCycEdge at *; simp_all +decide [ List.zip ] ;
    unfold closedEdges at *; simp_all +decide [ List.zip ] ;
    rcases ‹_› with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | h ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | h ) <;> simp_all +decide [ List.zipWith ];
    · rw [ List.mem_iff_get ] at h; obtain ⟨ i, hi ⟩ := h; simp_all +decide [ List.get ] ;
      grind;
    · rw [ List.mem_iff_get ] at h; obtain ⟨ i, hi ⟩ := h; simp_all +decide [ List.get ] ;
      grind

/-- **Interior-ear lift assembly (self-contained transfer brick, PROVED).**  This
    is the fully-proved *interior* half of the empty-branch lift.  Given the convex
    apex `b` of `V.rotate r = a :: b :: c :: rest` (with the convexity data
    `hbconv`/`hbseg` and the ear-orientation `horient`), and an ear
    `a' :: b' :: c'` of the *clip* `a :: c :: rest` whose `a–c` junction sits in
    the **interior** of the ear's tail (`rest' = s ++ a :: c :: t`, with tip
    `b' ∈ rest`), re-inserting `b` between `a` and `c` lifts the clip ear back to
    a genuine `EmptyCornerData2 V z1 z2` ear.  All transfers are local:
    - the rotation witness comes from `clip_ear_lift_interior`;
    - the clip-turn neighbours `p', q'` are unchanged by the insertion (the
      junction is interior), so the clip-turn clauses `hpt'`, `hqt'` transfer
      verbatim;
    - emptiness transfers because the only new vertex `b` is outside the ear
      triangle (`hbconv`), and diagonal-clearance because `b` is off the ear
      diagonal (`hbseg`);
    - the orientation `iff` transfers via `shoelace2_insert_mid` /
      `shoelace2_rotate` / `shoelace2_clip_second`, using that the two ear areas
      `shoelace2 [a,b,c]` and `shoelace2 [a',b',c']` are non-zero
      (`hABCne`, `hA'ne`) and the orientation hypotheses `horient`, `horient'`.
    The tip `b'` avoids both forbidden vertices via `hzrest`.  Consumed by
    `empty_branch_good_lift` (interior subcase).
-/
lemma empty_branch_interior_lift (V : List ℂ) (z1 z2 : ℂ)
    (a b c : ℂ) (rest : List ℂ) (r : ℕ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hac : a ≠ c) (hanr : a ∉ rest)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hABCne : HexArea.cross (b - a) (c - b) ≠ 0)
    (hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2)
    (a' b' c' p' q' : ℂ) (s t : List ℂ) (r' : ℕ)
    (hrot' : (a :: c :: rest).rotate r' = a' :: b' :: c' :: (s ++ a :: c :: t))
    (hb'rest : b' ∈ rest) (ha'V : a' ∈ V) (hb'V : b' ∈ V) (hc'V : c' ∈ V)
    (ha'b : b ≠ a') (hc'b : b ≠ c')
    (hA'ne : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hp' : (s ++ a :: c :: t).getLast? = some p')
    (hq' : (s ++ a :: c :: t).head? = some q')
    (hpt' : HexArea.cross (a' - p') (c' - a') ≠ 0)
    (hqt' : HexArea.cross (c' - a') (q' - c') ≠ 0)
    (hempty' : ∀ x ∈ (s ++ a :: c :: t), ¬ HexArea.inTriangleStrict a' b' c' x)
    (hdiag' : ∀ x ∈ (s ++ a :: c :: t), x ∉ segment ℝ a' c')
    (horient' : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t)))) :
    EmptyCornerData2 V z1 z2 := by
  -- By `clip_ear_lift_interior`, obtain旋转 witness `r''` for the genuine V ear.
  obtain ⟨r'', hrnewrot⟩ : ∃ r'', (V.rotate (r + r'')) = a' :: b' :: c' :: (s ++ a :: b :: c :: t) := by
    have := clip_ear_lift_interior a b c a' b' c' rest s t r' hac hanr ?_;
    · obtain ⟨ r'', hr'' ⟩ := this; use r''; rw [ ← hr'' ] ; simp +decide [ ← hrot, List.rotate_rotate ] ;
    · exact hrot';
  refine' ⟨ r + r'', a', b', c', p', q', s ++ a :: b :: c :: t, hrnewrot, _, _, _, _, _ ⟩;
  · exact hzrest _ hb'rest |>.1;
  · exact hzrest _ hb'rest |>.2;
  · grind;
  · cases s <;> aesop;
  · have hXYS : HexArea.shoelace2 (a :: c :: rest) = HexArea.shoelace2 (a' :: b' :: c' :: (s ++ a :: c :: t)) := by
      rw [ ← hrot', shoelace2_rotate ];
    have hXYS : HexArea.shoelace2 (a' :: b' :: c' :: (s ++ a :: c :: t)) = HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t)) + HexArea.shoelace2 [a', b', c'] := by
      convert shoelace2_clip_second a' b' c' ( s ++ a :: c :: t ) using 1;
    have hXYS : HexArea.shoelace2 (a' :: c' :: (s ++ a :: b :: c :: t)) = HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t)) + HexArea.shoelace2 [a, b, c] := by
      convert shoelace2_insert_mid ( a' :: c' :: s ) t a b c using 1;
    grind

end
