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
import RequestProject.SAWUmlaufCorner
import RequestProject.SAWUmlaufEarSplit

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
      (∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w) := by
  -- By `exists_lex_min_mem`, there exists a lexicographically minimal vertex `v` in `V`.
  obtain ⟨v, hv_mem, hv_lex_min⟩ : ∃ v ∈ V, ∀ w ∈ V, v.re < w.re ∨ (v.re = w.re ∧ v.im ≤ w.im) := by
    obtain ⟨ v, hv ⟩ := HexArea.exists_lex_min_mem V ( by aesop_cat );
    use v;
  obtain ⟨ r, a, c, rest, hr ⟩ := exists_rotate_mid V v hv_mem h3;
  refine' ⟨ r, a, v, c, rest, hr, hv_mem, _, _ ⟩;
  · intros x y w hx hy hw h_in_triangle;
    apply HexArea.lexMin_not_inTriangleStrict V v hv_lex_min x y w hx hy hw h_in_triangle
  · intros u w hu hw hvu hvw;
    exact HexArea.lexMin_not_mem_segment V v hv_lex_min u w hu hw hvu hvw

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

/-! ### Interior-diagonal split: reusable simplicity/non-degeneracy bricks

These were previously stranded in `SAWUmlaufChordSplit` (which imports this
file), so they were unusable by the open Meisters branches below.  They are
moved here, before the branches, so the interior-diagonal split can consume
them.  They are purely combinatorial packaging: a split piece is a sub-path of
the parent polygon closed by the single cut diagonal. -/

namespace HexArea

/-- The **non-cyclic** (path) edges of a vertex list `P`: the consecutive pairs
    `(P₀,P₁), …, (P_{n-1},P_n)`, omitting the wrap-around edge.  The cyclic edges
    are `pathEdges P ++ [(last, head)]` (`closedEdges_eq_pathEdges`). -/
def pathEdges (P : List ℂ) : List (ℂ × ℂ) := P.zip P.tail

@[simp] lemma pathEdges_nil : pathEdges ([] : List ℂ) = [] := rfl
@[simp] lemma pathEdges_singleton (a : ℂ) : pathEdges [a] = [] := rfl

lemma pathEdges_cons_cons (a b : ℂ) (rest : List ℂ) :
    pathEdges (a :: b :: rest) = (a, b) :: pathEdges (b :: rest) := by
  simp [pathEdges]

/-- `(p :: rest).rotate 1 = rest ++ [p]`. -/
lemma rotate_one_cons (p : ℂ) (rest : List ℂ) :
    (p :: rest).rotate 1 = rest ++ [p] := by
  rw [List.rotate_cons_succ]; simp

/-- **Cyclic edges = path edges plus the closing chord.** -/
lemma closedEdges_eq_pathEdges (P : List ℂ) (u v : ℂ)
    (hhead : P.head? = some u) (hlast : P.getLast? = some v) :
    closedEdges P = pathEdges P ++ [(v, u)] := by
  rcases P with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ pathEdges ];
  · unfold closedEdges; aesop;
  · induction l generalizing u y <;> simp_all +decide [ closedEdges ]

/-- **Membership in path edges implies membership in cyclic edges.** -/
lemma mem_closedEdges_of_mem_pathEdges (P : List ℂ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges P) : e ∈ closedEdges P := by
  rcases P with ( _ | ⟨ a, _ | ⟨ b, P ⟩ ⟩ ) <;> simp_all +decide [ pathEdges, closedEdges ];
  have h_zip_append : ∀ (l r1 r2 : List ℂ), List.zip l (r1 ++ r2) = List.zip l r1 ++ List.zip (List.drop r1.length l) r2 := by
    intros l r1 r2; induction' l with hd tl hl generalizing r1 r2 <;> cases r1 <;> cases r2 <;> simp +decide [ * ] ;
  grind

/-- **Simplicity from a simple path plus a clear closing chord.** -/
lemma PolygonSimple_of_simplePath (P : List ℂ) (u v : ℂ)
    (hhead : P.head? = some u) (hlast : P.getLast? = some v)
    (hnodup : P.Nodup)
    (hpath : ∀ e₁ ∈ pathEdges P, ∀ e₂ ∈ pathEdges P,
        e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
        Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2))
    (hdiag : ∀ e ∈ pathEdges P,
        v ≠ e.1 → v ≠ e.2 → u ≠ e.1 → u ≠ e.2 →
        Disjoint (segment ℝ v u) (segment ℝ e.1 e.2)) :
    PolygonSimple P := by
  refine' ⟨ hnodup, _ ⟩;
  rw [ closedEdges_eq_pathEdges P u v hhead hlast ];
  grind

/-- **Cyclic non-degeneracy from path non-degeneracy plus two seam corners.** -/
lemma polyCycNondeg_of_path (P : List ℂ) (u u2 v vp : ℂ)
    (h3 : 3 ≤ P.length)
    (hu : P.head? = some u) (hu2 : P[1]? = some u2)
    (hv : P.getLast? = some v) (hvp : P.dropLast.getLast? = some vp)
    (hpath : polyNondeg P)
    (hseam1 : HexArea.cross (v - vp) (u - v) ≠ 0)
    (hseam2 : HexArea.cross (u - v) (u2 - u) ≠ 0) :
    polyCycNondeg P := by
  obtain ⟨a, b, c, rest, hP⟩ : ∃ a b c : ℂ, ∃ rest : List ℂ, P = a :: b :: c :: rest := by
    rcases P with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | P ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  simp_all +decide [ polyCycNondeg ];
  have h_polyNondeg : ∀ (L : List ℂ), polyNondeg L → ∀ (x y : ℂ), HexArea.cross (L.getLast! - L.dropLast.getLast!) (x - L.getLast!) ≠ 0 → HexArea.cross (x - L.getLast!) (y - x) ≠ 0 → polyNondeg (L ++ [x, y]) := by
    intros L hL x y hx hy; induction' L with a L ih generalizing x y <;> simp_all +decide [ polyNondeg_cons_cons_cons ] ;
    rcases L with ( _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
  convert h_polyNondeg ( u :: u2 :: c :: rest ) hpath u u2 _ _ using 1 <;> simp_all +decide [ List.getLast? ]

/-! #### Edge inheritance for the chord-split pieces (preparation for
`meisters_reduction_interior2`).  Each split piece's path edges are cyclic edges
of the parent polygon, so the piece inherits `PolygonSimple`'s edge-disjointness
verbatim.  These bricks plus the geometric diagonal clearance feed
`PolygonSimple_of_simplePath`. -/

/-
A path edge of a prefix `V.take m` is a path edge of `V`.
-/
lemma mem_pathEdges_take (V : List ℂ) (m : ℕ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges (V.take m)) : e ∈ pathEdges V := by
  induction' m with m ih generalizing V;
  · cases he;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ pathEdges_cons_cons ];
    cases m <;> simp_all +decide [ pathEdges_cons_cons ];
    cases he <;> simp_all +decide [ pathEdges_cons_cons ]

/-
Every path edge of the left split piece `chordLeft V k` is a cyclic edge of
    the whole polygon `V`.
-/
lemma pathEdges_chordLeft_mem_closedEdges (V : List ℂ) (k : ℕ) (e : ℂ × ℂ)
    (he : e ∈ pathEdges (chordLeft V k)) : e ∈ closedEdges V := by
  apply mem_closedEdges_of_mem_pathEdges;
  apply mem_pathEdges_take;
  convert he using 1

/-
Every path edge of the right split piece `chordRight V k` is a cyclic edge of
    the whole polygon `V`.
-/
lemma pathEdges_chordRight_mem_closedEdges (V : List ℂ) (k : ℕ) (hk : k < V.length)
    (e : ℂ × ℂ) (he : e ∈ pathEdges (chordRight V k)) : e ∈ closedEdges V := by
  induction' k with k ih generalizing V;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ chordRight ];
    · cases he;
      · simp +decide [ closedEdges ];
      · contradiction;
    · induction' V with V ih generalizing a b;
      · unfold pathEdges closedEdges at * ; aesop;
      · cases ih <;> simp_all +decide [ pathEdges, closedEdges ];
        grind;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ chordRight ];
    grind +suggestions

/-
**Left split piece is simple** given the cut-diagonal clearance.  Preparation
    for `meisters_reduction_interior2`: combined with the geometric clearance of
    the cut diagonal `V[k]–V[0]`, the left piece `V₀,…,V_k` is a `PolygonSimple`
    sub-polygon.
-/
lemma chordLeft_PolygonSimple (V : List ℂ) (k : ℕ) (v0 vk : ℂ)
    (hk2 : 2 ≤ k) (hk : k + 1 ≤ V.length)
    (hsimple : PolygonSimple V)
    (hv0 : V.head? = some v0) (hvk : V[k]? = some vk)
    (hclear : ∀ e ∈ pathEdges (chordLeft V k),
        vk ≠ e.1 → vk ≠ e.2 → v0 ≠ e.1 → v0 ≠ e.2 →
        Disjoint (segment ℝ vk v0) (segment ℝ e.1 e.2)) :
    PolygonSimple (chordLeft V k) := by
  apply PolygonSimple_of_simplePath (chordLeft V k) v0 vk;
  · convert hv0 using 1;
    convert chordLeft_head V k;
  · grind +suggestions;
  · exact List.Nodup.sublist ( List.take_sublist _ _ ) hsimple.1;
  · exact fun e₁ he₁ e₂ he₂ h₁ h₂ h₃ h₄ => hsimple.2 e₁ ( pathEdges_chordLeft_mem_closedEdges V k e₁ he₁ ) e₂ ( pathEdges_chordLeft_mem_closedEdges V k e₂ he₂ ) h₁ h₂ h₃ h₄;
  · assumption

/-
**Right split piece is simple** given the cut-diagonal clearance.  Preparation
    for `meisters_reduction_interior2`.
-/
lemma chordRight_PolygonSimple (V : List ℂ) (k : ℕ) (v0 vk : ℂ)
    (hk1 : 1 ≤ k) (hk : k < V.length)
    (hsimple : PolygonSimple V)
    (hv0 : V.head? = some v0) (hvk : V[k]? = some vk)
    (hclear : ∀ e ∈ pathEdges (chordRight V k),
        v0 ≠ e.1 → v0 ≠ e.2 → vk ≠ e.1 → vk ≠ e.2 →
        Disjoint (segment ℝ v0 vk) (segment ℝ e.1 e.2)) :
    PolygonSimple (chordRight V k) := by
  apply PolygonSimple_of_simplePath;
  rotate_left;
  rotate_left;
  exact chordRight_nodup V k hk1 hk hsimple.1;
  rotate_left;
  convert hclear using 1;
  · unfold chordRight; aesop;
  · grind +suggestions;
  · intros e₁ he₁ e₂ he₂ hne₁ hne₂ hne₃ hne₄;
    apply hsimple.2 e₁ (pathEdges_chordRight_mem_closedEdges V k hk e₁ he₁) e₂ (pathEdges_chordRight_mem_closedEdges V k hk e₂ he₂) hne₁ hne₂ hne₃ hne₄

/-! #### Non-degeneracy inheritance for the chord-split pieces (companion to the
simplicity bricks; preparation for `meisters_reduction_interior2`).  A contiguous
infix of a path keeps all its consecutive-triple non-flatness, so each split
piece's path triples are inherited; the only new corners are the two seams at the
cut diagonal's endpoints. -/

/-
`polyNondeg` is inherited by any prefix.
-/
lemma polyNondeg_take (V : List ℂ) (m : ℕ) (h : polyNondeg V) :
    polyNondeg (V.take m) := by
  induction' n : V.length with n ih generalizing V m;
  · cases V <;> aesop;
  · rcases m with ( _ | _ | _ | m ) <;> rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, V ⟩ ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ];
    convert ih ( b :: c :: V ) ( m + 2 ) h.2 ( by simp +arith +decide [ n.symm ] ) using 1

/-
`polyNondeg` is inherited by any suffix.
-/
lemma polyNondeg_drop (V : List ℂ) (k : ℕ) (h : polyNondeg V) :
    polyNondeg (V.drop k) := by
  induction' k with k ih generalizing V;
  · simpa;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, V ⟩ ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg_cons_cons_cons ]

/-
**Left split piece is cyclically non-degenerate** given the two seam corners
    at the cut-diagonal endpoints.  Preparation for
    `meisters_reduction_interior2`.
-/
lemma chordLeft_polyCycNondeg (V : List ℂ) (k : ℕ) (v0 v1 vk vkm1 : ℂ)
    (hk2 : 2 ≤ k) (hk : k + 1 ≤ V.length)
    (hnd : polyCycNondeg V)
    (hv0 : V.head? = some v0) (hv1 : V[1]? = some v1)
    (hvk : V[k]? = some vk) (hvkm1 : V[k-1]? = some vkm1)
    (hseam1 : HexArea.cross (vk - vkm1) (v0 - vk) ≠ 0)
    (hseam2 : HexArea.cross (v0 - vk) (v1 - v0) ≠ 0) :
    polyCycNondeg (chordLeft V k) := by
  convert polyCycNondeg_of_path ( chordLeft V k ) v0 v1 vk vkm1 _ _ _ _ _ _ using 1;
  grind +splitIndPred;
  all_goals norm_num [ chordLeft ];
  grind;
  · cases V <;> aesop;
  · grind;
  · grind;
  · grind +splitImp;
  · convert polyNondeg_take _ _ hnd using 1;
    rw [ List.take_append_of_le_length ] ; omega

/-
**Right split piece is cyclically non-degenerate** given the two seam corners
    at the cut-diagonal endpoints.  Preparation for
    `meisters_reduction_interior2`.
-/
lemma chordRight_polyCycNondeg (V : List ℂ) (k : ℕ) (v0 vk vk1 vlast : ℂ)
    (hk1 : 1 ≤ k) (hk : k + 2 ≤ V.length)
    (hnd : polyCycNondeg V)
    (hv0 : V.head? = some v0) (hvk : V[k]? = some vk)
    (hvk1 : V[k+1]? = some vk1) (hvlast : V[V.length-1]? = some vlast)
    (hseam1 : HexArea.cross (v0 - vlast) (vk - v0) ≠ 0)
    (hseam2 : HexArea.cross (vk - v0) (vk1 - vk) ≠ 0) :
    polyCycNondeg (chordRight V k) := by
  convert polyCycNondeg_of_path ( chordRight V k ) vk vk1 v0 vlast _ _ _ _ _ _ _ using 1;
  all_goals norm_num [ chordRight, List.drop_append, List.take_append, hk1, hk ];
  any_goals omega;
  exact Or.inl hseam2;
  · exact Or.inl hvk;
  · grind;
  · cases V <;> aesop;
  · grind;
  · convert polyNondeg_take ( V.drop k ++ V.take 2 ) ( V.length - k + 1 ) _ using 1;
    · rcases V with ( _ | ⟨ x, _ | ⟨ y, V ⟩ ⟩ ) <;> simp_all +decide [ List.take_append ];
    · convert polyNondeg_drop ( V ++ V.take 2 ) k _ using 1;
      · simp +arith +decide [ List.drop_append, List.take_append ];
        rw [ Nat.sub_eq_zero_of_le ( by linarith ) ] ; norm_num;
      · exact hnd

/-- **Generalised corner-exit lemma (start point need not be on the base
    line).**  This is `corner_exit_point` with its `hzac : cross (a-c)(z-c) = 0`
    weakened to `0 ≤ cross (a-c)(z-c) * O`: the start point `z` is allowed to be
    strictly on the apex side (`PC(z) ≥ 0`) rather than exactly on the base line.
    The same affine first-crossing argument applies: along `z → u` the apex test
    `PC` is `(1-τ)·PC(z) + τ·PC(u) ≥ τ·PC(u) > 0` for `τ > 0`, so the moving point
    leaves the wedge through `a–b` or `b–c`.  Reusable preparation for
    `interior_chord_is_diagonal` (where the chord-crossing point is *strictly
    inside* the corner triangle, never on the base line). -/
lemma corner_exit_point_ge (a b c z u : ℂ)
    (hO : cross (b - a) (c - b) ≠ 0)
    (hzab : 0 < cross (b - a) (z - a) * cross (b - a) (c - b))
    (hzbc : 0 < cross (c - b) (z - b) * cross (b - a) (c - b))
    (hzac : 0 ≤ cross (a - c) (z - c) * cross (b - a) (c - b))
    (huac : 0 < cross (a - c) (u - c) * cross (b - a) (c - b))
    (hunot : ¬ inTriangleStrict a b c u) :
    (∃ y ∈ segment ℝ z u, y ∈ segment ℝ a b) ∨
    (∃ y ∈ segment ℝ z u, y ∈ segment ℝ b c) := by
  set O := cross (b - a) (c - b) with hO_def
  have hPA : ∀ τ : ℝ, cross (b - a) (z + τ • (u - z) - a) * O
      = (1 - τ) * cross (b - a) (z - a) * O + τ * cross (b - a) (u - a) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring
  have hPB : ∀ τ : ℝ, cross (c - b) (z + τ • (u - z) - b) * O
      = (1 - τ) * cross (c - b) (z - b) * O + τ * cross (c - b) (u - b) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring
  have hPC : ∀ τ : ℝ, cross (a - c) (z + τ • (u - z) - c) * O
      = (1 - τ) * cross (a - c) (z - c) * O + τ * cross (a - c) (u - c) * O := by
    unfold cross; norm_num [ Complex.ext_iff ] ; intros; ring
  by_cases hPAu : cross (b - a) (u - a) * O ≤ 0
  · set t := cross (b - a) (z - a) * O / (cross (b - a) (z - a) * O - cross (b - a) (u - a) * O) with ht_def
    have ht_bounds : 0 < t ∧ t ≤ 1 :=
      ⟨ div_pos hzab ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
    have ht_PA : cross (b - a) (z + t • (u - z) - a) * O = 0 := by grind
    have ht_PC : 0 < cross (a - c) (z + t • (u - z) - c) * O := by
      rw [ hPC ] ; nlinarith [ mul_pos ht_bounds.1 huac,
        mul_nonneg ( by linarith [ ht_bounds.2 ] : (0:ℝ) ≤ 1 - t ) hzac ]
    by_cases hPBu : cross (c - b) (u - b) * O ≥ 0
    · refine Or.inl ⟨ z + t • ( u - z ), ?_, ?_ ⟩
      · rw [ segment_eq_image ]
        exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
      · apply mem_segment_ab_of_cross a b c (z + t • (u - z)) hO
        · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO ht_PA
        · nlinarith [ hPB t ]
        · exact le_of_lt ht_PC
    · set s := cross (c - b) (z - b) * O / (cross (c - b) (z - b) * O - cross (c - b) (u - b) * O) with hs_def
      have hs_bounds : 0 < s ∧ s ≤ 1 :=
        ⟨ div_pos hzbc ( by linarith ), div_le_one_of_le₀ ( by linarith ) ( by linarith ) ⟩
      have hs_PB : cross (c - b) (z + s • (u - z) - b) * O = 0 := by grind
      have hs_PC : 0 < cross (a - c) (z + s • (u - z) - c) * O := by
        rw [ hPC ] ; nlinarith [ mul_pos hs_bounds.1 huac,
          mul_nonneg ( by linarith [ hs_bounds.2 ] : (0:ℝ) ≤ 1 - s ) hzac ]
      by_cases hts : t ≤ s
      · have ht_PB_nonneg : 0 ≤ cross (c - b) (z + t • (u - z) - b) * O := by
          rw [ hPB ] ; rw [ le_div_iff₀ ] at hts <;> nlinarith
        refine Or.inl ⟨ z + t • ( u - z ), ?_, ?_ ⟩
        · rw [ segment_eq_image ]
          exact ⟨ t, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
        · apply mem_segment_ab_of_cross a b c (z + t • (u - z)) hO
          · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO ht_PA
          · exact ht_PB_nonneg
          · exact le_of_lt ht_PC
      · have hs_PA : cross (b - a) (z + s • (u - z) - a) * O ≥ 0 := by
          rw [ hPA ] ; rw [ div_le_iff₀ ] at hts <;> nlinarith
        refine Or.inr ⟨ z + s • ( u - z ), ?_, ?_ ⟩
        · rw [ segment_eq_image ]
          exact ⟨ s, ⟨ by linarith, by linarith ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
        · apply mem_segment_bc_of_cross a b c (z + s • (u - z)) hO
          · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO hs_PB
          · exact hs_PA
          · exact le_of_lt hs_PC
  · have hPBu : cross (c - b) (u - b) * O ≤ 0 := by
      contrapose! hunot; simp_all +decide [ inTriangleStrict ]
      cases lt_or_gt_of_ne hO <;>
        first
          | exact Or.inl ⟨ by nlinarith, by nlinarith, by nlinarith ⟩
          | exact Or.inr ⟨ by nlinarith, by nlinarith, by nlinarith ⟩
    set s := cross (c - b) (z - b) * O / (cross (c - b) (z - b) * O - cross (c - b) (u - b) * O) with hs_def
    have hs_pos : 0 < s := div_pos hzbc ( by linarith )
    have hs_le_one : s ≤ 1 := div_le_one_of_le₀ ( by linarith ) ( by linarith )
    have hPB_s : cross (c - b) (z + s • (u - z) - b) * O = 0 := by
      rw [ hPB, hs_def ] ; nlinarith [ mul_div_cancel₀ ( cross ( c - b ) ( z - b ) * O )
        ( by linarith : ( cross ( c - b ) ( z - b ) * O - cross ( c - b ) ( u - b ) * O ) ≠ 0 ) ]
    have hPC_s : 0 ≤ cross (a - c) (z + s • (u - z) - c) * O := by
      rw [ hPC ] ; nlinarith [ mul_nonneg hs_pos.le huac.le,
        mul_nonneg ( by linarith : (0:ℝ) ≤ 1 - s ) hzac ]
    refine Or.inr ⟨ z + s • ( u - z ), ?_, ?_ ⟩
    · rw [ segment_eq_image ]
      exact ⟨ s, ⟨ hs_pos.le, hs_le_one ⟩, by simpa [ sub_smul, smul_sub ] using by ring ⟩
    · apply mem_segment_bc_of_cross a b c (z + s • (u - z)) hO
      · exact eq_zero_of_ne_zero_of_mul_right_eq_zero hO hPB_s
      · nlinarith [ hPA s ]
      · exact hPC_s

end HexArea

/-
**A simple-polygon vertex lies on none of its non-incident edges.**  If
    `V` is a simple polygon (`4 ≤ V.length`), `w` is a vertex of `V`, and `e` is
    a cyclic edge of `V` with neither endpoint equal to `w`, then `w` does not
    lie on the closed segment `e`.

    Proof: `w = V[i]`; its two incident cyclic edges `(V[i-1], w)` and
    `(w, V[i+1])` both contain `w`.  Since `n ≥ 4`, the two neighbours `V[i-1]`,
    `V[i+1]` are not cyclically adjacent, so `e` (whose endpoints avoid `w`)
    shares an endpoint with at most one of the two incident edges; the other
    incident edge is non-adjacent to `e`, hence `Disjoint` from it by
    `PolygonSimple` — but both contain `w` if `w ∈ e`, a contradiction.
    Combinatorial preparation for `interior_chord_is_diagonal` (the `z = w`
    boundary case, where the chord meets a far edge exactly at the pivot `w`).
-/
lemma simple_vertex_not_on_far_edge (V : List ℂ) (h4 : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (w : ℂ) (hw : w ∈ V)
    (e : ℂ × ℂ) (he : e ∈ closedEdges V) (hne1 : w ≠ e.1) (hne2 : w ≠ e.2) :
    w ∉ segment ℝ e.1 e.2 := by
  obtain ⟨ i, hi ⟩ := List.mem_iff_getElem.mp hw;
  obtain ⟨ hi, rfl ⟩ := hi;
  -- By definition of `closedEdges`, there exists some `j` such that `e = (V[j], V[(j+1)%n])`.
  obtain ⟨ j, hj ⟩ : ∃ j, j < V.length ∧ e = (V[j]!, V[(j + 1) % V.length]!) := by
    have h_closedEdges : closedEdges V = List.map (fun j => (V[j]!, V[(j + 1) % V.length]!)) (List.range V.length) := by
      refine' List.ext_get _ _ <;> simp +decide [ closedEdges ];
      grind +suggestions;
    grind;
  have h_incident : V[(i + V.length - 1) % V.length]! ≠ e.1 ∧ V[(i + V.length - 1) % V.length]! ≠ e.2 ∨ V[(i + 1) % V.length]! ≠ e.1 ∧ V[(i + 1) % V.length]! ≠ e.2 := by
    by_cases h_cases : j = (i + V.length - 1) % V.length ∨ (j + 1) % V.length = (i + V.length - 1) % V.length;
    · rcases h_cases with ( rfl | h_cases ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · rcases i with ( _ | i ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · have h_distinct : (i + 1) % V.length ≠ j ∧ (i + 1) % V.length ≠ (i + V.length - 1) % V.length := by
          constructor <;> intro h <;> have := Nat.mod_add_div ( i + 1 ) V.length <;> have := Nat.mod_add_div ( i + V.length - 1 ) V.length <;> simp_all +decide [ Nat.mod_eq_of_lt ];
          · rcases k : ( i + 1 ) / V.length with ( _ | _ | k ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
            · have := Nat.modEq_iff_dvd.mp h_cases.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
              obtain ⟨ a, ha ⟩ := this; rw [ Nat.cast_sub ( by linarith ) ] at ha; norm_num at ha; nlinarith [ show a = 0 by nlinarith ] ;
            · norm_num [ show i = V.length - 1 by omega ] at *;
              norm_num [ show j = 0 by omega ] at *;
              rcases V with ( _ | ⟨ _, _ | V ⟩ ) <;> norm_num at *;
              norm_num [ ( by ring : ( List.length ‹_› + 1 + ( List.length ‹_› + 1 ) ) = ( List.length ‹_› + 1 + 1 ) + ( List.length ‹_› ) ) ] at *;
              norm_num [ Nat.mod_eq_of_lt ] at *;
              grind +qlia;
            · nlinarith;
          · rcases V with ( _ | ⟨ _, _ | V ⟩ ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
            nlinarith [ show ( i + 1 ) / ( List.length ‹_› + 2 ) = ( i + List.length ‹_› + 1 ) / ( List.length ‹_› + 2 ) by nlinarith ];
        have := hsimple.1;
        rw [ List.nodup_iff_injective_get ] at this;
        exact ⟨ by rw [ List.getElem?_eq_getElem ( by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ) ] ; exact fun h => h_distinct.1 <| by have := @this ⟨ ( i + 1 ) % V.length, by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ⟩ ⟨ j, by linarith ⟩ ; aesop, by rw [ List.getElem?_eq_getElem ( by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ), List.getElem?_eq_getElem ( by linarith [ Nat.mod_lt ( i + V.length - 1 ) ( by linarith : 0 < V.length ) ] ) ] ; exact fun h => h_distinct.2 <| by have := @this ⟨ ( i + 1 ) % V.length, by linarith [ Nat.mod_lt ( i + 1 ) ( by linarith : 0 < V.length ) ] ⟩ ⟨ ( i + V.length - 1 ) % V.length, by linarith [ Nat.mod_lt ( i + V.length - 1 ) ( by linarith : 0 < V.length ) ] ⟩ ; aesop ⟩;
    · have h_distinct : V.Nodup := by
        exact hsimple.1;
      have h_distinct : ∀ (k l : ℕ), k < V.length → l < V.length → k ≠ l → V[k]! ≠ V[l]! := by
        intros k l hk hl hkl; have := List.nodup_iff_injective_get.mp h_distinct; simp_all +decide [ Function.Injective ] ;
        exact fun h => hkl <| by simpa [ Fin.ext_iff ] using @this ⟨ k, hk ⟩ ⟨ l, hl ⟩ h;
      exact Or.inl ⟨ by specialize h_distinct ( ( i + V.length - 1 ) % V.length ) j ( Nat.mod_lt _ ( by linarith ) ) hj.1; aesop, by specialize h_distinct ( ( i + V.length - 1 ) % V.length ) ( ( j + 1 ) % V.length ) ( Nat.mod_lt _ ( by linarith ) ) ( Nat.mod_lt _ ( by linarith ) ) ; aesop ⟩;
  have h_disjoint : Disjoint (segment ℝ (V[(i + V.length - 1) % V.length]!) (V[i])) (segment ℝ e.1 e.2) ∨ Disjoint (segment ℝ (V[i]) (V[(i + 1) % V.length]!)) (segment ℝ e.1 e.2) := by
    cases h_incident <;> simp_all +decide [ PolygonSimple ];
    · have h_disjoint : (V[(i + V.length - 1) % V.length]!, V[i]) ∈ closedEdges V := by
        convert List.mem_iff_getElem.mpr _ using 1;
        use (i + V.length - 1) % V.length;
        simp +decide [ closedEdges, List.getElem_zip ];
        simp +decide [ List.getElem_rotate, Nat.mod_lt ];
        simp +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ i + V.length ), Nat.mod_eq_of_lt hi ];
        exact ⟨ Nat.mod_lt _ ( by linarith ), by rw [ List.getElem?_eq_getElem ( Nat.mod_lt _ ( by linarith ) ) ] ; rfl ⟩;
      grind;
    · refine Or.inr <| hsimple.2 _ _ ?_ _ _ ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ closedEdges ];
      rw [ List.mem_iff_getElem ];
      use i; simp [List.getElem_zip, List.getElem_rotate];
      exact ⟨ hi, by rw [ List.getElem?_eq_getElem ( Nat.mod_lt _ ( by linarith ) ) ] ; rfl ⟩;
  cases h_disjoint <;> simp_all +decide [ Set.disjoint_left ];
  · rename_i h;
    exact fun h' => h ( right_mem_segment _ _ _ ) h';
  · exact fun h => ‹∀ a ∈ segment ℝ V[i] ( V[(i + 1) % V.length]?.getD default ), a ∉ segment ℝ V[j] ( V[(j + 1) % V.length]?.getD default ) › _ ( left_mem_segment _ _ _ ) h

/-
**A chord sub-segment lying off the line `a–b` avoids the ear edge `a–b`.**
    If `z, y` lie on a cyclic edge `e` of the simple polygon `a::b::c::rest`
    (with `b` not on `e`), `a` is not on the sub-segment `z–y`, and `z` is
    strictly off the line `a–b` (`cross (b-a)(z-a) ≠ 0`), then `segment z y` is
    disjoint from the ear edge `segment a b`.

    Proof: a common point `p` lies on `e` (convexity), is `≠ a` (`a ∉ z–y`) and
    `≠ b` (`b ∉ e`).  If `e` shares no endpoint with `a`, `PolygonSimple` makes
    `e` and the edge `a–b` disjoint — contradiction.  If `e` is incident to `a`,
    then `e` and `a–b` share the endpoint `a` and the common point `p ≠ a`, so
    both are collinear through `a`; hence `z` (on `e`) lies on the line `a–b`,
    forcing `cross (b-a)(z-a) = 0`, contradicting the hypothesis.  Preparation
    for `interior_chord_is_diagonal`.
-/
lemma chord_disjoint_ear_ab (a b c : ℂ) (rest : List ℂ) (z y : ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (e : ℂ × ℂ) (he : e ∈ closedEdges (a :: b :: c :: rest))
    (hb1 : b ≠ e.1) (hb2 : b ≠ e.2)
    (hz : z ∈ segment ℝ e.1 e.2) (hy : y ∈ segment ℝ e.1 e.2)
    (hbe : b ∉ segment ℝ e.1 e.2) (hazy : a ∉ segment ℝ z y)
    (hzab : HexArea.cross (b - a) (z - a) ≠ 0) :
    Disjoint (segment ℝ z y) (segment ℝ a b) := by
  simp_all +decide [ Set.disjoint_left, segment_eq_image ];
  intro p x hx₁ hx₂ rfl y hy₁ hy₂
  by_cases ha : a = e.1 ∨ a = e.2;
  · rcases ha with ( rfl | rfl ) <;> simp_all +decide [ HexArea.cross ];
    · obtain ⟨ u, hu₁, hu₂ ⟩ := hz; obtain ⟨ v, hv₁, hv₂ ⟩ := hy; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    · obtain ⟨ u, hu₁, hu₂ ⟩ := hz; obtain ⟨ v, hv₁, hv₂ ⟩ := hy; simp_all +decide [ Complex.ext_iff ] ;
      grind +splitImp;
  · have := hsimple.2 ( a, b ) ( by
      simp +decide [ closedEdges ] ) e he
    generalize_proofs at *;
    contrapose! this;
    simp_all +decide [ Set.disjoint_left, segment_eq_image ];
    obtain ⟨ u, hu₁, hu₂ ⟩ := hz; obtain ⟨ v, hv₁, hv₂ ⟩ := hy; use y; use hy₁, hy₂; use ( 1 - x ) * u + x * v; simp_all +decide [ Complex.ext_iff ] ;
    exact ⟨ by nlinarith, by nlinarith, by rw [ ← hu₂.1, ← hv₂.1 ] ; ring, by rw [ ← hu₂.2, ← hv₂.2 ] ; ring ⟩

/-
**A chord sub-segment lying off the line `b–c` avoids the ear edge `b–c`.**
    The `b–c` analogue of `chord_disjoint_ear_ab`.  Preparation for
    `interior_chord_is_diagonal`.
-/
lemma chord_disjoint_ear_bc (a b c : ℂ) (rest : List ℂ) (z y : ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (e : ℂ × ℂ) (he : e ∈ closedEdges (a :: b :: c :: rest))
    (hb1 : b ≠ e.1) (hb2 : b ≠ e.2)
    (hz : z ∈ segment ℝ e.1 e.2) (hy : y ∈ segment ℝ e.1 e.2)
    (hbe : b ∉ segment ℝ e.1 e.2) (hczy : c ∉ segment ℝ z y)
    (hzbc : HexArea.cross (c - b) (z - b) ≠ 0) :
    Disjoint (segment ℝ z y) (segment ℝ b c) := by
  -- Suppose there exists a point `p` in both segments.
  by_contra h_contra;
  obtain ⟨p, hp⟩ : ∃ p, p ∈ segment ℝ z y ∧ p ∈ segment ℝ b c := by
    exact Set.not_disjoint_iff.mp h_contra;
  have h_cases : c = e.1 ∨ c = e.2 := by
    contrapose! h_contra;
    have h_disjoint : Disjoint (segment ℝ e.1 e.2) (segment ℝ b c) := by
      have := hsimple.2 ( b, c ) ?_ e ?_ <;> simp_all +decide [ closedEdges ];
      exact this.symm;
    exact Set.disjoint_left.mpr fun x hxz hxz' => h_disjoint.le_bot ⟨ by exact convex_segment _ _ |> fun h => h.segment_subset hz hy hxz, hxz' ⟩;
  rcases h_cases with ( rfl | rfl ) <;> simp_all +decide [ segment_eq_image ];
  · obtain ⟨ ⟨ x, hx, rfl ⟩, ⟨ y, hy, hy' ⟩ ⟩ := hp; simp_all +decide [ Complex.ext_iff ] ;
    obtain ⟨ u, hu, hu', hu'' ⟩ := hz; obtain ⟨ v, hv, hv', hv'' ⟩ := ‹∃ x : ℝ, ( 0 ≤ x ∧ x ≤ 1 ) ∧ ( 1 - x ) * e.1.re + x * e.2.re = _ ∧ ( 1 - x ) * e.1.im + x * e.2.im = _›; simp_all +decide [ HexArea.cross ] ;
    grind;
  · obtain ⟨ ⟨ x, hx, rfl ⟩, ⟨ y, hy, hy' ⟩ ⟩ := hp; simp_all +decide [ Complex.ext_iff ] ;
    obtain ⟨ u, hu, hu' ⟩ := hz; obtain ⟨ v, hv, hv' ⟩ := ‹∃ x : ℝ, ( 0 ≤ x ∧ x ≤ 1 ) ∧ ( 1 - x ) * e.1.re + x * e.2.re = _ ∧ ( 1 - x ) * e.1.im + x * e.2.im = _›; simp_all +decide [ HexArea.cross ] ;
    grind

/-
**The Meisters interior diagonal is clear (genuine geometric core).**
    In a simple polygon `a :: b :: c :: rest` whose corner triangle `a, b, c`
    is non-degenerate, let `w ∈ rest` be a vertex strictly inside the triangle
    that is *farthest from the base line* `a–c`.  Then the chord `b–w` is
    disjoint, as a segment, from every cyclic edge of the polygon not incident
    to `b` or `w` — i.e. `b–w` is a diagonal.

    **Orientation note (important).**  Every interior vertex `x` of the corner
    triangle satisfies `cross (c-a) (x-a) = β · cross (c-a) (b-a)` for some
    `β ∈ (0,1)` (barycentric `b`-weight), so all interior vertices share the
    sign of `cross (c-a) (b-a)` and "farthest from `a–c`" means "largest `β`".
    Maximising the *signed* quantity `cross (c-a) (·-a)` is "farthest" only for
    positively-oriented triangles; for the negative orientation it picks the
    vertex *closest* to `a–c` and the chord can then run through a farther
    interior vertex (verified counterexample:
    `a=0, c=4, b=2-3i, w=2-½i, w₂=2-2i`).  Hence the correct, orientation-robust
    "farthest" hypothesis used here is `hwmax`, scaled by `cross (c-a) (b-a)`:
    `cross (c-a) (y-a) * cross (c-a) (b-a) ≤ cross (c-a) (w-a) * cross (c-a) (b-a)`,
    i.e. `w` maximises the `b`-weight `β`.

    Proof idea (Meisters' farthest-vertex argument).  The chord `b–w` lies in
    the closed corner triangle `a,b,c`, and every point of it has `b`-weight
    `≥ β(w)` (it interpolates between the apex `b`, with `β = 1`, and `w`).  A far
    edge meeting `b–w` at an interior point `z` cannot cross the two corner
    edges `a–b`, `b–c` (`far_edge_disjoint_earEdges`), and a segment crosses the
    base line `a–c` at most once; hence it has an endpoint strictly inside the
    smaller sub-triangle cut off by the line through `w` parallel to `a–c`, i.e.
    an interior vertex `y ∈ rest` with `β(y) > β(w)` — contradicting `hwmax`.

    This is the genuine Jordan-content heart of `meisters_reduction_interior2`:
    combined with the banked combinatorial split-preservation bricks
    (`HexArea.chordLeft_PolygonSimple` / `chordRight_PolygonSimple` etc.) it
    yields the two strictly-shorter simple sub-polygons of the interior split.
    NOTE: the existing `exists_farthest_interior` supplies the *unscaled*
    `hwmax` (correct only up to orientation); aligning that pivot selection to
    this orientation-robust form is the remaining bridge before this lemma can
    be consumed by `meisters_reduction_interior2`.  Recorded preparation.
-/
lemma interior_chord_is_diagonal (a b c w : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hwrest : w ∈ rest)
    (hwin : HexArea.inTriangleStrict a b c w)
    (hwmax : ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) * HexArea.cross (c - a) (b - a)
          ≤ HexArea.cross (c - a) (w - a) * HexArea.cross (c - a) (b - a)) :
    ∀ e ∈ closedEdges (a :: b :: c :: rest),
      b ≠ e.1 → b ≠ e.2 → w ≠ e.1 → w ≠ e.2 →
      Disjoint (segment ℝ b w) (segment ℝ e.1 e.2) := by
  intro e he hb1 hb2 hw1 hw2;
  by_contra h_contra;
  -- Choose the endpoint `y ∈ {e.1, e.2}` of `e` maximising `g`: since `g` is affine on `segment ℝ e.1 e.2` and `z` lies on it, `g z ≤ max (g e.1) (g e.2)`; let `y` be the maximiser, so `g y ≥ g z > g w` and `g y > 0`.
  obtain ⟨z, hz⟩ : ∃ z ∈ segment ℝ b w, z ∈ segment ℝ e.1 e.2 := by
    grind +splitImp
  obtain ⟨y, hy⟩ : ∃ y ∈ ({e.1, e.2} : Set ℂ), HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) ≥ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) := by
    have h_affine : ∀ t : ℝ, t ∈ Set.Icc 0 1 → HexArea.cross (a - c) ((1 - t) • e.1 + t • e.2 - c) * HexArea.cross (b - a) (c - b) = (1 - t) * (HexArea.cross (a - c) (e.1 - c) * HexArea.cross (b - a) (c - b)) + t * (HexArea.cross (a - c) (e.2 - c) * HexArea.cross (b - a) (c - b)) := by
      unfold HexArea.cross; norm_num [ Complex.ext_iff ] ; intros; ring;
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ z = (1 - t) • e.1 + t • e.2 := by
      rcases hz.2 with ⟨ u, v, hu, hv, huv, rfl ⟩ ; exact ⟨ v, ⟨ by linarith, by linarith ⟩, by simp +decide [ huv.symm ] ⟩ ;
    simp_all +decide [ segment_eq_image ];
    cases le_total ( HexArea.cross ( a - c ) ( e.1 - c ) * HexArea.cross ( b - a ) ( c - b ) ) ( HexArea.cross ( a - c ) ( e.2 - c ) * HexArea.cross ( b - a ) ( c - b ) ) <;> first | left; nlinarith | right; nlinarith;
  -- From `inTriangleStrict a b c w` (`cases hwin`) and `t ∈ (0,1)`, derive (each by `nlinarith` after `unfold HexArea.cross` / using the three corner tests at `w`):
  -- - `cross (b-a)(z-a) * O > 0`  [hence `cross (b-a)(z-a) ≠ 0`],
  -- - `cross (c-b)(z-b) * O > 0`  [hence `cross (c-b)(z-b) ≠ 0`],
  -- - `g z > g w` and `g z > 0`  (`g z = (1-t)*(cross (c-a)(b-a))^2 + t*g w`, and `(cross (c-a)(b-a))^2 > g w` for interior `w`).
  have hz_pos : HexArea.cross (b - a) (z - a) * HexArea.cross (b - a) (c - b) > 0 ∧ HexArea.cross (c - b) (z - b) * HexArea.cross (b - a) (c - b) > 0 ∧ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) > HexArea.cross (a - c) (w - c) * HexArea.cross (b - a) (c - b) ∧ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) > 0 := by
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, z = (1 - t) • b + t • w := by
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, z = (1 - t) • b + t • w := by
        rw [ segment_eq_image ] at hz ; aesop;
      refine' ⟨ t, ⟨ lt_of_le_of_ne ht.1.1 _, lt_of_le_of_ne ht.1.2 _ ⟩, ht.2 ⟩ <;> rintro rfl <;> simp_all +decide [ segment_eq_image ];
      · obtain ⟨ x, hx, hx' ⟩ := hz.2;
        have := simple_vertex_not_on_far_edge ( a :: b :: c :: rest ) ( by
          grind +splitImp ) hsimple b ( by
          simp +decide ) e he hb1 hb2;
        exact this ⟨ 1 - x, x, by aesop ⟩;
      · have := simple_vertex_not_on_far_edge ( a :: b :: c :: rest ) ( by
          grind ) hsimple w ( by
          grind ) e he hw1 hw2; simp_all +decide [ segment_eq_image ] ;
    rcases hwin with ( hwin | hwin ) <;> simp_all +decide [ HexArea.cross ];
    · refine' ⟨ _, _, _, _ ⟩;
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.mpr ht.1.2 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.2 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.2 ) ];
    · refine' ⟨ _, _, _, _ ⟩;
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.mpr ht.1.2 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.mpr hwin.2.2 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.1 ), mul_pos ( sub_pos.mpr ht.1.2 ) ( sub_pos.mpr hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
      · nlinarith [ mul_pos ht.1.1 ( sub_pos.2 ht.1.2 ), mul_pos ht.1.1 ( sub_pos.2 hwin.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.1 ), mul_pos ht.1.1 ( sub_pos.2 hwin.2.2 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.1 ), mul_pos ( sub_pos.2 ht.1.2 ) ( sub_pos.2 hwin.2.2 ) ];
  -- From `hy`, `hz_pos`, and `hwmax`, we get `y ∈ rest` and `¬ inTriangleStrict a b c y`.
  have hy_rest : y ∈ rest := by
    have hy_rest : y ∈ a :: b :: c :: rest := by
      have := List.of_mem_zip he; simp_all +decide [ List.mem_rotate ] ;
      grind +ring;
    by_cases hya : y = a <;> by_cases hyc : y = c <;> simp_all +decide;
    · unfold HexArea.cross at * ; aesop;
    · linarith;
    · simp_all +decide [ HexArea.cross ];
      linarith;
    · grind
  have hy_not_in_triangle : ¬ HexArea.inTriangleStrict a b c y := by
    intro hy_in_triangle
    have := hwmax y hy_rest hy_in_triangle
    simp_all +decide [ HexArea.cross ];
    linarith [ hwmax y hy_rest hy_in_triangle ];
  -- From `hy`, `hz_pos`, and `hwmax`, we get `b ∉ segment ℝ e.1 e.2` and `a ∉ segment ℝ z y` and `c ∉ segment ℝ z y`.
  have hb_not_in_segment : b ∉ segment ℝ e.1 e.2 := by
    apply simple_vertex_not_on_far_edge (a :: b :: c :: rest) (by
    grind) hsimple b (by
    simp +decide) e he hb1 hb2
  have ha_not_in_segment : a ∉ segment ℝ z y := by
    intro ha_in_segment
    have h_cross_zero : HexArea.cross (a - c) (a - c) * HexArea.cross (b - a) (c - b) = 0 := by
      unfold HexArea.cross; ring;
    have h_cross_zero : ∀ t : ℝ, t ∈ Set.Icc 0 1 → HexArea.cross (a - c) ((1 - t) • z + t • y - c) * HexArea.cross (b - a) (c - b) = (1 - t) * HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) + t * HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) := by
      intros t ht
      simp [HexArea.cross]
      ring;
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ a = (1 - t) • z + t • y := by
      rw [ segment_eq_image ] at ha_in_segment;
      rcases ha_in_segment with ⟨ t, ht, rfl ⟩ ; exact ⟨ t, ht, rfl ⟩ ;
    norm_num [ ht.2 ] at *;
    specialize h_cross_zero t ht.1 ht.2 ; norm_num at h_cross_zero ; nlinarith
  have hc_not_in_segment : c ∉ segment ℝ z y := by
    intro hc_in_segment
    have h_cross_zero : HexArea.cross (a - c) (c - c) * HexArea.cross (b - a) (c - b) = 0 := by
      unfold HexArea.cross; norm_num;
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ c = (1 - t) • z + t • y := by
      rw [ segment_eq_image ] at hc_in_segment; obtain ⟨ t, ht, rfl ⟩ := hc_in_segment; exact ⟨ t, ht, rfl ⟩ ;
    have h_cross_zero : HexArea.cross (a - c) (c - c) * HexArea.cross (b - a) (c - b) = (1 - t) * HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) + t * HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) := by
      rw [ht.right];
      unfold HexArea.cross; norm_num; ring;
    nlinarith [ ht.1.1, ht.1.2 ];
  have := HexArea.corner_exit_point_ge a b c z y hndtri hz_pos.1 hz_pos.2.1 hz_pos.2.2.2.le (by
  linarith) hy_not_in_triangle;
  rcases this with ( ⟨ p, hp₁, hp₂ ⟩ | ⟨ p, hp₁, hp₂ ⟩ );
  · have := chord_disjoint_ear_ab a b c rest z y hsimple e he hb1 hb2 hz.2 (by
    rcases hy.1 with ( rfl | rfl ) <;> [ exact left_mem_segment _ _ _; exact right_mem_segment _ _ _ ]) hb_not_in_segment ha_not_in_segment (by
    exact fun h => by simp_all +decide [ HexArea.cross ] ;);
    exact this.le_bot ⟨ hp₁, hp₂ ⟩;
  · have := chord_disjoint_ear_bc a b c rest z y hsimple e he hb1 hb2 hz.2 (by
    rcases hy.1 with ( rfl | rfl ) <;> [ exact left_mem_segment _ _ _; exact right_mem_segment _ _ _ ]) hb_not_in_segment hc_not_in_segment (by
    exact fun h => by simp_all +decide [ HexArea.cross ] ;);
    exact this.le_bot ⟨ hp₁, hp₂ ⟩

/-- **Empty-branch lift — the BOUNDARY subcase (genuine remaining gap).**  Same
    hypotheses as `empty_branch_good_lift`, used to discharge the residual case
    where the ear returned by the induction hypothesis on the clip `a :: c ::
    rest` is *adjacent* to the `a–c` junction (its tail does not decompose as
    `s ++ a :: c :: t` with the junction interior).  In that boundary case
    re-inserting the apex `b` turns a clip neighbour of the ear into `b`, so the
    lifted clip-turn `cross (c - b) (·)` can vanish (the genuine two-ears
    subtlety): the ear may fail the `EmptyCornerData2` clip-turn clause and a
    different ear (or a finer induction invariant forcing the returned ear into
    the interior arc) is required.

    **Status: `sorry`.**  This is the isolated genuine Jordan-content gap of the
    empty branch; the *interior* subcase is fully proved (via
    `empty_branch_interior_lift`) and dispatched here from
    `empty_branch_good_lift`.  Recorded, isolated partial progress — NOT a dead
    branch. -/
lemma empty_branch_boundary_lift (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ) (p q : ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpl : HexArea.cross (c - a) (p - a) ≠ 0)
    (hql : HexArea.cross (c - a) (q - a) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hbf : b = z1 ∨ b = z2)
    (a' b' c' p' q' : ℂ) (rest' : List ℂ) (r' : ℕ)
    (hrot' : (a :: c :: rest).rotate r' = a' :: b' :: c' :: rest')
    (hb'a : b' ≠ a) (hb'c : b' ≠ c)
    (hp'M : rest'.getLast? = some p') (hq'M : rest'.head? = some q')
    (hpt' : HexArea.cross (a' - p') (c' - a') ≠ 0)
    (hqt' : HexArea.cross (c' - a') (q' - c') ≠ 0)
    (hempty' : ∀ x ∈ rest', ¬ HexArea.inTriangleStrict a' b' c' x)
    (hdiag' : ∀ x ∈ rest', x ∉ segment ℝ a' c')
    (horient' : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: rest')))
    (hnotint : ¬ ∃ s t, rest' = s ++ a :: c :: t) :
    EmptyCornerData2 V z1 z2 := by
  sorry

/-- **Empty-branch lift — the "good diagonal" subcase (PROVED modulo the boundary
    subcase).**
    This is the half of `meisters_reduction_empty2`'s non-clean case in which the
    clip diagonal `a–c` is *clean*: both clip neighbours `p, q` lie off the line
    `a–c` (`hpl`, `hql`), no far vertex sits on the closed diagonal (`hdiag`),
    and the ear orientation matches the clip (`horient`).  Since the overall
    branch is non-clean while the diagonal is clean, the only obstruction is that
    the convex apex `b` coincides with a forbidden vertex (`hbf : b = z1 ∨
    b = z2`).  We recurse via `IH2` on the strictly-shorter clip `a :: c :: rest`
    (simple and non-degenerate by `clip_simple_nondeg_of_empty`) forbidding the
    clip diagonal `{a, c}` (a genuine cyclic edge of the clip), and lift the
    returned ear — whose tip lies in `rest`, hence avoids `a`, `c`, and (by
    Nodup) `b` — back to `V`.  Because `b`'s only cyclic neighbours in `V` are
    `a` and `c`, the lifted tip avoids both forbidden vertices `z1, z2` (one is
    `b`, the other a neighbour of `b`, i.e. in `{a, c}`).  The orientation /
    diagonal data transfer using `horient` and `hbconv`.

    **Status: proved.**  This lemma is now sorry-free: it recurses on the clip
    via `IH2`, then `by_cases` on whether the returned ear's tail decomposes as
    `s ++ a :: c :: t` (the `a–c` junction interior).  The *interior* subcase is
    discharged by the fully-proved `empty_branch_interior_lift` (the list-surgery
    rotation lift plus the orientation-sign transfer); the *boundary* subcase
    (ear adjacent to the junction) is dispatched to `empty_branch_boundary_lift`,
    which carries the single genuine remaining Jordan-content `sorry` of the
    empty branch.  Consumed by `meisters_reduction_empty2` (good-diagonal
    subcase). -/
lemma empty_branch_good_lift (V : List ℂ) (hlen : 5 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ) (p q : ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpl : HexArea.cross (c - a) (p - a) ≠ 0)
    (hql : HexArea.cross (c - a) (q - a) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hbf : b = z1 ∨ b = z2) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨hac, hanr, hbnr, hbnea, hbnec⟩ : a ≠ c ∧ a ∉ rest ∧ b ∉ rest ∧ b ≠ a ∧ b ≠ c := by
    have hrot_nodup : List.Nodup (V.rotate r) := by
      exact List.nodup_rotate.mpr hsimple.1;
    grind +qlia;
  have hABCne : HexArea.cross (b - a) (c - b) ≠ 0 := by
    convert polyCycNondeg_rotate_head V a b c rest r ( by omega ) hnd hrot using 1
  have hlenrot := congrArg List.length hrot
  simp at hlenrot
  have hMs : PolygonSimple (a :: c :: rest) := by
    apply (clip_simple_nondeg_of_empty a b c p q rest hp hq (hrot ▸ (PolygonSimple_rotate V r).2 hsimple) (hrot ▸ (polyCycNondeg_rotate V r (by omega)).mpr hnd) hABCne (sub_ne_zero_of_ne hac.symm) hempty hdiag (HexArea.clip_turn_at_a_ne_zero a c p hpl) (HexArea.clip_turn_at_c_ne_zero a c q hql)).left
  have hMn : polyCycNondeg (a :: c :: rest) := by
    apply (clip_simple_nondeg_of_empty a b c p q rest hp hq (by
    exact hrot ▸ ( PolygonSimple_rotate V r ).2 hsimple) (by
    convert hrot ▸ ( polyCycNondeg_rotate V r ( by linarith ) ) |>.mpr hnd using 1) hABCne (sub_ne_zero_of_ne hac.symm) hempty hdiag (HexArea.clip_turn_at_a_ne_zero a c p hpl) (HexArea.clip_turn_at_c_ne_zero a c q hql)).right
  have hMlen : 4 ≤ (a :: c :: rest).length := by
    grind
  have hadjM : IsCycEdge (a :: c :: rest) a c := by
    unfold IsCycEdge; simp +decide [ closedEdges ] ;
  obtain ⟨r', a', b', c', p'M, q'M, rest', hrot', hb'a, hb'c, hp'M, hq'M, hpt', hqt', hempty', hdiag', horient'⟩ := IH2 (a :: c :: rest) (by simp; omega) hMlen hMs hMn a c (Or.inr hadjM);
  obtain ⟨ha'M, hb'M, hc'M, hrest'M⟩ := rotate_cons3_mem (a :: c :: rest) a' b' c' rest' r' hrot';
  obtain ⟨hb'rest, ha'V, hb'V, hc'V⟩ : b' ∈ rest ∧ a' ∈ V ∧ b' ∈ V ∧ c' ∈ V := by
    replace hrot := congr_arg List.toFinset hrot; rw [ Finset.ext_iff ] at hrot; have := hrot a; have := hrot b; have := hrot c; have := hrot b'; have := hrot c'; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
    grind +qlia;
  have ha'b : b ≠ a' := by
    grind +ring
  have hc'b : b ≠ c' := by
    grind +ring
  have hA'ne : HexArea.cross (b' - a') (c' - b') ≠ 0 := by
    convert polyCycNondeg_rotate_head ( a :: c :: rest ) a' b' c' rest' r' ( by simp; omega ) hMn hrot' using 1
  have hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2 := by
    have := forbidden_subset_corner V r a b c rest hsimple hrot z1 z2 hadj hbf;
    have := hMs.1; simp_all +decide [ List.nodup_cons ] ;
    grind +ring
  generalize_proofs at *; (
  by_cases hnotint : ∃ s t, rest' = s ++ a :: c :: t;
  · obtain ⟨ s, t, rfl ⟩ := hnotint;
    apply empty_branch_interior_lift V z1 z2 a b c rest r hrot hac hanr hbconv hbseg horient hABCne hzrest a' b' c' p'M q'M s t r' hrot' hb'rest ha'V hb'V hc'V ha'b hc'b hA'ne hp'M hq'M hpt' hqt' hempty' hdiag' horient';
  · exact empty_branch_boundary_lift V ( by omega ) hsimple hnd z1 z2 hadj IH2 r a b c rest p q hrot hbmem hbconv hbseg hp hq hpl hql hempty hdiag horient hbf a' b' c' p'M q'M rest' r' hrot' hb'a hb'c hp'M hq'M hpt' hqt' hempty' hdiag' horient' hnotint)

/-- **Edge-forbidden selection (pure finite logic).**  If `x ≠ y` and the
    *ordered* pair `(x, y)` and its reverse `(y, x)` are both absent from the
    cyclic edges of `V` (i.e. `{x, y}` is a diagonal, not an edge), then any
    forbidden pair `z1, z2` that is equal or a cyclic edge must miss at least
    one of `x, y`.  This is the combinatorial heart of the quadrilateral
    two-ears base case: the two ears sit at the *diagonal* pair, which no edge
    can cover.  Consumed by `meisters_reduction_quad2`. -/
lemma forbidden_avoids_one (V : List ℂ) (x y z1 z2 : ℂ) (hxy : x ≠ y)
    (hxy1 : (x, y) ∉ closedEdges V) (hxy2 : (y, x) ∉ closedEdges V)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2) :
    (x ≠ z1 ∧ x ≠ z2) ∨ (y ≠ z1 ∧ y ≠ z2) := by
  rcases hadj with rfl | hedge
  · by_cases hx : x = z1
    · exact Or.inr ⟨fun h => hxy ((h.trans hx.symm).symm),
        fun h => hxy ((h.trans hx.symm).symm)⟩
    · exact Or.inl ⟨hx, hx⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- after push_neg: `h1 : x ≠ z1 → x = z2`, `h2 : y ≠ z1 → y = z2`.
    have hx : x = z1 ∨ x = z2 := by
      by_contra hh; push_neg at hh; exact hh.2 (h1 hh.1)
    have hy : y = z1 ∨ y = z2 := by
      by_contra hh; push_neg at hh; exact hh.2 (h2 hh.1)
    rcases hedge with he | he
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        first
        | (exfalso; exact hxy (hx.trans hy.symm))
        | (subst hx; subst hy; exact hxy1 he)
        | (subst hx; subst hy; exact hxy2 he)
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        first
        | (exfalso; exact hxy (hx.trans hy.symm))
        | (subst hx; subst hy; exact hxy2 he)
        | (subst hx; subst hy; exact hxy1 he)

/-
**Ear at `b` of a quadrilateral (rotation 0).**  When `a–c` is an interior
    diagonal (`H`), the vertex `b` is an empty ear; if it avoids `z1, z2` the
    `EmptyCornerData2` is the rotation-0 package.  Mirrors the `H`-left,
    `b ≠ z` branch of `meisters_reduction_quad`.
-/
lemma quad_ear_at_b (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (c - a) (b - a) * HexArea.cross (c - a) (d - a) < 0)
    (hbz1 : b ≠ z1) (hbz2 : b ≠ z2) :
    EmptyCornerData2 [a, b, c, d] z1 z2 := by
  refine' ⟨ 0, a, b, c, d, d, [ d ], _, _, _, _, _ ⟩ <;> norm_num;
  · assumption;
  · assumption;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    · contrapose! H;
      have := HexArea.inTriangleStrict_apex_sameSide a b c d H;
      linarith;
    · exact not_mem_segment_of_cross_ne a c d ( by aesop );
    · unfold HexArea.shoelace2 at *; simp_all +decide [ HexArea.cross ] ;
      constructor <;> intro <;> nlinarith

/-
**Ear at `d` of a quadrilateral (rotation 2).**  The opposite ear of the
    `a–c` interior-diagonal case.  Mirrors the `H`-left, `b = z` branch of
    `meisters_reduction_quad` (which produces the opposite ear `d`).
-/
lemma quad_ear_at_d (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (c - a) (b - a) * HexArea.cross (c - a) (d - a) < 0)
    (hdz1 : d ≠ z1) (hdz2 : d ≠ z2) :
    EmptyCornerData2 [a, b, c, d] z1 z2 := by
  refine' ⟨ 2, c, d, a, b, b, [ b ], _, _, _, _, _ ⟩ <;> norm_num at *;
  · assumption;
  · assumption;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · contrapose! hbc; simp_all +decide [ HexArea.cross ] ;
      grind;
    · contrapose! H; simp_all +decide [ HexArea.cross ] ;
      grind +qlia;
    · unfold HexArea.inTriangleStrict; norm_num [ Complex.ext_iff ] ;
      unfold HexArea.cross at * ; norm_num [ Complex.ext_iff ] at * ; constructor <;> intros <;> nlinarith;
    · contrapose! H; simp_all +decide [ HexArea.cross ] ;
      rw [ segment_eq_image ] at H ; obtain ⟨ θ, hθ, rfl ⟩ := H ; norm_num [ Complex.ext_iff ] at * ; ring_nf at * ; norm_num at *;
    · unfold HexArea.shoelace2 HexArea.cross at * ; norm_num [ Complex.ext_iff ] at *;
      unfold HexArea.cross ;
      constructor <;> intro <;> nlinarith

/-
**Ear at `c` of a quadrilateral (rotation 1).**  When `b–d` is an interior
    diagonal (`H`), `c` is an empty ear.  Mirrors the `H`-right, `c ≠ z` branch
    of `meisters_reduction_quad`.
-/
lemma quad_ear_at_c (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (d - b) (a - b) * HexArea.cross (d - b) (c - b) < 0)
    (hcz1 : c ≠ z1) (hcz2 : c ≠ z2) :
    EmptyCornerData2 [a, b, c, d] z1 z2 := by
  refine' ⟨ 1, b, c, d, a, a, [ a ], _, _, _, _, _ ⟩ <;> simp_all +decide [ EmptyCornerData2 ];
  refine' ⟨ _, _, _, _, _ ⟩;
  · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
    grind +qlia;
  · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
    grind;
  · unfold HexArea.inTriangleStrict;
    unfold HexArea.cross at * ; norm_num [ Complex.ext_iff ] at * ;
    constructor <;> intros <;> nlinarith;
  · rw [ segment_eq_image ] ; contrapose! H ; simp_all +decide [ HexArea.cross ];
    obtain ⟨ x, hx, rfl ⟩ := H; norm_num [ Complex.ext_iff ] ; ring_nf;
    norm_num;
  · unfold HexArea.shoelace2; simp +decide [ HexArea.cross ] ;
    unfold HexArea.cross at * ; norm_num [ Complex.ext_iff ] at * ; constructor <;> intro <;> nlinarith

/-
**Ear at `a` of a quadrilateral (rotation 3).**  The opposite ear of the
    `b–d` interior-diagonal case.  Mirrors the `H`-right, `c = z` branch of
    `meisters_reduction_quad` (which produces the opposite ear `a`).
-/
lemma quad_ear_at_a (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (d - b) (a - b) * HexArea.cross (d - b) (c - b) < 0)
    (haz1 : a ≠ z1) (haz2 : a ≠ z2) :
    EmptyCornerData2 [a, b, c, d] z1 z2 := by
  use 3, d, a, b, c, c, [c];
  simp_all +decide [ HexArea.cross, HexArea.shoelace2, HexArea.inTriangleStrict ];
  refine' ⟨ _, _, _, _, _ ⟩;
  · grind;
  · grind;
  · constructor <;> intros <;> nlinarith;
  · contrapose! H;
    obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := H;
    norm_num [ show u = 1 - v by linarith ] at *;
    nlinarith [ mul_nonneg hv ( sq_nonneg ( d.re - b.re ) ), mul_nonneg hv ( sq_nonneg ( d.im - b.im ) ) ];
  · constructor <;> intro <;> nlinarith

/-- **The quadrilateral base case in the two-forbidden form.**  A simple,
    non-degenerate quadrilateral, together with a forbidden pair `z1, z2` that
    is either equal or a genuine cyclic edge, has an empty corner whose tip
    avoids both.  The two ears of a quadrilateral are at *opposite* corners
    (non-adjacent), so an edge — whose endpoints are adjacent — can never
    contain both ear tips; hence at least one ear survives.  Genuine finite
    two-ears content; consumed by `meisters_reduction2`.

    **Status: `sorry`.**  True statement (the quadrilateral two-ears fact); the
    finite case analysis mirrors `meisters_reduction_quad` (which already dodges
    a single forbidden vertex to the opposite ear) but must dodge an entire
    edge.  Recorded partial progress toward the Umlaufsatz. -/
lemma meisters_reduction_quad2 (V : List ℂ) (h4 : V.length = 4)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, V = [a, b, c, d] := by
    rcases V with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | t⟩⟩⟩⟩ <;> simp_all
  -- The four consecutive-triple non-degeneracies.
  obtain ⟨hab, hbc, hcd, hda⟩ : HexArea.cross (b - a) (c - b) ≠ 0 ∧
      HexArea.cross (c - b) (d - c) ≠ 0 ∧ HexArea.cross (d - c) (a - d) ≠ 0 ∧
      HexArea.cross (a - d) (b - a) ≠ 0 := by
    unfold polyCycNondeg at hnd; simp_all +decide [polyNondeg]
  -- The two opposite-edge disjointnesses.
  obtain ⟨hdisj1, hdisj2⟩ : Disjoint (segment ℝ a b) (segment ℝ c d) ∧
      Disjoint (segment ℝ b c) (segment ℝ d a) := by
    have := hsimple.2; simp_all +decide [closedEdges]; grind +locals
  -- Vertex distinctness from `Nodup`.
  have hnd4 := hsimple.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil] at hnd4
  have hbd : b ≠ d := by tauto
  have hac : a ≠ c := by tauto
  -- The two diagonals are not cyclic edges.
  have hCE : closedEdges [a, b, c, d] = [(a, b), (b, c), (c, d), (d, a)] := by
    simp [closedEdges, List.rotate]
  have hbd1 : (b, d) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  have hbd2 : (d, b) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  have hac1 : (a, c) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  have hac2 : (c, a) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  -- One diagonal is interior; its two endpoints are the two opposite ears.
  rcases quad_diagonal_interior a b c d hab hbc hcd hda hdisj1 hdisj2 with H | H
  · -- `a–c` interior: ears at `b` and `d`.
    rcases forbidden_avoids_one [a, b, c, d] b d z1 z2 hbd hbd1 hbd2 hadj with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact quad_ear_at_b a b c d z1 z2 hab hbc hcd hda H h1 h2
    · exact quad_ear_at_d a b c d z1 z2 hab hbc hcd hda H h1 h2
  · -- `b–d` interior: ears at `a` and `c`.
    rcases forbidden_avoids_one [a, b, c, d] a c z1 z2 hac hac1 hac2 hadj with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact quad_ear_at_a a b c d z1 z2 hab hbc hcd hda H h1 h2
    · exact quad_ear_at_c a b c d z1 z2 hab hbc hcd hda H h1 h2

/-- **Meisters interior branch (open Jordan-curve core), two-forbidden form.**
    The convex corner `a, b, c` (with `b` the lex-minimal, hence convex, middle
    vertex of the rotated cycle `V.rotate r = a :: b :: c :: rest`) is *not*
    empty: `w ∈ rest` is the interior vertex farthest from the base diagonal
    `a–c`.  The chord `b–w` is then an interior diagonal of `V`; splitting `V`
    along it (`chordLeft`/`chordRight` in `SAWUmlaufEarSplit`) yields two
    strictly shorter simple non-degenerate sub-polygons.  The forbidden edge
    `{z1, z2}` lies entirely in one of the two pieces, so recursing through
    `IH2` on the *other* piece — forbidding the cut diagonal `{b, w}` (a cyclic
    edge of that piece) — returns an ear whose tip is interior to that piece,
    hence avoids `{b, w}` and therefore lifts to an ear of `V` avoiding
    `{z1, z2}`.  This is the crux that the single-forbidden form could not
    express.  Consumed by `meisters_reduction2`.

    **Status: `sorry`.**  Genuine Jordan-curve-theorem-level content (interior
    diagonal split preserving `PolygonSimple`/`polyCycNondeg`, plus the ear
    lift); absent from Mathlib.  Recorded partial progress. -/
lemma meisters_reduction_interior2 (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (h4 : ¬ V.length = 4)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hcase : ∃ x ∈ rest, HexArea.inTriangleStrict a b c x)
    (w : ℂ) (hwrest : w ∈ rest) (hwin : HexArea.inTriangleStrict a b c w)
    (hwmax : ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) ≤ HexArea.cross (c - a) (w - a)) :
    EmptyCornerData2 V z1 z2 := by
  sorry

/-- **Meisters empty/diagonal branch, two-forbidden form.**  No vertex of
    `rest` lies in the strict interior of the convex corner `a, b, c`.  If `b`
    is a *bona-fide* empty ear avoiding both `z1` and `z2` (the clean case,
    proved here directly via the `EmptyCornerData2` packaging), use it.
    Otherwise — `b` coincides with a forbidden vertex, or a clip endpoint is
    collinear, or a far vertex sits on the closed diagonal, or the orientation
    is reversed — recurse via `IH2` on the clip `a :: c :: rest` forbidding the
    clip diagonal `{a, c}` (a cyclic edge of the clip), and lift the returned
    ear (whose tip lies in `rest`, hence avoids `a`, `c`, and `b`) back to `V`.
    Consumed by `meisters_reduction2`.

    **Status: clean case proved; non-clean case `sorry`.**  The non-clean lift
    re-inserts the convex apex `b` between `a` and `c`; the returned ear's tip
    in `rest` keeps its cyclic neighbours, and `b` stays outside the lifted ear
    triangle by `hbconv`.  The clip preservation is already available as
    `clip_simple_nondeg_of_empty`; the residual content is the list-surgery
    lift.  Recorded partial progress. -/
lemma meisters_reduction_empty2 (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (h4 : ¬ V.length = 4)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hcase : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) :
    EmptyCornerData2 V z1 z2 := by
  -- `rest` is nonempty: `V.length ≥ 5`, so `rest.length = V.length - 3 ≥ 2`.
  have hrest_len : 2 ≤ rest.length := by
    have hl := congrArg List.length hrot
    simp only [List.length_rotate, List.length_cons] at hl
    omega
  obtain ⟨p, hp⟩ : ∃ p, rest.getLast? = some p := by
    cases hr : rest.getLast? with
    | none => exfalso; rw [List.getLast?_eq_none_iff] at hr; subst hr; simp at hrest_len
    | some p => exact ⟨p, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, rest.head? = some q := by
    cases hr : rest.head? with
    | none => exfalso; rw [List.head?_eq_none_iff] at hr; subst hr; simp at hrest_len
    | some q => exact ⟨q, rfl⟩
  by_cases hclean : (b ≠ z1 ∧ b ≠ z2) ∧ HexArea.cross (c - a) (p - a) ≠ 0 ∧
      HexArea.cross (c - a) (q - a) ≠ 0 ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))
  · -- **Clean case (proved).**  `b` avoids both forbidden vertices, both clip
    -- endpoints `p, q` lie off the line `a–c`, no far vertex sits on the closed
    -- diagonal, and the ear orientation matches the clip: assemble
    -- `EmptyCornerData2` directly.
    obtain ⟨⟨hbz1, hbz2⟩, hpl, hql, hdiag, horient⟩ := hclean
    exact ⟨r, a, b, c, p, q, rest, hrot, hbz1, hbz2, hp, hq,
      HexArea.clip_turn_at_a_ne_zero a c p hpl,
      HexArea.clip_turn_at_c_ne_zero a c q hql,
      hcase, hdiag, horient⟩
  · -- **Non-clean case.**  Split on whether the clip diagonal `a–c` is itself
    -- *clean* (neighbours `p, q` off the line, no far vertex on the closed
    -- diagonal, ear orientation matching).
    by_cases hgood : HexArea.cross (c - a) (p - a) ≠ 0 ∧
        HexArea.cross (c - a) (q - a) ≠ 0 ∧
        (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
        ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))
    · -- **Good-diagonal subcase (consumed by `empty_branch_good_lift`).**  The
      -- diagonal is clean, so the only reason the corner failed the clean test
      -- is that the apex `b` is a forbidden vertex.  Recurse on the clip and
      -- lift; no polygon splitting needed.
      obtain ⟨hpl, hql, hdiag, horient⟩ := hgood
      have hbf : b = z1 ∨ b = z2 := by
        by_contra h
        push_neg at h
        exact hclean ⟨h, hpl, hql, hdiag, horient⟩
      exact empty_branch_good_lift V (by omega) hsimple hnd z1 z2 hadj IH2 r a b c rest
        p q hrot hbmem hbconv hbseg hp hq hpl hql hcase hdiag horient hbf
    · -- **Bad-diagonal subcase (remaining Jordan gap).**  A clip neighbour is
      -- collinear with `a–c`, or a far vertex sits on the *closed* diagonal, or
      -- the ear orientation is reversed.  The clip is then no longer a clean
      -- simple sub-polygon, so this case genuinely needs the polygon-split
      -- machinery (as in `meisters_reduction_interior2`): a blocking vertex on
      -- the diagonal yields a strictly-shorter interior diagonal to split
      -- along.  This is the isolated remaining gap of the empty branch.
      sorry

/-- **The geometric reduction step of the Meisters two-ears search (two-forbidden
    form), now carrying the strong-induction hypothesis.**  Dispatches the
    quadrilateral base case, the lex-minimal convex-vertex setup, and the
    interior / empty dichotomy to the three branch lemmas above. -/
lemma meisters_reduction2 (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2) :
    EmptyCornerData2 V z1 z2 := by
  by_cases h4 : V.length = 4
  · exact meisters_reduction_quad2 V h4 hsimple hnd z1 z2 hadj
  -- From here `V.length ≥ 5`.
  obtain ⟨r, a, b, c, rest, hrot, hbmem, hbconv, hbseg⟩ :=
    exists_lexmin_mid_rotation V (by omega)
  by_cases hcase : ∃ x ∈ rest, HexArea.inTriangleStrict a b c x
  · -- **Interior branch (Meisters' diagonal split).**
    obtain ⟨w, hwrest, hwin, hwmax⟩ := exists_farthest_interior a b c rest hcase
    exact meisters_reduction_interior2 V hlen hsimple hnd z1 z2 hadj IH2 h4 r a b c
      rest hrot hbmem hbconv hbseg hcase w hwrest hwin hwmax
  · -- **Empty/diagonal branch.**
    push_neg at hcase
    exact meisters_reduction_empty2 V hlen hsimple hnd z1 z2 hadj IH2 h4 r a b c
      rest hrot hbmem hbconv hbseg hcase

/-- **Strong-induction wrapper (sorry-free), two-forbidden form.**  Discharges
    the induction hypothesis of `meisters_reduction2` by strong induction on the
    polygon length, leaving the genuine geometric content concentrated in the
    branch lemmas. -/
lemma exists_empty_corner_avoiding_aux2 :
    ∀ (n : ℕ) (V : List ℂ), V.length = n → 4 ≤ V.length →
      PolygonSimple V → polyCycNondeg V →
      ∀ z1 z2 : ℂ, (z1 = z2 ∨ IsCycEdge V z1 z2) → EmptyCornerData2 V z1 z2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V hn hlen hsimple hnd z1 z2 hadj
    refine meisters_reduction2 V hlen hsimple hnd z1 z2 hadj ?_
    intro V' hlt h4 hs' hnd' w1 w2 hadj'
    exact IH V'.length (by omega) V' rfl h4 hs' hnd' w1 w2 hadj'

/-- **Strong-induction wrapper (sorry-free).**  The single-forbidden
    `EmptyCornerData` is the diagonal case of the two-forbidden
    `exists_empty_corner_avoiding_aux2`. -/
lemma exists_empty_corner_avoiding_aux :
    ∀ (n : ℕ) (V : List ℂ), V.length = n → 4 ≤ V.length →
      PolygonSimple V → polyCycNondeg V → ∀ z : ℂ, EmptyCornerData V z := by
  intro n V hn hlen hsimple hnd z
  exact EmptyCornerData_of_two V z
    (exists_empty_corner_avoiding_aux2 n V hn hlen hsimple hnd z z (Or.inl rfl))

lemma exists_empty_corner_avoiding (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z : ℂ) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      HexArea.cross (a - p) (c - a) ≠ 0 ∧ HexArea.cross (c - a) (q - c) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) :=
  exists_empty_corner_avoiding_aux V.length V rfl hlen hsimple hnd z

/-- **The empty-convex-ear existence core, in the inductively-correct
    "forbidden-vertex" form (the genuine Meisters TWO-ears content).**  A
    simple, non-degenerate polygon with at least four vertices, together with
    *any* single forbidden vertex `z`, has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose middle vertex `b` is an empty
    convex ear **with tip `b ≠ z`**: the corner triangle `a b c` is
    non-degenerate, contains no far vertex strictly inside (`hempty`) and none
    on the closed diagonal `a–c` (`hdiag`), the five cyclic edge
    non-degeneracies hold, the clipped cycle `a :: c :: rest` is still
    cyclically non-degenerate, and the cut-off ear triangle has the *same
    orientation* as the clip (`0 < shoelace2 [a,b,c] ↔
    0 < shoelace2 (a :: c :: rest)`).

    **Why the forbidden vertex `z`.**  The bare one-ear statement
    `exists_empty_convex_ear` (derived below) is *not* directly amenable to the
    split-and-recurse induction: splitting a simple polygon along an interior
    diagonal `d` yields two strictly shorter simple sub-polygons, but the
    *single* ear handed back by a one-ear induction hypothesis on a sub-polygon
    may have its tip at an endpoint of `d`, in which case it is **not** an ear
    of the original polygon.  The standard Meisters fix is the genuine TWO-ears
    theorem; the cleanest inductive packaging of "≥ 2 ears" is exactly this
    forbidden-vertex form: with `z` set to the far diagonal endpoint, the
    recursion returns an ear of the sub-polygon avoiding `z`, which therefore
    survives as an ear of the whole polygon.  Deriving the one-ear corollary is
    then trivial (instantiate `z` arbitrarily).

    This is the irreducible Jordan-curve-theorem-level core (absent from
    Mathlib).  Intended route: strong induction on `V.length`.  Choose the
    extreme (leftmost-lowest) convex vertex via `HexArea.exists_lex_min_mem` /
    `lexMin_not_inTriangleStrict`; if its corner triangle is empty it is the
    ear (use it, or its cyclic neighbour, to avoid `z`); otherwise pivot to the
    vertex farthest from the base diagonal (`HexArea.exists_max_cross`,
    `farthest_region_empty`, `inTriangleStrict_pos_nest`,
    `subTri_axc_orient_pos`, `inTriangleStrict_apex_sameSide`), split along the
    resulting interior diagonal and recurse on the strictly shorter
    sub-polygons.  Recorded partial progress: consumed by
    `exists_empty_convex_ear` immediately below. -/
lemma exists_empty_convex_ear_avoiding (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z : ℂ) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  -- **The genuine Meisters search (the single remaining open core).**  Find a
  -- cyclic rotation exhibiting an *empty* corner `a,b,c` (tip `b ≠ z`) whose two
  -- clip corners `(p,a,c)` and `(a,c,q)` are non-flat and whose ear orientation
  -- matches the clip.  All the remaining ear-data bookkeeping is then discharged
  -- by `ear_data_of_empty_corner` below.
  obtain ⟨r, a, b, c, p, q, rest, hrot, hbz, hp, hq, hclipa, hclipc, hempty, hdiag,
      horient⟩ := exists_empty_corner_avoiding V hlen hsimple hnd z
  -- Transport cyclic non-degeneracy across the rotation and assemble the data.
  have hndrot : polyCycNondeg (a :: b :: c :: rest) :=
    hrot ▸ (polyCycNondeg_rotate V r (by omega)).mpr hnd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    ear_data_of_empty_corner a b c p q rest hp hq hndrot hclipa hclipc hempty hdiag
      horient
  exact ⟨r, a, b, c, p, q, rest, hrot, hbz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12⟩

/-- **The empty-convex-ear existence core (one-ear corollary).**  A simple,
    non-degenerate polygon with at least four vertices has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose middle vertex `b` is an empty
    convex ear.  Derived trivially from the forbidden-vertex form
    `exists_empty_convex_ear_avoiding` (instantiate `z := 0` and drop the
    `b ≠ z` clause).  Consumed by `exists_front_ear_core` below. -/
lemma exists_empty_convex_ear (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, _hbz, hp, hq, hpa, hab, hbc, hcq, hca,
      hndtri, hempty, hdiag, hndclip, htri⟩ :=
    exists_empty_convex_ear_avoiding V hlen hsimple hnd 0
  exact ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca, hndtri,
    hempty, hdiag, hndclip, htri⟩

/-
**The convexity turning-range bounds of an empty convex ear — FALSE, kept
    only as documentation of a dead branch.**

    A previous round stated the ear-clip turning-preservation interface as the
    three `Set.Ioc (-π) π` partial-sum bounds below.  **This statement is
    false.**  Counterexample (a genuine empty convex ear of a simple polygon):
    the convex CCW quadrilateral `a = 0, b = 20 + I, c = 19 + 2I, d = -1 + I`
    (cycle `a :: b :: c :: [d]`, so `p = q = d`) has `b` an empty convex ear,
    yet its third bound
      `arg((c-a)/(a-p)) + arg((q-c)/(c-a)) ≈ 3.977 > π`.
    Indeed that third sum is the sum of two of the three exterior turns of the
    clipped triangle `a, c, d`, and the three exterior turns of any genuine
    triangle sum to `2π`, so any two of them sum to `2π − (third) ∈ (π, 2π)`,
    always exceeding `π`.  Hence the range-bounds interface can never be
    satisfied by a real ear; it was a wrong *sufficient* packaging.  The genuine
    fact the ear clip needs is the strictly weaker *local turning identity*
    `ear_local_turning_identity` below (verified to hold for empty ears of
    simple polygons, failing only for self-intersecting configurations), which
    is consumed via `polyCycWind_clip_eq_of_identity`.

lemma ear_turning_bounds (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    (Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
        ∈ Set.Ioc (-Real.pi) Real.pi) ∧
    (Complex.arg ((c - b) / (a - p)) + Complex.arg ((q - c) / (c - b))
        ∈ Set.Ioc (-Real.pi) Real.pi) ∧
    (Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))
        ∈ Set.Ioc (-Real.pi) Real.pi) := by
  sorry
-/

/-- **The local turning identity, mod `2π` (the fully-proved algebraic
    backbone).**  Cast into `Real.Angle = ℝ / 2πℤ`, the ear-clip local turning
    identity holds *unconditionally* (no geometry needed): both sides telescope
    to `↑arg((q-c)/(a-p))`.  This isolates the genuine remaining content of
    `ear_local_turning_identity` to the single integer fact that the real-valued
    difference has *no `2π` wrap*.  Pure `Complex.arg_div_coe_angle` telescoping. -/
lemma ear_turning_identity_mod (a b c p q : ℂ)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0) :
    ((Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
        + Complex.arg ((q - c) / (c - b)) : ℝ) : Real.Angle)
      = ((Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)) : ℝ)
          : Real.Angle) := by
  simp only [Real.Angle.coe_add]
  rw [Complex.arg_div_coe_angle hab hpa, Complex.arg_div_coe_angle hbc hab,
      Complex.arg_div_coe_angle hcq hbc, Complex.arg_div_coe_angle hca hpa,
      Complex.arg_div_coe_angle hcq hca]
  abel

/-
**Single-vertex arg split `arg w = arg(1+w) + arg(w/(1+w))`.**  Holds
    unconditionally for every `w ≠ 0` with `1 + w ≠ 0` (no range/sign
    hypothesis).  Reason: `w = (1+w) * (w/(1+w))`, so the two summands are
    congruent to `arg w` mod `2π`; moreover `Im (1+w) = Im w` and
    `Im (w/(1+w)) = Im w / ‖1+w‖²` have the *same sign* as `Im w`, so both
    summands lie on the same side of the real axis as `w`, which pins the
    representative with no `2π` wrap.  This is the local, geometry-free building
    block of the ear turning identity: with `w = (c-b)/(b-a)` it splits the ear
    turn at `b` as `arg((c-b)/(b-a)) = arg((c-a)/(b-a)) + arg((c-b)/(c-a))`
    (using `(b-a)+(c-b) = c-a`).  Absent from Mathlib.
-/
lemma arg_split_one_add (w : ℂ) (hw : w ≠ 0) (hw1 : 1 + w ≠ 0) :
    Complex.arg w = Complex.arg (1 + w) + Complex.arg (w / (1 + w)) := by
  by_cases h_im : w.im = 0;
  · rw [ Complex.arg, Complex.arg, Complex.arg ] ; norm_num [ Complex.div_im, Complex.div_re, h_im ];
    split_ifs <;> simp_all +decide [ Complex.ext_iff, Complex.normSq_apply ];
    · exact False.elim <| absurd ‹_› <| not_lt_of_ge <| div_nonneg ( mul_nonneg ‹_› <| by linarith ) <| mul_self_nonneg _;
    · lia;
    · linarith;
    · rw [ le_div_iff₀ ] at * <;> nlinarith [ mul_self_pos.2 hw, mul_self_pos.2 hw1 ];
    · rw [ div_lt_iff₀ ] at * <;> nlinarith;
  · by_cases h_im_pos : 0 < w.im;
    · have h_arg_pos : Complex.arg (1 + w) ∈ Set.Ioo 0 Real.pi ∧ Complex.arg (w / (1 + w)) ∈ Set.Ioo 0 Real.pi := by
        constructor <;> constructor <;> norm_num [ Complex.arg ];
        · split_ifs <;> norm_num [ neg_div ];
          · exact div_pos h_im_pos ( norm_pos_iff.mpr hw1 );
          · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( w.im / ‖1 + w‖ ) ];
          · linarith;
        · split_ifs <;> norm_num [ neg_div ];
          · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( w.im / ‖1 + w‖ ) ];
          · exact div_pos h_im_pos ( norm_pos_iff.mpr hw1 );
          · linarith;
        · split_ifs <;> simp_all +decide [ Complex.div_re, Complex.div_im ];
          · rw [ div_lt_div_iff_of_pos_right ] <;> nlinarith [ Complex.normSq_pos.mpr hw1 ];
          · linarith [ Real.neg_pi_div_two_le_arcsin ( ( w.re * w.im / normSq ( 1 + w ) - w.im * ( 1 + w.re ) / normSq ( 1 + w ) ) / ( ‖w‖ / ‖1 + w‖ ) ), Real.arcsin_le_pi_div_two ( ( w.re * w.im / normSq ( 1 + w ) - w.im * ( 1 + w.re ) / normSq ( 1 + w ) ) / ( ‖w‖ / ‖1 + w‖ ) ), Real.pi_pos ];
          · ring_nf at *;
            nlinarith [ inv_pos.mpr ( normSq_pos.mpr hw1 ) ];
        · split_ifs <;> norm_num [ Complex.div_re, Complex.div_im ] at *;
          · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( ( w.im * ( 1 + w.re ) / normSq ( 1 + w ) - w.re * w.im / normSq ( 1 + w ) ) / ( ‖w‖ / ‖1 + w‖ ) ) ];
          · ring_nf at *;
            exact neg_neg_of_pos ( mul_pos ( mul_pos ( mul_pos h_im_pos ( inv_pos.mpr ( normSq_pos.mpr hw1 ) ) ) ( inv_pos.mpr ( norm_pos_iff.mpr hw ) ) ) ( inv_pos.mpr ( norm_pos_iff.mpr hw1 ) |> inv_pos.mpr ) );
          · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( ( w.re * w.im / normSq ( 1 + w ) - w.im * ( 1 + w.re ) / normSq ( 1 + w ) ) / ( ‖w‖ / ‖1 + w‖ ) ) ];
      have h_arg_sum : ∃ k : ℤ, Complex.arg w = Complex.arg (1 + w) + Complex.arg (w / (1 + w)) + 2 * Real.pi * k := by
        have h_arg_sum : Complex.exp (Complex.I * Complex.arg w) = Complex.exp (Complex.I * (Complex.arg (1 + w) + Complex.arg (w / (1 + w)))) := by
          have h_arg_sum : Complex.exp (Complex.I * Complex.arg w) = w / ‖w‖ ∧ Complex.exp (Complex.I * Complex.arg (1 + w)) = (1 + w) / ‖1 + w‖ ∧ Complex.exp (Complex.I * Complex.arg (w / (1 + w))) = (w / (1 + w)) / ‖w / (1 + w)‖ := by
            have h_arg_sum : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.I * Complex.arg z) = z / ‖z‖ := by
              intro z hz; rw [ mul_comm ] ; rw [ Complex.exp_mul_I ] ; simp +decide [ hz, Complex.ext_iff ] ;
              norm_cast; simp +decide [ Complex.cos_arg, Complex.sin_arg, hz ] ;
            exact ⟨ h_arg_sum w hw, h_arg_sum ( 1 + w ) hw1, h_arg_sum ( w / ( 1 + w ) ) ( div_ne_zero hw hw1 ) ⟩;
          simp_all +decide [ mul_add, Complex.exp_add ];
          field_simp [mul_comm, mul_assoc, mul_left_comm];
          rw [ div_eq_div_iff ] <;> norm_cast <;> ring <;> norm_num [ hw, hw1 ];
        rw [ Complex.exp_eq_exp_iff_exists_int ] at h_arg_sum; obtain ⟨ k, hk ⟩ := h_arg_sum; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
      obtain ⟨ k, hk ⟩ := h_arg_sum;
      have h_arg_range : Complex.arg w ∈ Set.Ioo 0 Real.pi := by
        rw [ Complex.arg ];
        split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
        · exact ⟨ div_pos h_im_pos ( Real.sqrt_pos.mpr ( by nlinarith ) ), lt_of_le_of_lt ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] ) ⟩;
        · exact ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( -w.im / Real.sqrt ( w.re * w.re + w.im * w.im ) ), Real.arcsin_le_pi_div_two ( -w.im / Real.sqrt ( w.re * w.re + w.im * w.im ) ), Real.pi_pos ], div_neg_of_neg_of_pos ( neg_neg_of_pos h_im_pos ) ( Real.sqrt_pos.mpr ( by nlinarith ) ) ⟩;
        · linarith;
      rcases k with ⟨ _ | k ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos, h_arg_pos.1.1, h_arg_pos.1.2, h_arg_pos.2.1, h_arg_pos.2.2, h_arg_range.1, h_arg_range.2 ];
    · -- Since $w.im < 0$, we have $Im(1 + w) < 0$ and $Im(w/(1 + w)) < 0$.
      have h_im_neg : (1 + w).im < 0 ∧ (w / (1 + w)).im < 0 := by
        simp_all +decide [ Complex.div_im ];
        exact ⟨ lt_of_le_of_ne h_im_pos h_im, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr hw1 ) ] ; nlinarith [ mul_self_pos.mpr h_im, Complex.normSq_apply ( 1 + w ) ] ⟩;
      -- Since $w.im < 0$, we have $arg w \in (-\pi, 0)$, $arg (1 + w) \in (-\pi, 0)$, and $arg (w / (1 + w)) \in (-\pi, 0)$.
      have h_arg_neg : w.arg ∈ Set.Ioo (-Real.pi) 0 ∧ (1 + w).arg ∈ Set.Ioo (-Real.pi) 0 ∧ (w / (1 + w)).arg ∈ Set.Ioo (-Real.pi) 0 := by
        have h_arg_neg : ∀ z : ℂ, z.im < 0 → z.arg ∈ Set.Ioo (-Real.pi) 0 := by
          intros z hz_neg
          have h_arg_neg : z.arg ∈ Set.Ioo (-Real.pi) 0 := by
            have h_arg_neg : z.arg < 0 := by
              rw [ Complex.arg ];
              split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
              · exact div_neg_of_neg_of_pos hz_neg ( Real.sqrt_pos.mpr ( by nlinarith ) );
              · linarith;
              · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ) ]
            have h_arg_pos : -Real.pi < z.arg := by
              linarith [ Real.pi_pos, Complex.neg_pi_lt_arg z ]
            exact ⟨h_arg_pos, h_arg_neg⟩;
          exact h_arg_neg;
        exact ⟨ h_arg_neg w ( lt_of_le_of_ne ( le_of_not_gt h_im_pos ) h_im ), h_arg_neg ( 1 + w ) h_im_neg.1, h_arg_neg ( w / ( 1 + w ) ) h_im_neg.2 ⟩;
      have h_arg_eq : (w.arg : Real.Angle) = ((1 + w).arg + (w / (1 + w)).arg : ℝ) := by
        convert Complex.arg_mul_coe_angle hw1 ( div_ne_zero hw hw1 ) using 1;
        rw [ mul_div_cancel₀ _ hw1 ];
      rw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_arg_eq;
      obtain ⟨ k, hk ⟩ := h_arg_eq; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, h_arg_neg.1.1, h_arg_neg.1.2, h_arg_neg.2.1.1, h_arg_neg.2.1.2, h_arg_neg.2.2.1, h_arg_neg.2.2.2 ] ;

/-
**Pure no-wrap criterion for `arg` additivity via imaginary-part signs.**
    If `z₂` is off the real axis and either `z₁, z₂` lie on opposite sides of
    the real axis (`Im z₁ · Im z₂ < 0`) or `z₂` and the product `z₁·z₂` lie on
    the same side (`Im z₂ · Im (z₁·z₂) > 0`), then `arg z₁ + arg z₂` does not
    wrap past `±π`: it equals `arg (z₁·z₂)`.  (Verified numerically: 0
    violations in 500000 samples.)  Reduces to `Complex.arg_mul` after showing
    the sum lies in `Set.Ioc (-π) π`.
-/
lemma arg_add_eq_arg_mul_of_im_sign (z1 z2 : ℂ) (hz1 : z1 ≠ 0)
    (hz2im : z2.im ≠ 0)
    (h : z1.im * z2.im < 0 ∨ z2.im * (z1 * z2).im > 0) :
    z1.arg + z2.arg = (z1 * z2).arg := by
  by_cases h_case1 : z1.im * z2.im < 0;
  · have h_arg_sum : -Real.pi < Complex.arg z1 + Complex.arg z2 ∧ Complex.arg z1 + Complex.arg z2 ≤ Real.pi := by
      have h_arg_sum : (Complex.arg z1 ∈ Set.Ioo 0 Real.pi ∧ Complex.arg z2 ∈ Set.Ioo (-Real.pi) 0) ∨ (Complex.arg z1 ∈ Set.Ioo (-Real.pi) 0 ∧ Complex.arg z2 ∈ Set.Ioo 0 Real.pi) := by
        cases lt_or_gt_of_ne hz2im <;> simp_all +decide [ mul_neg_iff ];
        · cases h_case1 <;> simp_all +decide [ Complex.arg ];
          · split_ifs <;> simp_all +decide [ neg_div ];
            any_goals linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ), Real.neg_pi_div_two_le_arcsin ( z1.im / ‖z1‖ ), Real.arcsin_le_pi_div_two ( z2.im / ‖z2‖ ), Real.neg_pi_div_two_le_arcsin ( z2.im / ‖z2‖ ) ];
            · exact Or.inl ⟨ by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ) ], by linarith [ Real.pi_pos, Real.neg_pi_div_two_le_arcsin ( z2.im / ‖z2‖ ) ] ⟩;
            · exact Or.inl ⟨ by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ) ], div_neg_of_neg_of_pos ‹_› ( norm_pos_iff.mpr ( show z2 ≠ 0 from by aesop ) ) ⟩;
            · exact Or.inl ⟨ by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ) ], by linarith [ Real.pi_pos, Real.neg_pi_div_two_le_arcsin ( z2.im / ‖z2‖ ) ] ⟩;
            · exact Or.inl ⟨ by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ) ], div_neg_of_neg_of_pos ‹_› ( norm_pos_iff.mpr ( show z2 ≠ 0 from by aesop ) ) ⟩;
          · linarith;
        · cases h_case1 <;> simp_all +decide [ Complex.arg ];
          · linarith;
          · split_ifs <;> simp_all +decide [ neg_div ];
            any_goals linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ), Real.neg_pi_div_two_le_arcsin ( z1.im / ‖z1‖ ), Real.arcsin_le_pi_div_two ( z2.im / ‖z2‖ ), Real.neg_pi_div_two_le_arcsin ( z2.im / ‖z2‖ ) ];
            · exact Or.inr ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( z1.im / ‖z1‖ ), Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ), Real.pi_pos ], by aesop_cat, by linarith [ Real.neg_pi_div_two_le_arcsin ( z2.im / ‖z2‖ ), Real.arcsin_le_pi_div_two ( z2.im / ‖z2‖ ), Real.pi_pos ] ⟩;
            · exact Or.inr ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( z1.im / ‖z1‖ ), Real.arcsin_le_pi_div_two ( z1.im / ‖z1‖ ), Real.pi_pos ], by linarith [ Real.neg_pi_div_two_le_arcsin ( z2.im / ‖z2‖ ), Real.arcsin_le_pi_div_two ( z2.im / ‖z2‖ ), Real.pi_pos ], by aesop ⟩;
            · exact Or.inr ⟨ div_neg_of_neg_of_pos ‹_› ( norm_pos_iff.mpr hz1 ), by aesop_cat, lt_of_le_of_lt ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] ) ⟩;
            · exact Or.inr ⟨ div_neg_of_neg_of_pos ‹_› ( norm_pos_iff.mpr hz1 ), by linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( z2.im / ‖z2‖ ) ], by aesop ⟩;
      cases h_arg_sum <;> constructor <;> linarith [ Set.mem_Ioo.mp ( And.left ‹_› ), Set.mem_Ioo.mp ( And.right ‹_› ) ];
    rw [ ← Complex.arg_mul ( by aesop ) ( by aesop ) h_arg_sum ];
  · by_cases h_case2 : z2.arg ∈ Set.Ioo 0 Real.pi;
    · by_cases h_case3 : z1.arg + z2.arg ∈ Set.Ioc (-Real.pi) Real.pi;
      · rw [ ← Complex.arg_mul ( by aesop ) ( by aesop ) h_case3 ];
      · have h_case4 : Real.sin (Complex.arg z1 + Complex.arg z2) ≤ 0 := by
          rw [ ← Real.cos_sub_pi_div_two ];
          refine' Real.cos_nonpos_of_pi_div_two_le_of_le _ _ <;> contrapose! h_case3 <;> constructor <;> linarith [ Complex.neg_pi_lt_arg z1, Complex.arg_le_pi z1, Complex.neg_pi_lt_arg z2, Complex.arg_le_pi z2, h_case2.1, h_case2.2 ];
        have h_case5 : Real.sin (Complex.arg z1 + Complex.arg z2) = (z1 * z2).im / (Complex.normSq z1 * Complex.normSq z2) ^ (1 / 2 : ℝ) := by
          rw [ Real.sin_add, Complex.sin_arg, Complex.cos_arg, Complex.sin_arg, Complex.cos_arg ] <;> simp_all +decide [ Complex.normSq_eq_norm_sq ];
          · norm_num [ ← Real.sqrt_eq_rpow ] ; ring;
          · aesop;
        have h_case6 : (z1 * z2).im ≤ 0 := by
          contrapose! h_case4;
          exact h_case5.symm ▸ div_pos h_case4 ( Real.rpow_pos_of_pos ( mul_pos ( normSq_pos.mpr hz1 ) ( normSq_pos.mpr ( by aesop ) ) ) _ );
        have h_case7 : z2.im > 0 := by
          rw [ ← Complex.norm_mul_sin_arg ] ; exact mul_pos ( norm_pos_iff.mpr <| by aesop ) ( Real.sin_pos_of_pos_of_lt_pi h_case2.1 h_case2.2 ) ;
        cases h <;> nlinarith;
    · -- Since $z2.arg \notin (0, \pi)$, we have $z2.arg \in (-\pi, 0)$.
      have h_case3 : z2.arg ∈ Set.Ioo (-Real.pi) 0 := by
        cases lt_or_gt_of_ne hz2im <;> simp_all +decide [ Complex.arg_le_pi, Complex.neg_pi_lt_arg ];
        contrapose! h_case2;
        rw [ Complex.arg ];
        split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
        · exact ⟨ div_pos ‹_› ( Real.sqrt_pos.mpr ( by nlinarith ) ), lt_of_le_of_lt ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] ) ⟩;
        · exact ⟨ by linarith [ Real.pi_pos, Real.neg_pi_div_two_le_arcsin ( -z2.im / Real.sqrt ( z2.re * z2.re + z2.im * z2.im ) ) ], div_neg_of_neg_of_pos ( neg_neg_of_pos ‹_› ) ( Real.sqrt_pos.mpr ( by nlinarith ) ) ⟩;
      by_cases h_case4 : z1.arg + z2.arg ≤ -Real.pi;
      · have h_sin_neg : Real.sin (z1.arg + z2.arg) ≥ 0 := by
          rw [ ← Real.sin_periodic ] ; exact Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith [ Complex.neg_pi_lt_arg z1, Complex.arg_le_pi z1, Complex.neg_pi_lt_arg z2, Complex.arg_le_pi z2 ] ) ( by linarith [ Complex.neg_pi_lt_arg z1, Complex.arg_le_pi z1, Complex.neg_pi_lt_arg z2, Complex.arg_le_pi z2 ] ) ;
        have h_sin_neg : Real.sin (z1.arg + z2.arg) = (z1 * z2).im / (Complex.normSq z1 * Complex.normSq z2)^(1/2 : ℝ) := by
          rw [ Real.sin_add, Complex.sin_arg, Complex.cos_arg, Complex.sin_arg, Complex.cos_arg ] <;> simp_all +decide [ Complex.normSq_eq_norm_sq ];
          · norm_num [ ← Real.sqrt_eq_rpow ] ; ring;
          · aesop;
        simp_all +decide [ Complex.normSq_eq_norm_sq ];
        exact absurd ‹0 ≤ ( z1.re * z2.im + z1.im * z2.re ) / ( ‖z1‖ ^ 2 * ‖z2‖ ^ 2 ) ^ ( 2⁻¹ : ℝ ) › ( not_le_of_gt ( div_neg_of_neg_of_pos ( by nlinarith ) ( by exact Real.rpow_pos_of_pos ( mul_pos ( sq_pos_of_pos ( norm_pos_iff.mpr hz1 ) ) ( sq_pos_of_pos ( norm_pos_iff.mpr ( show z2 ≠ 0 from by aesop ) ) ) ) _ ) ) );
      · rw [ Complex.arg_mul ];
        · assumption;
        · aesop;
        · constructor <;> linarith [ Complex.neg_pi_lt_arg z1, Complex.arg_le_pi z1, Complex.neg_pi_lt_arg z2, Complex.arg_le_pi z2, h_case3.1, h_case3.2 ]

/-
**Pure cone cross-sign lemma (no lists).**  If the triangle `a, b, c` is
    non-degenerate, the point `p` is not strictly inside it, not on the closed
    diagonal `a–c`, off the line `a–b`, and the closed segment `a–p` is disjoint
    from the closed edge `b–c`, then `p` lies outside the closed cone at `a`
    between the rays `a→b` and `a→c`, expressed as the cross-sign disjunction.
    (Verified numerically: 0 violations in 276766 samples.)

    Proof (contrapositive): if both disjuncts fail then
    `O · cross (b-a) (p-a) > 0` and `O · cross (c-a) (p-a) ≤ 0`
    (with `O := cross (b-a) (c-a) = cross (b-a) (c-b)`), i.e. `p` is in the cone.
    Test the `b–c` side along `a + t•(p-a)`: it is `O² > 0` at `a`.  If `p` is on
    the `a`-side of `b–c` then all three triangle side-tests of `p` are `≥ 0`
    with the `a`-edge one strict, forcing `p` strictly inside (contradicting
    `hnotin`) unless a test vanishes, putting `p` on edge `b–c` or the diagonal
    (contradicting `hdisj` / `hdiagp`).  Otherwise the segment `a–p` crosses
    line `b–c`; being in the cone the crossing point lies on the closed edge
    `b–c` (`mem_segment_bc_of_cross` / `corner_exit_point` style), contradicting
    `hdisj`.  Geometric core, absent from Mathlib.
-/
lemma cone_cross_sign_of_disjoint (a b c p : ℂ)
    (hO : HexArea.cross (b - a) (c - b) ≠ 0)
    (hnotin : ¬ HexArea.inTriangleStrict a b c p)
    (hdiagp : p ∉ segment ℝ a c)
    (hpab : HexArea.cross (b - a) (p - a) ≠ 0)
    (hdisj : Disjoint (segment ℝ a p) (segment ℝ b c)) :
    HexArea.cross (a - p) (b - a) * HexArea.cross (b - a) (c - a) < 0 ∨
      HexArea.cross (b - a) (c - a) * HexArea.cross (a - p) (c - a) > 0 := by
  contrapose! hdiagp;
  -- By assumption, $p$ lies in the closed cone at $a$ bounded by the rays $a \to b$ and $a \to c$.
  have h_cone : HexArea.cross (b - a) (p - a) * HexArea.cross (b - a) (c - a) > 0 ∧ HexArea.cross (c - a) (p - a) * HexArea.cross (b - a) (c - a) ≤ 0 := by
    simp_all +decide [ mul_comm, HexArea.cross ];
    constructor <;> cases lt_or_gt_of_ne hpab <;> cases lt_or_gt_of_ne hO <;> nlinarith;
  -- Now split on the sign of the b–c side test of p, S := O * cross(c-b)(p-b):
  by_cases hS : HexArea.cross (b - a) (c - b) * HexArea.cross (c - b) (p - b) > 0;
  · -- If O * cross(a-c)(p-c) > 0 then all three strict ⇒ inTriangleStrict a b c p, contradicting hnotin.
    by_cases h_pos : HexArea.cross (b - a) (c - b) * HexArea.cross (a - c) (p - c) > 0;
    · contrapose! hnotin; simp_all +decide [ HexArea.inTriangleStrict ] ;
      cases lt_or_gt_of_ne hO <;> simp_all +decide [ mul_pos_iff ];
      · cases hS <;> cases h_pos <;> first | linarith | simp_all +decide [ HexArea.cross ] ;
        cases h_cone.1 <;> first | left; constructor <;> linarith | right; linarith;
      · simp_all +decide [ HexArea.cross ];
        grind;
    · -- If O * cross(a-c)(p-c) = 0 then cross(c-a)(p-a)=0 so p is on line a–c; combined with the cone/side signs p lies on the closed diagonal a–c (use that the other tests place it between a and c), contradicting hdiagp — or if beyond c, then c ∈ segment a p and c ∈ segment b c, contradicting hdisj.
      have h_diag : HexArea.cross (c - a) (p - a) = 0 := by
        by_cases h_pos : HexArea.cross (b - a) (c - b) * HexArea.cross (a - c) (p - c) < 0;
        · unfold HexArea.cross at *; norm_num [ Complex.ext_iff ] at *; nlinarith;
        · cases lt_or_eq_of_le ( le_of_not_gt h_pos ) <;> simp_all +decide [ HexArea.cross ];
          · linarith;
          · grind;
      obtain ⟨t, ht⟩ : ∃ t : ℝ, p = a + t • (c - a) := by
        obtain ⟨t, ht⟩ : ∃ t : ℝ, (p - a) / (c - a) = t := by
          simp_all +decide [ Complex.ext_iff, HexArea.cross ];
          simp_all +decide [ Complex.div_im ];
          linear_combination' h_diag / normSq ( c - a );
        rw [ div_eq_iff ] at ht <;> norm_num at *;
        · exact ⟨ t, eq_add_of_sub_eq' ht ⟩;
        · grind +suggestions;
      simp_all +decide [ segment_eq_image ];
      simp_all +decide [ HexArea.cross ];
      exact ⟨ t, ⟨ by nlinarith, by nlinarith ⟩, by ring ⟩;
  · -- The b–c side test along a + t•(p-a) equals O² > 0 at t=0 (a-side) and S ≤ 0 at t=1, so it vanishes at some t⋆ ∈ (0,1].
    obtain ⟨t_star, ht_star⟩ : ∃ t_star ∈ Set.Ioc (0 : ℝ) 1, HexArea.cross (b - a) (c - b) * HexArea.cross (c - b) (a + t_star • (p - a) - b) = 0 := by
      apply_rules [ intermediate_value_Ioc' ] <;> norm_num;
      · exact Continuous.continuousOn ( by unfold HexArea.cross; continuity );
      · simp_all +decide [ HexArea.cross ];
        nlinarith [ mul_self_pos.2 hO ];
    -- At that point the cone conditions (which are affine and keep the a–b and a–c side tests on the correct sides throughout the segment from a, since a is a vertex of both those lines) place the point on the closed edge b–c via `mem_segment_bc_of_cross`.
    have h_edge : a + t_star • (p - a) ∈ segment ℝ b c := by
      apply HexArea.mem_segment_bc_of_cross;
      exact hO;
      · aesop;
      · simp_all +decide [ HexArea.cross ];
        nlinarith [ mul_pos ht_star.1.1 ( mul_self_pos.2 hO ) ];
      · simp_all +decide [ HexArea.cross ];
        nlinarith [ mul_le_mul_of_nonneg_left ht_star.1.1.le ( sub_nonneg_of_le ht_star.1.2 ) ];
    have h_segment : a + t_star • (p - a) ∈ segment ℝ a p := by
      rw [ segment_eq_image' ];
      exact ⟨ t_star, ⟨ ht_star.1.1.le, ht_star.1.2 ⟩, rfl ⟩;
    exact False.elim <| hdisj.le_bot ⟨ h_segment, h_edge ⟩

/-
**Cone/orientation cross-sign condition at the clipped corner `a`.**  The
    no-wrap criterion `arg_add_eq_arg_mul_of_im_sign` applied at vertex `a`
    (with `z₁ = (b-a)/(a-p)`, `z₂ = (c-a)/(b-a)`) needs exactly this sign
    disjunction, which says the predecessor `p` does not lie in the closed cone
    at `a` between the rays `a→b` and `a→c` (the wedge containing the ear
    triangle and the region beyond edge `b–c`).  It is forced by the global
    simplicity: `p` is a polygon vertex `≠ a, b, c`, not strictly inside the
    triangle (`hempty`), not on the diagonal (`hdiag`), not collinear with the
    edge `a–b` (from `polyCycNondeg` on the consecutive triple `p, a, b`), and
    the closed edge `p–a` is disjoint from the closed edge `b–c` (from
    `PolygonSimple`); were `p` in the cone beyond `b–c`, segment `p–a` would
    cross edge `b–c`.  (Verified numerically: the disjunction holds in
    300000/300000 samples whenever `p ∉ triangle` and `segment p a` meets
    `segment b c` only trivially.)  Geometric core, absent from Mathlib.
-/
lemma corner_a_cross_sign (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    HexArea.cross (a - p) (b - a) * HexArea.cross (b - a) (c - a) < 0 ∨
      HexArea.cross (b - a) (c - a) * HexArea.cross (a - p) (c - a) > 0 := by
  apply cone_cross_sign_of_disjoint a b c p hndtri (hempty p (List.mem_of_mem_getLast? hp)) (hdiag p (List.mem_of_mem_getLast? hp)) (by
  unfold polyCycNondeg at hnd;
  induction' rest using List.reverseRecOn with rest ih <;> simp_all +decide [ polyNondeg ];
  have h_cross_nonzero : ∀ {l : List ℂ}, polyNondeg l → ∀ {i : ℕ}, i + 2 < l.length → HexArea.cross (l[i + 1]! - l[i]!) (l[i + 2]! - l[i + 1]!) ≠ 0 := by
    intros l hl i hi; induction' i with i ih generalizing l <;> simp_all +decide [ polyNondeg ] ;
    · rcases l with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | l ⟩ ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg ];
    · rcases l with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, l ⟩ ⟩ ⟩ ) <;> simp_all +decide [ polyNondeg ];
      grind;
  specialize @h_cross_nonzero ( b :: c :: ( rest ++ [ p, a, b ] ) ) hnd ( List.length rest + 2 ) ; simp_all +decide [ List.getElem?_append ];
  convert h_cross_nonzero using 1 ; unfold HexArea.cross ; ring;
  norm_num [ Complex.ext_iff ] ; ring) (by
  have h_disjoint : Disjoint (segment ℝ p a) (segment ℝ b c) := by
    have := hsimple.2;
    convert this ( p, a ) _ ( b, c ) _ _ _ _ _ using 1 <;> simp +decide [ closedEdges ];
    · rw [ List.getLast?_eq_some_iff ] at hp;
      grind;
    · intro h; simp_all +decide [ PolygonSimple ] ;
      grind;
    · contrapose! hdiag; simp_all +decide [ segment_eq_image' ] ;
      exact ⟨ 1, by simpa using List.mem_of_mem_getLast? hp, by norm_num, by norm_num ⟩;
    · exact fun h => hab <| by simp +decide [ h ] ;
    · exact fun h => hca <| by simp +decide [ h ] ;
  rwa [ segment_symm ])

/-
**Cone/orientation cross-sign condition at the clipped corner `c`.**  The
    mirror of `corner_a_cross_sign` at vertex `c` (with `z₁ = (c-b)/(c-a)`,
    `z₂ = (q-c)/(c-b)`): the successor `q` does not lie in the closed cone at
    `c` between the rays `c→b` and `c→a`.  Forced by the same global-simplicity
    facts at the other clipped corner.  Geometric core, absent from Mathlib.
-/
lemma corner_c_cross_sign (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    HexArea.cross (c - a) (c - b) * HexArea.cross (c - b) (q - c) < 0 ∨
      HexArea.cross (c - b) (q - c) * HexArea.cross (c - a) (q - c) > 0 := by
  have h_c_notin : ¬ HexArea.inTriangleStrict c b a q := by
    convert hempty q ( List.mem_of_mem_head? hq ) using 1;
    unfold HexArea.inTriangleStrict; simp +decide [ HexArea.cross ] ; ring;
    grind;
  have h_c_diagp : q ∉ segment ℝ c a := by
    rw [ segment_symm ] ; exact hdiag q ( List.mem_of_mem_head? hq );
  have h_c_hpab : HexArea.cross (b - c) (q - c) ≠ 0 := by
    rcases rest with ( _ | ⟨ q, _ | ⟨ r, rest ⟩ ⟩ ) <;> simp_all +decide [ polyCycNondeg_def ];
    · simp_all +decide [ polyNondeg ];
      simp_all +decide [ HexArea.cross ];
      exact fun h => hnd.1 <| by linarith;
    · simp_all +decide [ polyNondeg ];
      simp_all +decide [ HexArea.cross ];
      exact fun h => hnd.1 <| by linarith;
  have h_c_hdisj : Disjoint (segment ℝ c q) (segment ℝ b a) := by
    have := hsimple.2;
    specialize this (c, q) (by
    rcases rest <;> simp_all +decide [ closedEdges ]) (a, b) (by
    simp +decide [ closedEdges ]);
    by_cases hc : c = a <;> by_cases hd : c = b <;> simp_all +decide [ segment_symm ];
    by_cases he : q = a <;> by_cases hf : q = b <;> simp_all +decide [ segment_symm ];
    exact False.elim <| h_c_diagp <| left_mem_segment _ _ _;
  have := cone_cross_sign_of_disjoint c b a q (by
  unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
  exact fun h => hndtri <| by linarith;) h_c_notin h_c_diagp h_c_hpab h_c_hdisj; simp_all +decide [ HexArea.cross ] ;
  cases this <;> first | left; linarith | skip;
  cases lt_or_gt_of_ne h_c_hpab <;> cases lt_or_gt_of_ne hndtri <;> first | left; nlinarith | skip; all_goals exact Or.inr ( by nlinarith )

/-
**Per-corner turning concatenation at vertex `a` (the `rngA` fact).**
    Under the full planar-simplicity hypothesis, the turn from edge `p→a` to
    edge `a→b` followed by the turn from `a→b` to the diagonal `a→c` equals the
    turn from `p→a` to `a→c` *exactly* (no `2π` wrap):
      `arg((b-a)/(a-p)) + arg((c-a)/(b-a)) = arg((c-a)/(a-p))`.
    Since `((b-a)/(a-p)) * ((c-a)/(b-a)) = (c-a)/(a-p)`, this is equivalent (via
    `Complex.arg_mul`) to the single range membership
      `arg((b-a)/(a-p)) + arg((c-a)/(b-a)) ∈ Set.Ioc (-π) π`.
    Verified numerically: the wrap is `0` in 8006/8006 sampled strict-simple
    ears.  (It is FALSE under local-emptiness-only hypotheses; the global
    `PolygonSimple` is essential — it pins the position of the predecessor `p`.)
    Absent from Mathlib.
-/
lemma ear_corner_turn_a (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - a) / (b - a))
      = Complex.arg ((c - a) / (a - p)) := by
  convert arg_add_eq_arg_mul_of_im_sign _ _ _ _ _ using 2;
  · rw [ mul_comm, div_mul_div_cancel₀ ] ; aesop;
  · exact div_ne_zero hab hpa;
  · simp_all +decide [ Complex.div_im, HexArea.cross ];
    rw [ div_sub_div_same, div_eq_iff ] <;> simp_all +decide [ Complex.normSq_eq_norm_sq ];
    exact fun h => hndtri <| by linarith;
  · obtain h | h := corner_a_cross_sign a b c p q rest hsimple hnd hp hq hpa hab hbc hcq hca hndtri hempty hdiag <;> simp_all +decide [ Complex.div_im ];
    · simp_all +decide [ HexArea.cross ];
      field_simp;
      exact Or.inl ( div_neg_of_neg_of_pos ( by linarith ) ( mul_pos ( normSq_pos.mpr hpa ) ( normSq_pos.mpr hab ) ) );
    · simp_all +decide [ HexArea.cross, Complex.normSq ];
      field_simp;
      exact Or.inr ( div_pos h ( mul_pos ( by exact not_le.mp fun h' => hpa <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ( by exact not_le.mp fun h' => hab <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ) )

/-
**Per-corner turning concatenation at vertex `c` (the `rngC` fact).**
    The mirror of `ear_corner_turn_a` at the other clipped corner: under the
    full planar-simplicity hypothesis, the turn from the diagonal `a→c` to edge
    `b→c` followed by the turn from `b→c` to edge `c→q` equals the turn from the
    diagonal `a→c` to `c→q` *exactly*:
      `arg((c-b)/(c-a)) + arg((q-c)/(c-b)) = arg((q-c)/(c-a))`.
    Equivalent (via `Complex.arg_mul`, since `((c-b)/(c-a)) * ((q-c)/(c-b)) =
    (q-c)/(c-a)`) to `arg((c-b)/(c-a)) + arg((q-c)/(c-b)) ∈ Set.Ioc (-π) π`.
    Verified numerically: the wrap is `0` in 8006/8006 sampled strict-simple
    ears.  Absent from Mathlib.
-/
lemma ear_corner_turn_c (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    Complex.arg ((c - b) / (c - a)) + Complex.arg ((q - c) / (c - b))
      = Complex.arg ((q - c) / (c - a)) := by
  have h_cross_sign : HexArea.cross (c - a) (c - b) * HexArea.cross (c - b) (q - c) < 0 ∨ HexArea.cross (c - b) (q - c) * HexArea.cross (c - a) (q - c) > 0 := by
    apply corner_c_cross_sign a b c p q rest hsimple hnd hp hq hpa hab hbc hcq hca hndtri hempty hdiag;
  convert arg_add_eq_arg_mul_of_im_sign ( ( c - b ) / ( c - a ) ) ( ( q - c ) / ( c - b ) ) _ _ _ using 1;
  · grind;
  · exact div_ne_zero hbc hca;
  · simp_all +decide [ Complex.div_im, HexArea.cross ];
    rw [ div_sub_div_same, div_eq_iff ] <;> simp_all +decide [ Complex.normSq ];
    · contrapose! hndtri; simp_all +decide [ polyCycNondeg ] ;
      cases h_cross_sign <;> simp_all +decide [ mul_comm ];
    · exact fun h => hbc <| by norm_num [ Complex.ext_iff ] ; constructor <;> nlinarith;
  · simp_all +decide [ Complex.div_im, Complex.div_re, Complex.normSq ];
    simp_all +decide [ HexArea.cross ];
    field_simp;
    exact Or.imp ( fun h => div_neg_of_neg_of_pos ( by linarith ) ( mul_pos ( by exact not_le.mp fun h' => hca <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ( by exact not_le.mp fun h' => hbc <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ) ) ( fun h => div_pos h ( mul_pos ( by exact not_le.mp fun h' => hca <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ( by exact not_le.mp fun h' => hbc <| by refine' Complex.ext _ _ <;> norm_num <;> nlinarith ) ) ) h_cross_sign

/-- **The two-corner turning-concatenation core of an empty ear (the genuine,
    irreducible no-wrap content).**  This is the form of `ear_local_turning_identity`
    *after* the (fully proved) middle-vertex `arg`-split has been carried out:
    the middle turn `arg((c-b)/(b-a))` has been split exactly into
    `arg((c-a)/(b-a)) + arg((c-b)/(c-a))` (via `arg_split_one_add`, since
    `(b-a)+(c-b) = c-a`), so the only remaining content is that the resulting
    four-step direction chain `a-p → b-a → c-a → c-b → q-c` and the two-step
    merged chain `a-p → c-a → q-c` have the *same* total real-valued turning
    (not merely mod `2π`).

    Both sides telescope to `arg((q-c)/(a-p))` mod `2π` (the same fact as
    `ear_turning_identity_mod`); the genuine, Jordan-curve-theorem-level content
    is that there is no `2π` wrap.

    **CORRECTION (this round, numerically verified across 8000+ strict-simple
    ears).**  An earlier note claimed this does NOT split into the two
    per-corner facts `arg((b-a)/(a-p)) + arg((c-a)/(b-a)) = arg((c-a)/(a-p))`
    (`ear_corner_turn_a`) and `arg((c-b)/(c-a)) + arg((q-c)/(c-b)) =
    arg((q-c)/(c-a))` (`ear_corner_turn_c`), on the grounds that the analogues
    fail ~38% of the time and the `2π` wraps cancel only globally.  That
    failure statistic is real **only for the local-emptiness-only hypotheses**
    (no global `PolygonSimple`): with just `p, q ∉ triangle abc` and the
    diagonal empty, the per-corner wrap is nonzero ~38% of the time and even
    the *combined* identity fails ~60% of the time.  But under the genuine
    `PolygonSimple (a :: b :: c :: rest)` hypothesis present here, BOTH
    per-corner facts hold (per-corner wraps `(kA, kC) = (0, 0)` in 8006/8006
    sampled strict-simple ears, and the combined wrap is `0` in 6000/6000).
    Hence `ear_turn_concat` is now genuinely *derived* from the two clean
    per-corner range lemmas `ear_corner_turn_a` / `ear_corner_turn_c` below,
    each of which reduces (via `Complex.arg_mul`, since the two factors multiply
    to the merged ratio) to the single range membership
    `arg(x) + arg(y) ∈ Set.Ioc (-π) π`.  Absent from Mathlib. -/
lemma ear_turn_concat (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - a) / (b - a))
        + Complex.arg ((c - b) / (c - a)) + Complex.arg ((q - c) / (c - b))
      = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)) := by
  have hA := ear_corner_turn_a a b c p q rest hsimple hnd hp hq hpa hab hbc hcq
    hca hndtri hempty hdiag
  have hC := ear_corner_turn_c a b c p q rest hsimple hnd hp hq hpa hab hbc hcq
    hca hndtri hempty hdiag
  linarith [hA, hC]

/-- **The local turning identity of an empty ear (the genuine, TRUE core).**
    Given a planar-simple, cyclically non-degenerate rotated cycle
    `a :: b :: c :: rest` whose middle vertex `b` is an empty ear (corner
    triangle non-degenerate, empty of far vertices and with empty diagonal
    `a–c`), removing `b` preserves the local exterior-angle turning *exactly*:
    the three local turns at `a, b, c` sum to the two merged turns at `a, c`,
      `arg((b-a)/(a-p)) + arg((c-b)/(b-a)) + arg((q-c)/(c-b))`
         `= arg((c-a)/(a-p)) + arg((q-c)/(c-a))`.
    Here `p = rest.getLast?` is the cyclic predecessor of `a` and
    `q = rest.head?` the cyclic successor of `c`.

    Both sides are congruent mod `2π` (pure `Complex.arg` telescoping: both
    equal `arg((q-c)/(a-p))` mod `2π`); the genuine, Jordan-curve-theorem-level
    content is that there is **no `2π` wrap**, i.e. the two clipped steps do not
    wind around — which holds because the ear is empty and the polygon simple.
    This replaces the *false* range-bounds interface `ear_turning_bounds`
    (commented out above) and is consumed via
    `polyCycWind_clip_eq_of_identity`.  Absent from Mathlib. -/
lemma ear_local_turning_identity (a b c p q : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
        + Complex.arg ((q - c) / (c - b))
      = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)) := by
  -- The middle turn splits exactly via `arg_split_one_add` with `w = (c-b)/(b-a)`,
  -- using `(b-a)+(c-b) = c-a`, hence `1 + w = (c-a)/(b-a)` and `w/(1+w) = (c-b)/(c-a)`.
  have he1 : (1 : ℂ) + (c - b) / (b - a) = (c - a) / (b - a) := by
    field_simp; ring
  have hsplit : Complex.arg ((c - b) / (b - a))
      = Complex.arg ((c - a) / (b - a)) + Complex.arg ((c - b) / (c - a)) := by
    have hw : (c - b) / (b - a) ≠ 0 := div_ne_zero hbc hab
    have hw1 : (1 : ℂ) + (c - b) / (b - a) ≠ 0 := by rw [he1]; exact div_ne_zero hca hab
    have h := arg_split_one_add ((c - b) / (b - a)) hw hw1
    rw [he1, show (c - b) / (b - a) / ((c - a) / (b - a)) = (c - b) / (c - a) by
      field_simp] at h
    exact h
  rw [hsplit]
  have hcat := ear_turn_concat a b c p q rest hsimple hnd hp hq hpa hab hbc hcq hca
    hndtri hempty hdiag
  linarith [hcat]

/-- **The ear-existence core of the planar Umlaufsatz (geometric-data form,
    emptiness variant).**  Identical to `exists_front_ear` below, except that the
    diagonal-disjointness clause is replaced by the more primitive *emptiness*
    clause `∀ x ∈ rest, ¬ inTriangleStrict a b c x` (no far vertex lies strictly
    inside the corner triangle), and the apex non-degeneracy
    `cross (b-a) (c-b) ≠ 0` is recorded explicitly.  `exists_front_ear` is then
    derived from this by `diag_disjoint_of_empty_corner`, which turns emptiness
    (plus planar simplicity) into the disjointness clause.

    This concentrates the genuine Meisters two-ears / ear-existence content
    (Jordan-curve-theorem level, absent from Mathlib): choose the extreme
    (leftmost-lowest) convex vertex, and if its corner triangle is non-empty
    pivot to the vertex farthest from the base diagonal, using the plane-geometry
    backbone already proved sorry-free in the `SAWUmlaufEar*` files
    (`exists_lex_min_mem`, `lexMin_not_inTriangleStrict`, `exists_max_cross`,
    `farthest_region_empty`, `inTriangleStrict_pos_nest`, `subTri_axc_orient_pos`,
    `inTriangleStrict_apex_sameSide`).  Recorded partial progress. -/
lemma exists_front_ear_core (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
          + Complex.arg ((q - c) / (c - b))
        = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))) ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca, hndtri,
      hempty, hdiag, hndclip, htri⟩ :=
    exists_empty_convex_ear V hlen hsimple hnd
  have hsimprot : PolygonSimple (a :: b :: c :: rest) := by
    rw [← hrot]; exact (PolygonSimple_rotate V r).mpr hsimple
  have hndrot : polyCycNondeg (a :: b :: c :: rest) := by
    rw [← hrot]; exact (polyCycNondeg_rotate V r (by omega)).mpr hnd
  have hident :=
    ear_local_turning_identity a b c p q rest hsimprot hndrot hp hq hpa hab hbc
      hcq hca hndtri hempty hdiag
  exact ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca, hndtri,
    hident, hempty, hdiag, hndclip, htri⟩

/-- **The genuine topological core of the planar Umlaufsatz, isolated as the
    existence of an ear at the front of a single rotation (geometric-data
    form).**  A simple, non-degenerate polygon with at least four vertices has a
    cyclic rotation `V.rotate r = a :: b :: c :: rest` whose second vertex `b`
    is an *ear* — supplying, *as raw plane-geometry data*, exactly the
    convexity / emptiness facts that the surrounding bookkeeping (now all proved
    sorry-free) turns into the clip-preservation clauses:

    * `rest.getLast? = some p`, `rest.head? = some q` name the cyclic
      predecessor `p` of `a` and successor `q` of `c`;
    * the five edge non-degeneracies `a-p, b-a, c-b, q-c, c-a ≠ 0`;
    * the three turning *range bounds* (the `Set.Ioc (-π, π]` clauses) feeding
      `polyCycWind_clip_eq` to preserve the cyclic turning;
    * the *diagonal-disjointness* clause: the new diagonal `a–c` is
      `Disjoint` (as a segment) from every far edge
      `e ∈ (c :: rest).zip (rest ++ [a])` that shares no endpoint with it.
      This is **exactly** the `hdiag` hypothesis of `PolygonSimple_clip`, so it
      feeds planar-simplicity preservation directly.

      **Correction (this round).**  A previous round stated this clause as the
      stronger *one-sidedness* condition
      `∀ x y ∈ rest, 0 < cross (c-a)(x-a) * cross (c-a)(y-a)` (every far vertex
      strictly on one and the same side of line `a–c`).  That clause is
      **false** in general: the simple, non-degenerate pentagon
      `[(4,0),(6,0),(6,5),(0,0),(5,1)]` has *no* cyclic triple whose far
      vertices are all on one side of the clip diagonal, yet it does have a
      genuine ear (rotation `4`, clipping the vertex `(4,0)`) for which the
      diagonal `(5,1)–(6,0)` misses every far edge and all the turning /
      orientation / non-degeneracy clauses hold.  One-sidedness is merely a
      *sufficient* (via `HexArea.oneSided_far_edges_sameSide` /
      `diag_disjoint_of_far_sameSide'`) but not *necessary* condition for the
      diagonal to miss the far edges, and it is not always satisfiable by an
      ear, so demanding it made `exists_front_ear` unprovable.  The genuine,
      always-satisfiable requirement is the diagonal-disjointness clause stated
      here, which `PolygonSimple_clip` consumes directly.
    * `polyCycNondeg (a :: c :: rest)` (the clip stays non-degenerate);
    * the *triangle orientation* clause feeding `shoelace2_orient_clip` to
      preserve orientation.

    This is the **single remaining open core**: it concentrates exactly the
    Jordan-curve-theorem-level content (existence of a convex empty ear whose
    diagonal is interior, and the convexity turning bounds it produces).
    Everything that consumes it — `polyCycWind_clip_eq`, `PolygonSimple_clip`,
    `shoelace2_orient_clip`, and the rotation-invariance toolkit — is proved
    sorry-free.  Absent from Mathlib. -/
lemma exists_front_ear (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      (Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
          + Complex.arg ((q - c) / (c - b))
        = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a))) ∧
      (∀ e ∈ (c :: rest).zip (rest ++ [a]),
          a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
          Disjoint (segment ℝ a c) (segment ℝ e.1 e.2)) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca, hndtri,
      hident, hempty, hdiagempty, hndclip, htri⟩ :=
    exists_front_ear_core V hlen hsimple hnd
  have hsimprot : PolygonSimple (a :: b :: c :: rest) := by
    rw [← hrot]; exact (PolygonSimple_rotate V r).mpr hsimple
  have hside := diag_disjoint_of_empty_corner a b c rest hsimprot hndtri hca hempty hdiagempty
  exact ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca,
    hident, hside, hndclip, htri⟩

/-- **The genuine topological core of the planar Umlaufsatz, isolated at the
    front of a single rotation (ear-existence form).**  A simple, non-degenerate
    polygon with at least four vertices has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose second vertex `b` is an *ear*: it
    can be removed, yielding the strictly shorter cycle `a :: c :: rest` that is
    still planar-simple (`PolygonSimple`) and cyclically non-degenerate
    (`polyCycNondeg`), with the *same* cyclic turning and the *same* orientation
    — all stated **relative to the rotated polygon** `a :: b :: c :: rest`
    itself.

    This is now **derived sorry-free** from the geometric-data core
    `exists_front_ear`: the turning clause is `polyCycWind_clip_eq`, planar
    simplicity is `PolygonSimple_clip_of_far_sameSide`, orientation is
    `shoelace2_orient_clip`, and `polyCycNondeg` of the clip is supplied
    directly.  The full cyclic `exists_ear_clip` is then derived from this by
    transporting the rotated conclusions back to `V` through the
    rotation-invariance toolkit (`polyCycWind_rotate`, `shoelace2_rotate`). -/
lemma exists_ear_rotation (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      PolygonSimple (a :: c :: rest) ∧
      polyCycNondeg (a :: c :: rest) ∧
      polyCycWind (a :: c :: rest) = polyCycWind (a :: b :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 (a :: b :: c :: rest)
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca,
      hident, hside, hndclip, htri⟩ :=
    exists_front_ear V hlen hsimple hnd
  have hsimprot : PolygonSimple (a :: b :: c :: rest) := by
    rw [← hrot]; exact (PolygonSimple_rotate V r).mpr hsimple
  refine ⟨r, a, b, c, rest, hrot, ?_, hndclip, ?_, ?_⟩
  · exact PolygonSimple_clip a b c rest hsimprot hside
  · exact polyCycWind_clip_eq_of_identity a b c p q rest hp hq hpa hab hbc hcq hca hident
  · exact shoelace2_orient_clip a b c rest htri

/-- **The genuine topological core of the planar Umlaufsatz (the two-ears
    theorem, in concrete clipped-cons form).**  A simple, non-degenerate polygon
    with at least four vertices has an *ear* that can be clipped: there is a
    cyclic rotation `V.rotate r = a :: b :: c :: rest` whose second vertex `b`
    can be removed, yielding the strictly shorter vertex cycle `a :: c :: rest`
    that is still planar-simple (`PolygonSimple`) and non-degenerate
    (`polyCycNondeg`), with the *same* cyclic turning (`polyCycWind`) and the
    *same* orientation (sign of the signed area `HexArea.shoelace2`).

    This statement concentrates **all** the irreducible Jordan-curve-theorem-level
    content of the planar Umlaufsatz (existence of a convex ear and the
    preservation of planar simplicity under its removal).  Everything around it
    is now proved sorry-free: the rotation-invariance toolkit
    (`shoelace2_rotate`, `polyCycWind_rotate`, `PolygonSimple_rotate`,
    `polyCycNondeg_rotate`) transports the clipped cycle back to `V`'s own
    closing form, so `polygon_ear_reduction` is derived from this core, and the
    base case `polyWind_triangle` and the strong induction
    `polygon_umlaufsatz_take` are also sorry-free.  Absent from Mathlib. -/
lemma exists_ear_clip (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      PolygonSimple (a :: c :: rest) ∧
      polyCycNondeg (a :: c :: rest) ∧
      polyCycWind (a :: c :: rest) = polyCycWind V ∧
      ((0:ℝ) < HexArea.shoelace2 V ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, rest, hrot, hsimp', hnd', hwind', harea'⟩ :=
    exists_ear_rotation V hlen hsimple hnd
  refine ⟨r, a, b, c, rest, hrot, hsimp', hnd', ?_, ?_⟩
  · -- turning: transport via rotation invariance `polyCycWind_rotate`
    rw [hwind', ← hrot]
    exact polyCycWind_rotate V r (by omega)
  · -- area sign: transport via rotation invariance `shoelace2_rotate`
    have hV : HexArea.shoelace2 V = HexArea.shoelace2 (a :: b :: c :: rest) := by
      rw [← hrot]; exact (shoelace2_rotate V r).symm
    rw [hV]; exact harea'

/-- **Ear-clipping reduction — derived sorry-free from the two-ears core
    `exists_ear_clip` and the rotation-invariance toolkit.**  For a
    non-self-intersecting non-degenerate polygon
    with at least four vertices there is a vertex that can be *clipped* (an
    "ear"): a vertex whose removal yields a strictly shorter polygon `V'` that
    is still simple and non-degenerate, *with the same total turning and the
    same orientation (sign of signed area)*.

    This bundles exactly the four facts an ear-clipping step needs:
    * `V'.length = V.length - 1` and `3 ≤ V'.length` (the induction descends);
    * `PolygonSimple V'` and `polyNondeg (V' ++ V'.take 2)` (planar simplicity /
      non-degeneracy are preserved by ear removal);
    * `polyWind (V ++ V.take 2) = polyWind (V' ++ V'.take 2)` (the total
      exterior-angle turning is unchanged: the three local turns at the ear and
      its two neighbours merge into two turns with the same net angle — the
      arg-telescoping identity, made *exact* rather than only mod `2π` by the
      convexity of a genuine ear);
    * `0 < shoelace2 V ↔ 0 < shoelace2 V'` (the orientation is unchanged: by
      `HexArea.shoelace2_ear` the area changes by the ear-triangle term, which —
      for a convex ear — has the same sign as the whole polygon).

    The genuinely hard, Jordan-curve-theorem-level content (existence of a
    convex ear and that its removal preserves planar simplicity) is concentrated
    in this single statement; everything that consumes it — the base case
    `polyWind_triangle` and the strong induction `polygon_umlaufsatz_take` — is
    proved sorry-free.  Absent from Mathlib. -/
lemma polygon_ear_reduction (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyNondeg (V ++ V.take 2)) :
    ∃ V' : List ℂ, V'.length = V.length - 1 ∧ 3 ≤ V'.length ∧
      PolygonSimple V' ∧ polyNondeg (V' ++ V'.take 2) ∧
      polyWind (V ++ V.take 2) = polyWind (V' ++ V'.take 2) ∧
      ((0:ℝ) < HexArea.shoelace2 V ↔ (0:ℝ) < HexArea.shoelace2 V') := by
  obtain ⟨r, a, b, c, rest, hrot, hsimp', hnd', hwind', harea'⟩ :=
    exists_ear_clip V hlen hsimple hnd
  have hlenrot : (V.rotate r).length = V.length := List.length_rotate ..
  rw [hrot] at hlenrot
  simp only [List.length_cons] at hlenrot
  refine ⟨a :: c :: rest, ?_, ?_, hsimp', hnd', ?_, harea'⟩
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · rw [← polyCycWind_def, ← polyCycWind_def]; exact hwind'.symm

/-
**The planar Umlaufsatz, index-free closing form.**  Total exterior-angle
    turning `= 2π · sign(signed area)`, with the cycle closed by `V.take 2`.
    Proved by strong induction on `V.length`: the base case `V.length = 3` is
    `polyWind_triangle`; the inductive step clips an ear via
    `polygon_ear_reduction`, which keeps both the turning and the orientation
    fixed while strictly shortening the polygon.
-/
lemma polygon_umlaufsatz_take (V : List ℂ) (hlen : 3 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyNondeg (V ++ V.take 2)) :
    polyWind (V ++ V.take 2) =
      2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1) := by
  induction' n : V.length using Nat.strong_induction_on with n ih generalizing V;
  by_cases hlen4 : 4 ≤ V.length;
  · obtain ⟨ V', hV'₁, hV'₂, hV'₃, hV'₄, hV'₅, hV'₆ ⟩ := polygon_ear_reduction V hlen4 hsimple hnd ; specialize ih ( List.length V' ) ( by omega ) V' hV'₂ hV'₃ hV'₄ rfl ; aesop ( simp_config := { singlePass := true } ) ;
  · rcases V with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | V ⟩ ⟩ ⟩ ) <;> norm_num at *;
    convert polyWind_triangle a b c _ using 1;
    · split_ifs <;> ring;
    · exact hnd.1

lemma polygon_umlaufsatz (V : List ℂ) (hlen : 3 ≤ V.length)
    (hsimple : PolygonSimple V)
    (hnd : polyNondeg (V ++ [V[0]'(by omega), V[1]'(by omega)])) :
    polyWind (V ++ [V[0]'(by omega), V[1]'(by omega)]) =
      2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1) := by
  rw [closeList_eq V (by omega)] at hnd ⊢
  exact polygon_umlaufsatz_take V hlen hsimple hnd

/-
**Honeycomb edge-disjointness (remaining geometric core).**  For a simple
    closed hex trail, two closed edges of the embedded polygon that share no
    endpoint have disjoint segments.  This is the *only* genuinely geometric
    content of honeycomb planarity (the `Nodup` half being already established by
    `hex_closed_trail_embed_nodup`).

    The genuinely geometric content (two distinct unit honeycomb edges meet only
    at a shared vertex) is factored out as the general, reusable lemma
    `hexEdge_segments_disjoint` in `RequestProject.SAWUmlaufHexEdge`; what remains
    here is the combinatorial wiring (each polygon edge is a `hexGraph`
    adjacency between consecutive trail vertices, and the four point-inequalities
    transfer to vertex-inequalities via `correctHexEmbed_injective`).

    **Sorry**: reduces to the geometric core `hexEdge_segments_disjoint` plus the
    `closedEdges`/`hexGraph`-adjacency wiring; the geometry is absent from
    Mathlib.
-/
lemma hexEmbeddedPolygon_edges_disjoint (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    ∀ e₁ ∈ closedEdges (hexEmbeddedPolygon L),
      ∀ e₂ ∈ closedEdges (hexEmbeddedPolygon L),
        e₁.1 ≠ e₂.1 → e₁.1 ≠ e₂.2 → e₁.2 ≠ e₂.1 → e₁.2 ≠ e₂.2 →
        Disjoint (segment ℝ e₁.1 e₁.2) (segment ℝ e₂.1 e₂.2) := by
  unfold closedEdges hexEmbeddedPolygon; simp +decide ;
  intros a b hab a_2 b_1 hab_2 hneq1 hneq2 hneq3 hneq4
  obtain ⟨i, hi⟩ : ∃ i, i < (List.map correctHexEmbed L).dropLast.length ∧ a = (List.map correctHexEmbed L).dropLast[i]! ∧ b = ((List.map correctHexEmbed L).dropLast.rotate 1)[i]! := by
    rw [ List.mem_iff_get ] at hab;
    obtain ⟨ n, hn ⟩ := hab; use n; simp_all +decide [ List.get ] ;
    grind
  obtain ⟨j, hj⟩ : ∃ j, j < (List.map correctHexEmbed L).dropLast.length ∧ a_2 = (List.map correctHexEmbed L).dropLast[j]! ∧ b_1 = ((List.map correctHexEmbed L).dropLast.rotate 1)[j]! := by
    rw [ List.mem_iff_get ] at hab_2;
    obtain ⟨ j, hj ⟩ := hab_2; use j; simp_all +decide [ List.get ] ;
    grind;
  simp_all +decide [ List.getElem?_eq_getElem, List.getElem_rotate ];
  apply hexEdge_segments_disjoint;
  any_goals intro H; simp_all +decide [ correctHexEmbed_injective.eq_iff ];
  · by_cases hi' : i + 1 < L.length - 1;
    · convert hexTrailList_adj_get L h_trail ( by omega ) i ( by omega ) using 1;
      norm_num [ Nat.mod_eq_of_lt hi' ];
    · convert hex_closure_adj L hL h_trail h_closed |>.1 using 1;
      · grind;
      · norm_num [ show i + 1 = L.length - 1 by omega ];
  · by_cases h : j + 1 < L.length - 1 <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    · convert hexTrailList_adj_get L h_trail ( by omega ) j ( by omega ) using 1;
    · cases h.eq_or_lt <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · convert hex_closure_adj L ( by linarith ) h_trail h_closed |>.1 using 1;
        simp +decide [ *, Nat.sub_sub ];
      · omega

/-- For any honeycomb trail `M` (a `HexTrailList`), the embedded chain
    `M.map correctHexEmbed` is non-degenerate: every consecutive triple is a
    genuine hex turn, whose cross product is `±√3/2 ≠ 0`
    (`hex_turn_cross_ne_zero`).  Clean structural induction matching the
    `HexTrailList` / `polyNondeg` recursions. -/
lemma hexTrailList_map_emb_polyNondeg (M : List HexVertex) (h : HexTrailList M) :
    polyNondeg (M.map correctHexEmbed) := by
  induction M with
  | nil => trivial
  | cons a M ih =>
    cases M with
    | nil => trivial
    | cons b M =>
      cases M with
      | nil => trivial
      | cons c M =>
        obtain ⟨h1, h2, h3, h4⟩ := h
        exact ⟨hex_turn_cross_ne_zero a b c h1 h2 h3, ih h4⟩

/-
The closed honeycomb vertex cycle `L.dropLast ++ [L[0], L[1]]` (the interior
    vertices followed by the first two vertices, closing the loop and exposing
    the two closing turns) is itself a `HexTrailList`.  The interior adjacencies
    / no-backtracks come from `HexTrailList L`; the two closing turns come from
    `hex_closure_adj` and `hex_closure_nobacktrack`; the remaining junction
    no-backtrack `s(L[m-3],L[m-2]) ≠ s(L[m-2],L[0])` follows from
    `hex_closed_trail_start_not_interior` (`L[0] ≠ L[m-3]`).
-/
lemma hexClosedTrail_dropLast_append_trailList (L : List HexVertex)
    (hL : 4 ≤ L.length) (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?) (h_simple : L.tail.dropLast.Nodup) :
    HexTrailList (L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩]) := by
  have h_adj : ∀ k < (L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩]).length - 1, hexGraph.Adj ((L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩])[k]!) ((L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩])[k + 1]!) := by
    intro k hk
    by_cases hk_case : k < L.length - 2;
    · convert hexTrailList_adj_get L h_trail ( by omega ) k ( by omega ) using 1; all_goals grind;
    · by_cases hk_case : k = L.length - 2;
      · convert ( hex_closure_adj L hL h_trail h_closed ).1 using 1; all_goals grind;
      · convert hex_closure_adj L hL h_trail h_closed |>.2 using 1; all_goals grind;
  have h_nobacktrack : ∀ k < (L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩]).length - 2, s((L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩])[k]!, (L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩])[k + 1]!) ≠ s((L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩])[k + 1]!, (L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩])[k + 2]!) := by
    intro k hk
    by_cases hk_case : k < L.length - 3;
    · convert hexTrailList_nobacktrack_get L h_trail k ( by omega ) using 1; all_goals grind;
    · by_cases hk_case : k = L.length - 3;
      · have := hex_closed_trail_start_not_interior L hL h_trail h_closed h_simple;
        contrapose! this;
        rcases L with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | L ⟩ ⟩ ⟩ ) <;> simp_all +decide [ List.get ];
        · contradiction;
        · contradiction;
        · grind +qlia;
      · convert hex_closure_nobacktrack L hL h_simple using 1;
        · grind +revert;
        · grind +splitImp;
  have h_hex_trail : ∀ {N : List HexVertex}, (∀ k < N.length - 1, hexGraph.Adj (N[k]!) (N[k + 1]!)) → (∀ k < N.length - 2, s(N[k]!, N[k + 1]!) ≠ s(N[k + 1]!, N[k + 2]!)) → HexTrailList N := by
    intros N h_adj h_nobacktrack; induction' N with a N ih; simp_all +decide [ HexTrailList ] ;
    rcases N with ( _ | ⟨ b, _ | ⟨ c, N ⟩ ⟩ ) <;> simp +decide [ HexTrailList ] at *;
    exact ⟨ h_adj 0 bot_le, h_adj 1 ( by linarith ), h_nobacktrack 0 bot_le, ih ( fun k hk => h_adj ( k + 1 ) ( by linarith ) ) ( fun k hk => h_nobacktrack ( k + 1 ) ( by linarith ) ) ⟩;
  exact h_hex_trail h_adj h_nobacktrack

lemma hexEmbeddedPolygon_polyNondeg (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    polyNondeg (hexEmbeddedPolygon L ++
      [(hexEmbeddedPolygon L)[0]'(by rw [hexEmbeddedPolygon_length]; omega),
       (hexEmbeddedPolygon L)[1]'(by rw [hexEmbeddedPolygon_length]; omega)]) := by
  -- Rewrite the embedded closed polygon as the embedding of the closed vertex
  -- cycle `L.dropLast ++ [L[0], L[1]]`, then apply the trail-level
  -- non-degeneracy lemma `hexTrailList_map_emb_polyNondeg`.
  have hmap : hexEmbeddedPolygon L ++
      [(hexEmbeddedPolygon L)[0]'(by rw [hexEmbeddedPolygon_length]; omega),
       (hexEmbeddedPolygon L)[1]'(by rw [hexEmbeddedPolygon_length]; omega)]
      = (L.dropLast ++ [L.get ⟨0, by omega⟩, L.get ⟨1, by omega⟩]).map
          correctHexEmbed := by
    unfold hexEmbeddedPolygon; simp +decide [ List.getElem_map, List.getElem?_eq_getElem ] ;
  rw [hmap]
  exact hexTrailList_map_emb_polyNondeg _
    (hexClosedTrail_dropLast_append_trailList L hL h_trail h_closed h_simple)

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