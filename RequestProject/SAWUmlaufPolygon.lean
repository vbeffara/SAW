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

/-- **The empty-convex-ear existence core (the genuine Meisters two-ears
    content), without the local turning-range bounds.**  A simple,
    non-degenerate polygon with at least four vertices has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose middle vertex `b` is a convex ear:
    the corner triangle `a b c` is non-degenerate, contains no far vertex
    strictly inside (`hempty`) and none on the closed diagonal `a–c`
    (`hdiag`), the five cyclic edge non-degeneracies hold, the clipped cycle
    `a :: c :: rest` is still cyclically non-degenerate, and the cut-off ear
    triangle has the *same orientation* as the clip (`0 < shoelace2 [a,b,c] ↔
    0 < shoelace2 (a :: c :: rest)`).

    This is the irreducible Jordan-curve-theorem-level core (absent from
    Mathlib): choose the extreme (leftmost-lowest) convex vertex via
    `HexArea.exists_lex_min_mem` / `lexMin_not_inTriangleStrict`, and if its
    corner triangle is non-empty pivot to the vertex farthest from the base
    diagonal (`HexArea.exists_max_cross`, `farthest_region_empty`,
    `inTriangleStrict_pos_nest`, `subTri_axc_orient_pos`,
    `inTriangleStrict_apex_sameSide`), splitting along an interior diagonal and
    recursing on the strictly shorter sub-polygon.  Recorded partial progress:
    consumed by `exists_front_ear_core` below. -/
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
  sorry

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
  sorry

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