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
import RequestProject.SAWUmlaufSegment

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
  sorry

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