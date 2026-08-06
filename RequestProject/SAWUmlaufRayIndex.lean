import Mathlib
import RequestProject.SAWUmlaufPtWindRay

/-!
# `SAWUmlaufRayIndex` — the ray-crossing index formula for `ptWind`

`RequestProject.SAWUmlaufPtWindRay` proves the *vanishing* half of the branch-cut
analysis of the point-winding number: if **no** closed edge of the cycle `V`
crosses the ray from `x` in a fixed direction, the sweep-angle sum telescopes to
`0`.  This file removes the "no crossing" hypothesis and computes the sum in
general:

  `ptWind x V = Σ_{closed edges (a,b)} wrapTerm x e a b`,

where the per-edge **wrap defect**

  `wrapTerm x e a b = arg ((b-x)/(a-x)) - (arg ((b-x)/e) - arg ((a-x)/e))`

is always one of `0`, `2π`, `-2π` (`wrapTerm_trichotomy`), vanishes exactly when
the edge misses the branch cut (`wrapTerm_eq_zero_of_avoids`, inherited from
`argSubRel_of_segment_avoids_neg`), and equals `∓2π` on a transversal crossing of
the cut, the sign being the crossing direction (`wrapTerm_eq_neg_two_pi_of_up`,
`wrapTerm_eq_two_pi_of_down`).  In the rotated coordinates `w ↦ (w - x)/e` the
branch cut is the non-positive real axis, i.e. the ray emanating from `x` in the
direction `-e`.

This is the classical *ray-crossing* (point-in-polygon) formula: the winding
number of a closed polygon around `x` is `2π` times the signed number of
crossings of any ray out of `x` by the edge cycle.

## Contents

* `wrapTerm`, `wrapSum` — the per-edge defect and its sum along an open chain;
* `wrapSum_concat`, `ptTurn_eq_wrapSum_add`, `ptWind_eq_wrapSum` — the exact
  telescoping identity (the boundary terms of the closed cycle cancel);
* `wrapTerm_trichotomy` — `wrapTerm ∈ {0, 2π, -2π}`;
* `wrapTerm_eq_zero_of_avoids` — no crossing ⟹ no defect;
* `cross_eq_scaled_re_of_im_crossing` — the elementary algebra of a transversal
  crossing of the real axis: the cross product of the endpoints is the crossing
  abscissa scaled by the (positive) imaginary drop;
* `wrapTerm_eq_neg_two_pi_of_up`, `wrapTerm_eq_two_pi_of_down` — the value of the
  defect at an upward / downward crossing of the cut;
* `ptWind_eq_of_single_crossing` — the packaged form used downstream: if every
  *path* edge of `V` misses the cut and the closing edge crosses it upward, then
  `ptWind x V = -2π` (and the mirror statement).

## Downstream use (NOT a dead branch)

The file is imported by `RequestProject.SAWUmlaufChordLiftAux`, hence lies on the
live route to `polygon_umlaufsatz`.  It is *preparation*, in the precise sense
recorded in `PROOF_STATUS.md`, for the four remaining Jordan-level gaps of the
Umlaufsatz chain (`clipped_ear_escape_walk`,
`vertex_escape_joinedIn_arbitrarily_far_one_diag`,
`chord_lift_other_not_on_diagonal`, `chord_piece_orient`).  Every one of those
statements is an instance of the polygonal Jordan curve theorem — "a point whose
winding vanishes lies in the unbounded complementary component", respectively
"the two sides of an edge carry winding numbers differing by `2π`" — and the
crossing formula proved here is the elementary computation of the winding number
that makes such statements accessible without any analytic Jordan input: it
turns the winding number into a finite signed count that can be compared along a
path.
-/

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 1000000

/-! ## 1. The wrap defect of a single edge, and its sum along a chain -/

/-- **The branch-wrap defect of the edge `(a, b)`, seen from `x` in the frame
`e`.**  It is the failure of the sweep angle of the edge to be the plain
difference of the two rotated position arguments; equivalently `2π` times the
signed number of times the edge crosses the branch cut (the ray from `x` in
direction `-e`). -/
def wrapTerm (x e a b : ℂ) : ℝ :=
  Complex.arg ((b - x) / (a - x))
    - (Complex.arg ((b - x) / e) - Complex.arg ((a - x) / e))

/-- The sum of the wrap defects along the consecutive pairs of an open chain. -/
def wrapSum (x e : ℂ) : List ℂ → ℝ
  | a :: b :: rest => wrapTerm x e a b + wrapSum x e (b :: rest)
  | _ => 0

@[simp] lemma wrapSum_nil (x e : ℂ) : wrapSum x e [] = 0 := rfl

@[simp] lemma wrapSum_singleton (x e a : ℂ) : wrapSum x e [a] = 0 := rfl

lemma wrapSum_cons_cons (x e a b : ℂ) (L : List ℂ) :
    wrapSum x e (a :: b :: L) = wrapTerm x e a b + wrapSum x e (b :: L) := rfl

/-- The wrap defect vanishes exactly when the edge satisfies the exact
argument-subtraction relation of `RequestProject.SAWUmlaufPtWindRay`. -/
lemma wrapTerm_eq_zero_iff_argSubRel (x e a b : ℂ) :
    wrapTerm x e a b = 0 ↔ argSubRel x e a b := by
  unfold wrapTerm argSubRel
  constructor <;> intro h <;> linarith

/-- Appending one vertex to a nonempty chain adds exactly one wrap defect. -/
lemma wrapSum_concat (x e : ℂ) :
    ∀ (a : ℂ) (L : List ℂ) (z : ℂ),
      wrapSum x e (a :: L ++ [z])
        = wrapSum x e (a :: L) + wrapTerm x e ((a :: L).getLastD a) z := by
  intro a L
  induction L generalizing a with
  | nil => intro z; simp [wrapSum_cons_cons]
  | cons b L ih =>
      intro z
      have h1 : wrapSum x e ((a :: b :: L) ++ [z])
          = wrapTerm x e a b + wrapSum x e ((b :: L) ++ [z]) := by
        simp only [List.cons_append]
        rw [wrapSum_cons_cons]
      rw [h1, ih b z, wrapSum_cons_cons, getLastD_cons_cons]
      ring

/-! ## 2. The exact telescoping identity -/

/-- **Telescoping with defects.**  Along any open chain the sweep-angle sum is
the sum of the wrap defects plus the difference of the endpoint arguments in the
frame `e`.  (With all defects `0` this is `ptTurn_telescope_branch`.) -/
lemma ptTurn_eq_wrapSum_add (x e : ℂ) :
    ∀ (a : ℂ) (L : List ℂ),
      ptTurn x (a :: L)
        = wrapSum x e (a :: L)
          + (Complex.arg (((a :: L).getLastD a - x) / e) - Complex.arg ((a - x) / e)) := by
  intro a L
  induction L generalizing a with
  | nil => simp [ptTurn]
  | cons b L ih =>
      rw [ptTurn_cons_cons, ih b, wrapSum_cons_cons, getLastD_cons_cons]
      unfold wrapTerm
      ring

/-- **The winding number is the total wrap defect.**  For any frame `e`, the
winding of the closed cycle `V` around `x` is the sum of the wrap defects of the
closed edges: the endpoint arguments of the closed chain cancel. -/
lemma ptWind_eq_wrapSum (x e : ℂ) (V : List ℂ) :
    ptWind x V = wrapSum x e (V ++ V.take 1) := by
  cases V with
  | nil => simp [ptWind, wrapSum]
  | cons a V =>
      unfold ptWind
      have hform : (a :: V) ++ (a :: V).take 1 = a :: (V ++ [a]) := by simp [List.take]
      rw [hform, ptTurn_eq_wrapSum_add x e a (V ++ [a])]
      have hlast : ((a :: (V ++ [a])).getLastD a) = a := by
        have h2 : a :: (V ++ [a]) = (a :: V) ++ [a] := by simp
        rw [h2, List.getLastD_concat]
      rw [hlast]
      ring

/-! ## 3. The trichotomy `wrapTerm ∈ {0, 2π, -2π}` -/

/-- **The wrap defect is `2π` times an integer of absolute value at most one.**
Both `arg` values live in `(-π, π]`, so the defect lies in `(-3π, 3π)`; and it is
a multiple of `2π` because `arg (B/A) ≡ arg B - arg A` in `ℝ / 2πℤ`. -/
lemma wrapTerm_trichotomy (x e a b : ℂ) (he : e ≠ 0) (ha : a ≠ x) (hb : b ≠ x) :
    wrapTerm x e a b = 0 ∨ wrapTerm x e a b = 2 * Real.pi
      ∨ wrapTerm x e a b = -(2 * Real.pi) := by
  have hA : (a - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr ha) he
  have hB : (b - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr hb) he
  have hratio : (b - x) / (a - x) = ((b - x) / e) / ((a - x) / e) := by
    field_simp
  have hwrap : wrapTerm x e a b
      = Complex.arg (((b - x) / e) / ((a - x) / e))
        - (Complex.arg ((b - x) / e) - Complex.arg ((a - x) / e)) := by
    unfold wrapTerm; rw [hratio]
  set A := (a - x) / e with hAdef
  set B := (b - x) / e with hBdef
  have hangle : ((B / A).arg : Real.Angle) = (B.arg : Real.Angle) - (A.arg : Real.Angle) :=
    Complex.arg_div_coe_angle hB hA
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hangle
  obtain ⟨k, hk⟩ := hangle
  have h1 := Complex.neg_pi_lt_arg (B / A)
  have h2 := Complex.arg_le_pi (B / A)
  have h3 := Complex.neg_pi_lt_arg A
  have h4 := Complex.arg_le_pi A
  have h5 := Complex.neg_pi_lt_arg B
  have h6 := Complex.arg_le_pi B
  have hpi := Real.pi_pos
  have hkr : (-2 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 2 := by
    constructor <;> nlinarith [hk]
  have hk' : k = 0 ∨ k = 1 ∨ k = -1 := by
    have : (-2 : ℤ) < k ∧ k < 2 := by exact_mod_cast hkr
    omega
  rcases hk' with rfl | rfl | rfl
  · left; rw [hwrap, hk]; push_cast; ring
  · right; left; rw [hwrap, hk]; push_cast; ring
  · right; right; rw [hwrap, hk]; push_cast; ring

/-- **No crossing, no defect.**  If the rotated edge segment misses the
non-positive real axis (the edge does not cross the ray from `x` in direction
`-e`), its wrap defect vanishes. -/
lemma wrapTerm_eq_zero_of_avoids (x e : ℂ) (he : e ≠ 0) (a b : ℂ)
    (ha : a ≠ x) (hb : b ≠ x)
    (havoid : ∀ z ∈ segment ℝ ((a - x) / e) ((b - x) / e),
        ¬ (z.im = 0 ∧ z.re ≤ 0)) :
    wrapTerm x e a b = 0 :=
  (wrapTerm_eq_zero_iff_argSubRel x e a b).mpr
    (argSubRel_of_segment_avoids_neg x e he a b ha hb havoid)

/-! ## 4. The value of the defect at a transversal crossing -/

/-- Real part of a point of the parametrised segment. -/
lemma param_point_re (A B : ℂ) (t : ℝ) :
    (A + t • (B - A)).re = A.re + t * (B.re - A.re) := by
  simp

/-- Imaginary part of a point of the parametrised segment. -/
lemma param_point_im (A B : ℂ) (t : ℝ) :
    (A + t • (B - A)).im = A.im + t * (B.im - A.im) := by
  simp

/-- **The algebra of a transversal crossing of the real axis.**  If `A.im < 0 <
B.im` then the segment `[A, B]` meets the real axis in the single point
`A + t(B - A)` with `t = -A.im / (B.im - A.im) ∈ (0,1)`, and the cross product of
the endpoints is that point's abscissa scaled by the positive imaginary drop.
Consequently the sign of `cross A B` is the sign of the crossing abscissa. -/
lemma cross_eq_scaled_re_of_im_crossing (A B : ℂ) (hA : A.im < 0) (hB : 0 < B.im) :
    cross A B = (B.im - A.im) * (A + (-A.im / (B.im - A.im)) • (B - A)).re := by
  have hs : B.im - A.im > 0 := by linarith
  have hne : B.im - A.im ≠ 0 := ne_of_gt hs
  rw [param_point_re A B (-A.im / (B.im - A.im)), cross]
  field_simp
  ring

/-- If the segment `[A, B]` of a transversal upward crossing meets the
non-positive real axis, then `cross A B < 0` — unless the crossing point is the
origin, which is excluded because the crossing abscissa is then `0` and the
segment passes through `0`.  We state the useful direction: a crossing point with
*negative* abscissa forces `cross A B < 0`. -/
lemma cross_neg_of_up_crossing (A B : ℂ) (hA : A.im < 0) (hB : 0 < B.im)
    (hre : (A + (-A.im / (B.im - A.im)) • (B - A)).re < 0) :
    cross A B < 0 := by
  have hs : B.im - A.im > 0 := by linarith
  rw [cross_eq_scaled_re_of_im_crossing A B hA hB]
  exact mul_neg_of_pos_of_neg hs hre

/-- Mirror statement for a downward crossing. -/
lemma cross_pos_of_down_crossing (A B : ℂ) (hA : 0 < A.im) (hB : B.im < 0)
    (hre : (B + (-B.im / (A.im - B.im)) • (A - B)).re < 0) :
    0 < cross A B := by
  have h := cross_neg_of_up_crossing B A hB hA hre
  have hswap : cross A B = -cross B A := by simp only [cross]; ring
  linarith

/-- The sine of the argument difference is the normalised cross product. -/
lemma sin_arg_sub (A B : ℂ) :
    Real.sin (B.arg - A.arg) * (‖A‖ * ‖B‖) = cross A B := by
  rw [Real.sin_sub, cross]
  have hAre : ‖A‖ * Real.cos A.arg = A.re := Complex.norm_mul_cos_arg A
  have hAim : ‖A‖ * Real.sin A.arg = A.im := Complex.norm_mul_sin_arg A
  have hBre : ‖B‖ * Real.cos B.arg = B.re := Complex.norm_mul_cos_arg B
  have hBim : ‖B‖ * Real.sin B.arg = B.im := Complex.norm_mul_sin_arg B
  rw [← hAre, ← hAim, ← hBre, ← hBim]
  ring

/-- **Upward crossing of the cut: the defect is `-2π`.**  In the frame `e`, the
edge goes from the lower half plane to the upper half plane and crosses the
branch cut (`cross A B < 0`, which by `cross_neg_of_up_crossing` is exactly a
crossing point of negative abscissa). -/
lemma wrapTerm_eq_neg_two_pi_of_up (x e a b : ℂ) (he : e ≠ 0) (ha : a ≠ x) (hb : b ≠ x)
    (hAim : ((a - x) / e).im < 0) (hBim : 0 < ((b - x) / e).im)
    (hcross : cross ((a - x) / e) ((b - x) / e) < 0) :
    wrapTerm x e a b = -(2 * Real.pi) := by
  have hA : (a - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr ha) he
  have hB : (b - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr hb) he
  have hratio : (b - x) / (a - x) = ((b - x) / e) / ((a - x) / e) := by field_simp
  have hwrap : wrapTerm x e a b
      = Complex.arg (((b - x) / e) / ((a - x) / e))
        - (Complex.arg ((b - x) / e) - Complex.arg ((a - x) / e)) := by
    unfold wrapTerm; rw [hratio]
  set A := (a - x) / e with hAdef
  set B := (b - x) / e with hBdef
  -- `arg A ∈ (-π, 0)` and `arg B ∈ (0, π)`.
  have hargA : A.arg < 0 := Complex.arg_neg_iff.mpr hAim
  have hargA' : -Real.pi < A.arg := Complex.neg_pi_lt_arg A
  have hargB : 0 < B.arg :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hBim.le)
      (fun h => by
        have := (Complex.arg_eq_zero_iff.mp h.symm).2
        linarith)
  have hargB' : B.arg ≤ Real.pi := Complex.arg_le_pi B
  -- The difference is in `(0, 2π)` and has negative sine, hence exceeds `π`.
  have hsin : Real.sin (B.arg - A.arg) < 0 := by
    have hnorm : 0 < ‖A‖ * ‖B‖ := by positivity
    have := sin_arg_sub A B
    nlinarith [this, hcross, hnorm]
  have hgt : Real.pi < B.arg - A.arg := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < B.arg - A.arg := by linarith
    have : 0 ≤ Real.sin (B.arg - A.arg) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt h1) hcon
    linarith
  -- The wrap integer is therefore `-1`.
  have hangle : ((B / A).arg : Real.Angle) = (B.arg : Real.Angle) - (A.arg : Real.Angle) :=
    Complex.arg_div_coe_angle hB hA
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hangle
  obtain ⟨k, hk⟩ := hangle
  have h1 := Complex.neg_pi_lt_arg (B / A)
  have h2 := Complex.arg_le_pi (B / A)
  have hpi := Real.pi_pos
  have hklt : (k : ℝ) < 0 := by nlinarith [hk]
  have hkgt : (-2 : ℝ) < (k : ℝ) := by nlinarith [hk]
  have hk1 : k = -1 := by
    have hz1 : (-2 : ℤ) < k := by exact_mod_cast hkgt
    have hz2 : k < 0 := by exact_mod_cast hklt
    omega
  rw [hwrap, hk, hk1]
  push_cast
  ring

/-- **Downward crossing of the cut: the defect is `2π`.** -/
lemma wrapTerm_eq_two_pi_of_down (x e a b : ℂ) (he : e ≠ 0) (ha : a ≠ x) (hb : b ≠ x)
    (hAim : 0 < ((a - x) / e).im) (hBim : ((b - x) / e).im < 0)
    (hcross : 0 < cross ((a - x) / e) ((b - x) / e)) :
    wrapTerm x e a b = 2 * Real.pi := by
  have hA : (a - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr ha) he
  have hB : (b - x) / e ≠ 0 := div_ne_zero (sub_ne_zero.mpr hb) he
  have hratio : (b - x) / (a - x) = ((b - x) / e) / ((a - x) / e) := by field_simp
  have hwrap : wrapTerm x e a b
      = Complex.arg (((b - x) / e) / ((a - x) / e))
        - (Complex.arg ((b - x) / e) - Complex.arg ((a - x) / e)) := by
    unfold wrapTerm; rw [hratio]
  set A := (a - x) / e with hAdef
  set B := (b - x) / e with hBdef
  have hargA : 0 < A.arg :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hAim.le)
      (fun h => by
        have := (Complex.arg_eq_zero_iff.mp h.symm).2
        linarith)
  have hargA' : A.arg ≤ Real.pi := Complex.arg_le_pi A
  have hargB : B.arg < 0 := Complex.arg_neg_iff.mpr hBim
  have hargB' : -Real.pi < B.arg := Complex.neg_pi_lt_arg B
  have hsin : 0 < Real.sin (B.arg - A.arg) := by
    have hnorm : 0 < ‖A‖ * ‖B‖ := by positivity
    have := sin_arg_sub A B
    nlinarith [this, hcross, hnorm]
  have hlt : B.arg - A.arg < -Real.pi := by
    by_contra hcon
    push_neg at hcon
    have h1 : B.arg - A.arg < 0 := by linarith
    have : Real.sin (B.arg - A.arg) ≤ 0 := by
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -(B.arg - A.arg))
        (by linarith) (by linarith)
      rw [Real.sin_neg] at this
      linarith
    linarith
  have hangle : ((B / A).arg : Real.Angle) = (B.arg : Real.Angle) - (A.arg : Real.Angle) :=
    Complex.arg_div_coe_angle hB hA
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hangle
  obtain ⟨k, hk⟩ := hangle
  have h1 := Complex.neg_pi_lt_arg (B / A)
  have h2 := Complex.arg_le_pi (B / A)
  have hpi := Real.pi_pos
  have hkgt : (0 : ℝ) < (k : ℝ) := by nlinarith [hk]
  have hklt : (k : ℝ) < 2 := by nlinarith [hk]
  have hk1 : k = 1 := by
    have hz1 : (0 : ℤ) < k := by exact_mod_cast hkgt
    have hz2 : k < 2 := by exact_mod_cast hklt
    omega
  rw [hwrap, hk, hk1]
  push_cast
  ring

/-- **From a crossing point on the segment to the sign of the cross product
(upward crossing).**  If the edge runs from the lower to the upper half plane and
some point of the segment lies on the *negative* real axis, then the endpoints
have negative cross product, i.e. the edge really crosses the branch cut. -/
lemma cross_neg_of_segment_crossing (A B z : ℂ) (hA : A.im < 0) (hB : 0 < B.im)
    (hz : z ∈ segment ℝ A B) (hzim : z.im = 0) (hzre : z.re < 0) :
    cross A B < 0 := by
  rw [segment_eq_image' ℝ A B] at hz
  obtain ⟨t, -, rfl⟩ := hz
  have hs : (0:ℝ) < B.im - A.im := by linarith
  have him : A.im + t * (B.im - A.im) = 0 := by
    rw [← param_point_im A B t]; exact hzim
  have ht' : t = -A.im / (B.im - A.im) := by
    field_simp
    linarith
  subst ht'
  exact cross_neg_of_up_crossing A B hA hB hzre

/-- Mirror form of `cross_neg_of_segment_crossing` for a downward crossing. -/
lemma cross_pos_of_segment_crossing (A B z : ℂ) (hA : 0 < A.im) (hB : B.im < 0)
    (hz : z ∈ segment ℝ A B) (hzim : z.im = 0) (hzre : z.re < 0) :
    0 < cross A B := by
  have h := cross_neg_of_segment_crossing B A z hB hA (by rwa [segment_symm]) hzim hzre
  have hswap : cross A B = -cross B A := by simp only [cross]; ring
  linarith

/-! ## 5. The packaged single-crossing formula -/

/-- **Ray crossing formula, single-crossing form.**  Suppose every *path* edge of
the cycle `V` (the consecutive pairs of the list) misses the branch cut, and the
closing edge `(last, first)` has wrap defect `w`.  Then `ptWind x V = w`.  With
`wrapTerm_eq_zero_of_avoids` and the two crossing lemmas above, this computes the
winding number of a polygon from a single ray crossing. -/
lemma ptWind_eq_wrapTerm_last (x e : ℂ) (V : List ℂ) (a : ℂ) (L : List ℂ)
    (hV : V = a :: L)
    (hzero : ∀ p ∈ V.zip (V.drop 1), wrapTerm x e p.1 p.2 = 0) :
    ptWind x V = wrapTerm x e (V.getLastD a) a := by
  subst hV
  have hform : (a :: L) ++ (a :: L).take 1 = (a :: L) ++ [a] := by simp [List.take]
  rw [ptWind_eq_wrapSum x e, hform, wrapSum_concat x e a L a]
  have hzeroSum : wrapSum x e (a :: L) = 0 := by
    clear hform
    induction L generalizing a with
    | nil => simp
    | cons b L ih =>
        rw [wrapSum_cons_cons]
        have h1 : wrapTerm x e a b = 0 := by
          refine hzero (a, b) ?_
          simp
        have h2 : wrapSum x e (b :: L) = 0 := by
          refine ih b ?_
          intro p hp
          refine hzero p ?_
          simp only [List.drop, List.zip_cons_cons, List.mem_cons] at hp ⊢
          exact Or.inr hp
        rw [h1, h2]; ring
  rw [hzeroSum]
  ring

/-- **Point-in-polygon by a single ray crossing (upward form).**  Fix a frame
`e ≠ 0`, so that the branch cut is the ray from `x` in direction `-e`.  If every
*path* edge of the cycle `a :: L` misses that ray, while the closing edge
`(last, a)` crosses it transversally from the lower to the upper half plane, then

  `ptWind x (a :: L) = -2π`.

In particular `x` is enclosed by the polygon: a single transversal crossing of an
escaping ray already pins the winding number.  This is the elementary,
fully-computable point-in-polygon criterion; combined with `ptWind_rotate`
(`RequestProject.SAWUmlaufPtWindJordan`) the crossing edge may be taken to be any
edge of the cycle. -/
theorem ptWind_of_single_up_crossing (x e : ℂ) (he : e ≠ 0) (a : ℂ) (L : List ℂ)
    (hxv : ∀ v ∈ (a :: L), v ≠ x)
    (hzero : ∀ p ∈ (a :: L).zip L,
        ∀ w ∈ segment ℝ ((p.1 - x) / e) ((p.2 - x) / e), ¬ (w.im = 0 ∧ w.re ≤ 0))
    (hlow : (((a :: L).getLastD a - x) / e).im < 0)
    (hhigh : 0 < ((a - x) / e).im)
    (w : ℂ) (hw : w ∈ segment ℝ (((a :: L).getLastD a - x) / e) ((a - x) / e))
    (hwim : w.im = 0) (hwre : w.re < 0) :
    ptWind x (a :: L) = -(2 * Real.pi) := by
  have hdrop : (a :: L).drop 1 = L := rfl
  have hzeroTerm : ∀ p ∈ (a :: L).zip ((a :: L).drop 1), wrapTerm x e p.1 p.2 = 0 := by
    intro p hp
    rw [hdrop] at hp
    obtain ⟨hp1, hp2⟩ := List.of_mem_zip hp
    exact wrapTerm_eq_zero_of_avoids x e he p.1 p.2 (hxv p.1 hp1)
      (hxv p.2 (List.mem_cons_of_mem a hp2)) (fun z hz hcon => hzero p hp z hz hcon)
  have hlast : ptWind x (a :: L) = wrapTerm x e ((a :: L).getLastD a) a :=
    ptWind_eq_wrapTerm_last x e (a :: L) a L rfl hzeroTerm
  have hmem : (a :: L).getLastD a ∈ (a :: L) := List.mem_of_getLast? rfl
  have hcross : cross (((a :: L).getLastD a - x) / e) ((a - x) / e) < 0 :=
    cross_neg_of_segment_crossing _ _ w hlow hhigh hw hwim hwre
  rw [hlast]
  exact wrapTerm_eq_neg_two_pi_of_up x e _ a he (hxv _ hmem) (hxv a (by simp))
    hlow hhigh hcross

end HexArea

end
