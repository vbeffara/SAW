/-
# Half-plane vanishing of the point-winding (`ptWind`)

This file proves the elementary — but genuinely useful — vanishing criterion
for the point-winding number `ptWind` of a closed polygon: **if all vertices of
`P` lie in an open half-plane whose defining line does *not* contain the base
point `x`, then `ptWind x P = 0`.**

Concretely, the half-plane is encoded by a fixed complex "test direction" `d`
via the condition `0 < ((v - x) * d).re` for every vertex `v ∈ P` (equivalently
`⟨v - x, conj d⟩ > 0`, i.e. every position vector `v - x` has strictly positive
inner product with a fixed normal direction).  Under this hypothesis every
sweep-ratio `(w - x)/(z - x)` is a quotient of two numbers lying in a common
open half-plane through the origin, so its principal argument telescopes
*exactly* (no `2π` wrap), and the closed sum collapses to `0`.

## Why this is not a dead branch

This is the missing tool for the "outside ⟹ winding `0`" point-in-polygon
direction (`chord_ear_other_ptWind_zero` in `RequestProject.SAWUmlaufPolygon`):
a valid diagonal cut of a simple polygon separates the two chord pieces by the
diagonal line, so a vertex `x` of the *other* piece lies strictly on one side of
that line while every vertex of the piece `P` lies in the closed opposite
half-plane — hence in the *open* half-plane relative to `x`.  Feeding the
diagonal normal as `d` gives `ptWind x P = 0` directly.

The file is imported by `RequestProject.SAWUmlaufPolygon`.
-/

import Mathlib
import RequestProject.SAWUmlaufPtWind
import RequestProject.SAWUmlaufPtWindJordan

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 4000000

/-
**Exact argument subtraction in the right half-plane.**  For two complex
    numbers with strictly positive real part, the principal argument of the
    quotient is the difference of the principal arguments (no `2π` wrap), because
    each argument lies in `(-π/2, π/2)` (`Complex.abs_arg_lt_pi_div_two_iff`), so
    their difference lies in `(-π, π)`.
-/
lemma arg_div_of_pos_re (A B : ℂ) (hA : 0 < A.re) (hB : 0 < B.re) :
    Complex.arg (A / B) = Complex.arg A - Complex.arg B := by
  by_contra h_neq;
  -- Since $A$ and $B$ have positive real parts, their arguments lie in $(-\frac{\pi}{2}, \frac{\pi}{2})$.
  have h_arg_bounds : -Real.pi / 2 < A.arg ∧ A.arg < Real.pi / 2 ∧ -Real.pi / 2 < B.arg ∧ B.arg < Real.pi / 2 := by
    simp_all +decide [ neg_div, Complex.arg_lt_pi_div_two_iff, Complex.neg_pi_div_two_lt_arg_iff ];
  have h_arg_div : Complex.arg (A / B) = Complex.arg A - Complex.arg B := by
    have h_arg_div_coe : ((Complex.arg (A / B) : ℝ) : Real.Angle) = (Complex.arg A : Real.Angle) - (Complex.arg B : Real.Angle) := by
      convert Complex.arg_div_coe_angle ( show A ≠ 0 from by rintro rfl; norm_num at hA ) ( show B ≠ 0 from by rintro rfl; norm_num at hB ) using 1
    erw [ Real.Angle.angle_eq_iff_two_pi_dvd_sub ] at h_arg_div_coe;
    obtain ⟨ k, hk ⟩ := h_arg_div_coe; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, Complex.neg_pi_lt_arg ( A / B ), Complex.arg_le_pi ( A / B ) ] ;
  contradiction

/-
**Exact argument subtraction for a common test direction `d`.**  If `z * d`
    and `w * d` both have positive real part, then the sweep argument
    `arg (w / z)` equals `arg (w * d) - arg (z * d)`.  (The factor `d` cancels in
    the quotient; `arg_div_of_pos_re` supplies the wrap-free subtraction.)
-/
lemma arg_div_of_halfplane (z w d : ℂ) (hz : 0 < (z * d).re) (hw : 0 < (w * d).re) :
    Complex.arg (w / z) = Complex.arg (w * d) - Complex.arg (z * d) := by
  convert arg_div_of_pos_re ( w * d ) ( z * d ) hw hz using 1;
  rw [ mul_div_mul_right _ _ ( by aesop_cat ) ]

/-
**Telescoping of `ptTurn` in a half-plane.**  For an open chain `a :: L` all
    of whose vertices lie in the open half-plane `0 < ((v - x) * d).re`, the
    sweep-angle sum telescopes exactly to the endpoint difference
    `arg ((last - x) * d) - arg ((a - x) * d)`.  Proved by induction on `L`
    using `arg_div_of_halfplane` on each consecutive pair.
-/
lemma ptTurn_halfplane (x d : ℂ) :
    ∀ (a : ℂ) (L : List ℂ), (∀ v ∈ (a :: L), 0 < ((v - x) * d).re) →
      ptTurn x (a :: L)
        = Complex.arg (((a :: L).getLastD a - x) * d) - Complex.arg ((a - x) * d) := by
  intro a L hL; induction' L with b L ih generalizing a <;> simp_all +decide [ ptTurn_cons_cons ] ;
  convert congr_arg₂ ( · + · ) ( arg_div_of_halfplane ( a - x ) ( b - x ) d ( by simpa using hL.1 ) ( by simpa using hL.2.1 ) ) rfl using 1;
  grind

/-
**Half-plane vanishing of the point-winding.**  If every vertex of the
    closed polygon `P` lies in the open half-plane `0 < ((v - x) * d).re`
    (i.e. `x` lies strictly outside the closed half-plane containing `P`), then
    the winding number of `P` around `x` is `0`.  This is the "outside ⟹ winding
    `0`" separation tool: the closed sweep sum telescopes to
    `arg ((a - x) * d) - arg ((a - x) * d) = 0`.
-/
lemma ptWind_eq_zero_of_halfplane (x d : ℂ) (P : List ℂ)
    (h : ∀ v ∈ P, 0 < ((v - x) * d).re) :
    ptWind x P = 0 := by
  induction' P with a P ih;
  · rfl;
  · convert ptTurn_halfplane x d a ( P ++ [ a ] ) _ using 1;
    · simp +decide [ List.getLastD ];
    · grind

end HexArea

end