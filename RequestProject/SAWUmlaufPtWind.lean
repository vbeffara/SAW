/-
# Winding number of a closed polygon around a point (`ptWind`)

This file develops the **winding number of a closed polygon around a base
point** `x`, the missing piece of plane topology needed to discharge the single
irreducible Jordan-separation gap `chord_ear_empty_other` of the discrete Hopf
Umlaufsatz (`RequestProject.SAWUmlaufPolygon`).

Where `polyWind` (in `SAWUmlaufPolygon`) sums the *exterior turning* angles
`arg ((pᵢ₊₁ - pᵢ) / (pᵢ - pᵢ₋₁))` of the edge *directions*, the winding number
`ptWind x V` sums the *sweep* angles `arg ((pᵢ₊₁ - x) / (pᵢ - x))` of the
*position vectors from `x`*.  For a simple polygon this is the classical
point-in-polygon / winding-number function: it is `2π·sign(area)` for points in
the interior and `0` for points in the exterior, and it is exactly the tool that
separates the two chord pieces of a valid diagonal cut.

## Contents

* `ptTurn`, `ptWind` — definitions.
* `ptWind_triangle_expand` — the closed triangle winding as a three-`arg` sum
  (definitional unfolding).
* `cross_pos_vec` — the position-vector cross product `cross (a-x) (b-x)` equals
  the edge cross product `cross (b-a) (x-a)` (so `inTriangleStrict a b c x`
  is exactly the statement that all three position-vector sweeps are co-signed).
* `ptWind_triangle` — **the winding number of a triangle around an interior
  point is `2π·sign(area)`** (the exact analogue of `polyWind_triangle`).
* `ptWind_triangle_ne_zero` — corollary: nonzero for interior points.

## Downstream use (NOT a dead branch)

This file is imported by `RequestProject.SAWUmlaufPolygon`.  The point-winding
machinery here is the intended foundation for the Jordan-separation keystone
`chord_ear_empty_other`: an empty convex ear triangle of one chord piece `P`
contains a point `x` only if `ptWind x P ≠ 0` (via `ptWind_triangle` plus ear
containment), whereas a vertex of the *other* chord piece has `ptWind x P = 0`
(via the valid-diagonal separation), a contradiction.  The base-case triangle
identity `ptWind_triangle` and the ear-clip additivity `ptWind_ear_clip` are
proved here (sorry-free).  The remaining genuinely plane-topological fact — the
locally-constant / integer-valued behaviour of the winding number of a *simple*
polygon (point-in-polygon), which pins the winding of a piece around a vertex of
the other piece to `0` — is the target of future rounds.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarConvex

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 4000000

/-- Turning of the open chain `L` as seen from the base point `x`: the sum over
    consecutive pairs `(cur, next)` of the sweep angle `arg ((next-x)/(cur-x))`
    of the position vectors from `x`. -/
def ptTurn (x : ℂ) : List ℂ → ℝ
  | a :: b :: rest => Complex.arg ((b - x) / (a - x)) + ptTurn x (b :: rest)
  | _ => 0

/-- Winding number (× `2π`) of the closed polygon with vertex cycle `V` around
    the point `x`.  The cycle is closed by appending the first vertex. -/
def ptWind (x : ℂ) (V : List ℂ) : ℝ := ptTurn x (V ++ V.take 1)

@[simp] lemma ptTurn_nil (x : ℂ) : ptTurn x [] = 0 := rfl
@[simp] lemma ptTurn_singleton (x a : ℂ) : ptTurn x [a] = 0 := rfl

lemma ptTurn_cons_cons (x a b : ℂ) (rest : List ℂ) :
    ptTurn x (a :: b :: rest)
      = Complex.arg ((b - x) / (a - x)) + ptTurn x (b :: rest) := rfl

/-- The position-vector cross product `cross (a-x) (b-x)` equals the edge cross
    product `cross (b-a) (x-a)`.  In particular the sign of the imaginary part of
    `(b-x)/(a-x)` (i.e. the sweep direction of the segment `a → b` as seen from
    `x`) is the sign of `cross (b-a) (x-a)`, so `inTriangleStrict a b c x` is
    precisely the statement that the three position-vector sweeps
    `cross (a-x)(b-x)`, `cross (b-x)(c-x)`, `cross (c-x)(a-x)` are co-signed. -/
lemma cross_pos_vec (a b x : ℂ) : cross (a - x) (b - x) = cross (b - a) (x - a) := by
  simp only [cross, Complex.sub_re, Complex.sub_im]; ring

/-- The closed triangle winding number as a sum of three sweep angles
    (definitional unfolding of `ptWind` on `[a,b,c]`). -/
lemma ptWind_triangle_expand (a b c x : ℂ) :
    ptWind x [a, b, c]
      = Complex.arg ((b - x) / (a - x)) + Complex.arg ((c - x) / (b - x))
        + Complex.arg ((a - x) / (c - x)) := by
  simp only [ptWind, List.take, List.append_assoc, List.cons_append, List.nil_append,
    ptTurn_cons_cons, ptTurn_singleton, ptTurn_nil]
  ring

/-
**Winding number of a triangle around an interior point.**  If `x` lies in
    the strict interior of the triangle `a, b, c`, then the winding number
    (× `2π`) of the closed triangle around `x` equals `2π · sign(signed area)`.

    This is the exact analogue of `polyWind_triangle` (the exterior-turning
    triangle base case), but for the *point-winding* function: the three sweep
    ratios `(b-x)/(a-x)`, `(c-x)/(b-x)`, `(a-x)/(c-x)` have product `1`, so their
    `arg`s sum to a multiple of `2π`; and since `x` is strictly interior, all
    three position-vector cross products `cross (a-x)(b-x)`, `cross (b-x)(c-x)`,
    `cross (c-x)(a-x)` (= the three `inTriangleStrict` cross products, by
    `cross_pos_vec`) share the sign of the area, forcing each `arg` strictly into
    `(0,π)` or `(-π,0)`; the sum then lies in `(0,3π)` resp. `(-3π,0)` and is a
    multiple of `2π`, hence `±2π`.
-/
lemma ptWind_triangle (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    ptWind x [a, b, c]
      = 2 * Real.pi * (if 0 < shoelace2 [a, b, c] then 1 else -1) := by
  obtain h₁ | h₁ := h <;> simp_all +decide [ inTriangleStrict ];
  · -- Since $x$ is strictly inside the triangle, the arguments of the complex numbers $(b-x)/(a-x)$, $(c-x)/(b-x)$, and $(a-x)/(c-x)$ are all positive and less than $\pi$.
    have h_arg_pos : 0 < Complex.arg ((b - x) / (a - x)) ∧ Complex.arg ((b - x) / (a - x)) < Real.pi ∧ 0 < Complex.arg ((c - x) / (b - x)) ∧ Complex.arg ((c - x) / (b - x)) < Real.pi ∧ 0 < Complex.arg ((a - x) / (c - x)) ∧ Complex.arg ((a - x) / (c - x)) < Real.pi := by
      have h_im_pos : 0 < Complex.im ((b - x) / (a - x)) ∧ 0 < Complex.im ((c - x) / (b - x)) ∧ 0 < Complex.im ((a - x) / (c - x)) := by
        simp_all +decide [ Complex.div_im, cross ];
        exact ⟨ by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr <| sub_ne_zero.mpr <| by aesop_cat ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr <| sub_ne_zero.mpr <| by aesop_cat ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr <| sub_ne_zero.mpr <| by aesop_cat ) ] ; linarith ⟩;
      have h_arg_pos : ∀ z : ℂ, 0 < z.im → 0 < Complex.arg z ∧ Complex.arg z < Real.pi := by
        intro z hz; rw [ Complex.arg ] ;
        split_ifs <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        · exact ⟨ by nlinarith, lt_of_le_of_lt ( Real.arcsin_le_pi_div_two _ ) ( by linarith [ Real.pi_pos ] ) ⟩;
        · exact ⟨ by linarith [ Real.neg_pi_div_two_le_arcsin ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.arcsin_le_pi_div_two ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.pi_pos ], div_neg_of_neg_of_pos ( neg_neg_of_pos hz ) ( Real.sqrt_pos.mpr ( by nlinarith ) ) ⟩;
        · linarith;
      exact ⟨ h_arg_pos _ h_im_pos.1 |>.1, h_arg_pos _ h_im_pos.1 |>.2, h_arg_pos _ h_im_pos.2.1 |>.1, h_arg_pos _ h_im_pos.2.1 |>.2, h_arg_pos _ h_im_pos.2.2 |>.1, h_arg_pos _ h_im_pos.2.2 |>.2 ⟩;
    -- Since the product of the three ratios is 1, the sum of their arguments is an integer multiple of $2\pi$.
    have h_sum_arg : ∃ k : ℤ, Complex.arg ((b - x) / (a - x)) + Complex.arg ((c - x) / (b - x)) + Complex.arg ((a - x) / (c - x)) = k * 2 * Real.pi := by
      have h_sum_arg : Complex.exp (Complex.I * (Complex.arg ((b - x) / (a - x)) + Complex.arg ((c - x) / (b - x)) + Complex.arg ((a - x) / (c - x)))) = 1 := by
        have h_exp : Complex.exp (Complex.I * Complex.arg ((b - x) / (a - x))) = ((b - x) / (a - x)) / ‖(b - x) / (a - x)‖ ∧ Complex.exp (Complex.I * Complex.arg ((c - x) / (b - x))) = ((c - x) / (b - x)) / ‖(c - x) / (b - x)‖ ∧ Complex.exp (Complex.I * Complex.arg ((a - x) / (c - x))) = ((a - x) / (c - x)) / ‖(a - x) / (c - x)‖ := by
          have h_exp : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.I * Complex.arg z) = z / ‖z‖ := by
            intro z hz; rw [ mul_comm ] ; rw [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring_nf; norm_num [ hz ] ;
            conv_rhs => rw [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring;
            norm_num [ mul_comm, Complex.norm_exp, hz ];
          exact ⟨ h_exp _ ( by aesop_cat ), h_exp _ ( by aesop_cat ), h_exp _ ( by aesop_cat ) ⟩;
        simp_all +decide [ mul_add, Complex.exp_add ];
        simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, sub_ne_zero.mpr ( show a ≠ x from by rintro rfl; norm_num [ cross ] at h₁ ), sub_ne_zero.mpr ( show b ≠ x from by rintro rfl; norm_num [ cross ] at h₁ ), sub_ne_zero.mpr ( show c ≠ x from by rintro rfl; norm_num [ cross ] at h₁ ) ];
      rw [ Complex.exp_eq_one_iff ] at h_sum_arg; obtain ⟨ k, hk ⟩ := h_sum_arg; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
    obtain ⟨ k, hk ⟩ := h_sum_arg; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> try nlinarith;
    rw [ if_pos ];
    · rw [ ← hk, ptWind_triangle_expand ];
    · exact cross_edges_eq_shoelace2_triple a b c ▸ inTriangleStrict_pos_area a b c x h₁.1 h₁.2.1 h₁.2.2;
  · -- Since $x$ is in the strict interior of the triangle $abc$, we have $x \neq a$, $x \neq b$, and $x \neq c$.
    have h_ne_a : x ≠ a := by
      aesop
    have h_ne_b : x ≠ b := by
      rintro rfl; norm_num [ cross ] at h₁
    have h_ne_c : x ≠ c := by
      rintro rfl; norm_num [ cross ] at h₁;
    simp_all +decide [ Complex.arg ];
    -- Since $x$ is in the strict interior of the triangle $abc$, we have $arg((b - x) / (a - x)) \in (-π, 0)$, $arg((c - x) / (b - x)) \in (-π, 0)$, and $arg((a - x) / (c - x)) \in (-π, 0)$.
    have h_arg_neg : Complex.arg ((b - x) / (a - x)) < 0 ∧ Complex.arg ((c - x) / (b - x)) < 0 ∧ Complex.arg ((a - x) / (c - x)) < 0 := by
      simp_all +decide [ Complex.div_im, cross ];
      exact ⟨ by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr ( sub_ne_zero.mpr <| by tauto ) ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr ( sub_ne_zero.mpr <| by tauto ) ) ] ; linarith, by rw [ div_lt_div_iff_of_pos_right ( normSq_pos.mpr ( sub_ne_zero.mpr <| by tauto ) ) ] ; linarith ⟩;
    -- Since the arguments are negative, their sum is also negative.
    have h_sum_neg : Complex.arg ((b - x) / (a - x)) + Complex.arg ((c - x) / (b - x)) + Complex.arg ((a - x) / (c - x)) = -2 * Real.pi := by
      have h_sum_neg : Complex.exp (Complex.I * (Complex.arg ((b - x) / (a - x)) + Complex.arg ((c - x) / (b - x)) + Complex.arg ((a - x) / (c - x)))) = 1 := by
        have h_sum_mul : Complex.exp (Complex.I * Complex.arg ((b - x) / (a - x))) * Complex.exp (Complex.I * Complex.arg ((c - x) / (b - x))) * Complex.exp (Complex.I * Complex.arg ((a - x) / (c - x))) = 1 := by
          have h_sum_mul : Complex.exp (Complex.I * Complex.arg ((b - x) / (a - x))) = ((b - x) / (a - x)) / ‖(b - x) / (a - x)‖ ∧ Complex.exp (Complex.I * Complex.arg ((c - x) / (b - x))) = ((c - x) / (b - x)) / ‖(c - x) / (b - x)‖ ∧ Complex.exp (Complex.I * Complex.arg ((a - x) / (c - x))) = ((a - x) / (c - x)) / ‖(a - x) / (c - x)‖ := by
            have h_sum_mul : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.I * Complex.arg z) = z / ‖z‖ := by
              intro z hz; rw [ mul_comm ] ; rw [ Complex.ext_iff ] ; simp +decide [ Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin, hz ] ;
              rw [ Complex.cos_arg, Complex.sin_arg ] <;> aesop;
            exact ⟨ h_sum_mul _ ( div_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ), h_sum_mul _ ( div_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ), h_sum_mul _ ( div_ne_zero ( sub_ne_zero_of_ne <| by tauto ) ( sub_ne_zero_of_ne <| by tauto ) ) ⟩;
          simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
          simp +decide [ mul_assoc, mul_left_comm ( a - x ), mul_left_comm ( b - x ), mul_left_comm ( c - x ), sub_ne_zero.mpr ( Ne.symm h_ne_a ), sub_ne_zero.mpr ( Ne.symm h_ne_b ), sub_ne_zero.mpr ( Ne.symm h_ne_c ) ];
        convert h_sum_mul using 1 ; push_cast [ ← Complex.exp_add ] ; ring;
      rw [ Complex.exp_eq_one_iff ] at h_sum_neg;
      obtain ⟨ n, hn ⟩ := h_sum_neg; norm_num [ Complex.ext_iff ] at hn; rcases n with ( ⟨ _ | _ | n ⟩ | ⟨ _ | _ | n ⟩ ) <;> norm_num at hn <;> nlinarith [ Real.pi_pos, Complex.neg_pi_lt_arg ( ( b - x ) / ( a - x ) ), Complex.arg_le_pi ( ( b - x ) / ( a - x ) ), Complex.neg_pi_lt_arg ( ( c - x ) / ( b - x ) ), Complex.arg_le_pi ( ( c - x ) / ( b - x ) ), Complex.neg_pi_lt_arg ( ( a - x ) / ( c - x ) ), Complex.arg_le_pi ( ( a - x ) / ( c - x ) ) ] ;
    rw [ if_neg ];
    · rw [ ptWind_triangle_expand ] ; linarith;
    · unfold shoelace2; simp +decide [ *, List.foldl ] ;
      unfold cross at *; norm_num [ Complex.ext_iff ] at *; linarith;

/-- The winding number of a triangle around a strict interior point is nonzero. -/
lemma ptWind_triangle_ne_zero (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    ptWind x [a, b, c] ≠ 0 := by
  rw [ptWind_triangle a b c x h]
  have hpi := Real.pi_pos
  split_ifs <;> nlinarith

/-
**Winding number of a triangle around an exterior point is `0`.**  If the
    three `inTriangleStrict` cross products `A = cross (b-a)(x-a)`,
    `B = cross (c-b)(x-b)`, `C = cross (a-c)(x-c)` are all nonzero (i.e. `x` is
    off all three edge lines) but are *not* all of the same sign (i.e. `x` is not
    in the strict interior — the two `inTriangleStrict` disjuncts fail), then the
    winding number of the closed triangle around `x` is `0`.

    Companion of `ptWind_triangle`: with all sweeps nonzero each `arg` lies
    strictly in `(-π,0) ∪ (0,π)`; mixed signs force the (multiple-of-`2π`) sum
    into `(-2π, 2π)`, hence it is `0`.  Together the two lemmas give the full
    point-winding of a triangle: `2π·sign` inside, `0` outside.
-/
lemma ptWind_triangle_exterior (a b c x : ℂ)
    (hA : cross (b - a) (x - a) ≠ 0) (hB : cross (c - b) (x - b) ≠ 0)
    (hC : cross (a - c) (x - c) ≠ 0)
    (hpos : ¬ (0 < cross (b - a) (x - a) ∧ 0 < cross (c - b) (x - b)
        ∧ 0 < cross (a - c) (x - c)))
    (hneg : ¬ (cross (b - a) (x - a) < 0 ∧ cross (c - b) (x - b) < 0
        ∧ cross (a - c) (x - c) < 0)) :
    ptWind x [a, b, c] = 0 := by
  have h_nonzero : a - x ≠ 0 ∧ b - x ≠ 0 ∧ c - x ≠ 0 := by
    refine' ⟨ _, _, _ ⟩ <;> intro h <;> simp_all +decide [ sub_eq_iff_eq_add ];
  -- By `ptWind_triangle_expand`, `ptWind x [a,b,c] = arg r1 + arg r2 + arg r3` where `r1 = (b-x)/(a-x)`, `r2 = (c-x)/(b-x)`, `r3 = (a-x)/(c-x)`.
  set r1 := (b - x) / (a - x)
  set r2 := (c - x) / (b - x)
  set r3 := (a - x) / (c - x)
  have h_sum : ptWind x [a, b, c] = Complex.arg r1 + Complex.arg r2 + Complex.arg r3 := by
    convert ptWind_triangle_expand a b c x using 1;
  -- Since $r1 * r2 * r3 = 1$, we have $\exp(i(\arg r1 + \arg r2 + \arg r3)) = 1$, so $\arg r1 + \arg r2 + \arg r3 = k * 2\pi$ for some integer $k$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Complex.arg r1 + Complex.arg r2 + Complex.arg r3 = k * 2 * Real.pi := by
    have h_exp : Complex.exp (Complex.I * (Complex.arg r1 + Complex.arg r2 + Complex.arg r3)) = 1 := by
      have h_exp : Complex.exp (Complex.I * Complex.arg r1) * Complex.exp (Complex.I * Complex.arg r2) * Complex.exp (Complex.I * Complex.arg r3) = r1 * r2 * r3 := by
        conv_rhs => rw [ ← Complex.norm_mul_exp_arg_mul_I r1, ← Complex.norm_mul_exp_arg_mul_I r2, ← Complex.norm_mul_exp_arg_mul_I r3 ] ; ring;
        simp +zetaDelta at *;
        simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, h_nonzero ];
      simp_all +decide [ mul_div_mul_comm, Complex.exp_add, mul_add ];
      grind;
    rw [ Complex.exp_eq_one_iff ] at h_exp; obtain ⟨ k, hk ⟩ := h_exp; exact ⟨ k, by norm_num [ Complex.ext_iff ] at hk; linarith ⟩ ;
  -- Since $A, B, C$ are not all positive and not all negative, at least one of the arguments $\arg r1, \arg r2, \arg r3$ is positive and at least one is negative.
  have h_arg_signs : (0 < Complex.arg r1 ∨ 0 < Complex.arg r2 ∨ 0 < Complex.arg r3) ∧ (Complex.arg r1 < 0 ∨ Complex.arg r2 < 0 ∨ Complex.arg r3 < 0) := by
    have h_arg_signs : (0 < Complex.im r1 ∨ 0 < Complex.im r2 ∨ 0 < Complex.im r3) ∧ (Complex.im r1 < 0 ∨ Complex.im r2 < 0 ∨ Complex.im r3 < 0) := by
      have h_arg_signs : Complex.im r1 = cross (a - x) (b - x) / Complex.normSq (a - x) ∧ Complex.im r2 = cross (b - x) (c - x) / Complex.normSq (b - x) ∧ Complex.im r3 = cross (c - x) (a - x) / Complex.normSq (c - x) := by
        simp +zetaDelta at *;
        simp +decide [ Complex.div_im, cross ];
        exact ⟨ by ring, by ring, by ring ⟩;
      simp_all +decide [ div_neg_iff, neg_div, cross_pos_vec ];
      grind +suggestions;
    have h_arg_signs : ∀ z : ℂ, z ≠ 0 → (0 < Complex.im z → 0 < Complex.arg z) ∧ (Complex.im z < 0 → Complex.arg z < 0) := by
      intros z hz_nonzero
      constructor;
      · rw [ Complex.arg ];
        split_ifs <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        · exact fun h => by nlinarith;
        · exact fun _ => by linarith [ Real.neg_pi_div_two_le_arcsin ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.arcsin_le_pi_div_two ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ), Real.pi_pos ] ;
        · grind +qlia;
      · rw [ Complex.arg ];
        split_ifs <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        · exact fun h => div_neg_of_neg_of_pos h ( Real.sqrt_pos.mpr ( by nlinarith [ Complex.normSq_apply z, Complex.sq_norm z, show 0 < Complex.normSq z from Complex.normSq_pos.mpr hz_nonzero ] ) );
        · linarith [ Real.pi_pos, Real.arcsin_le_pi_div_two ( -z.im / Real.sqrt ( z.re * z.re + z.im * z.im ) ) ];
    grind;
  rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at hk <;> try nlinarith [ Real.pi_pos, Complex.neg_pi_lt_arg r1, Complex.arg_le_pi r1, Complex.neg_pi_lt_arg r2, Complex.arg_le_pi r2, Complex.neg_pi_lt_arg r3, Complex.arg_le_pi r3 ] ;
  · rcases h_arg_signs.1 with h|h|h <;> rcases h_arg_signs.2 with j|j|j <;> linarith [ Real.pi_pos, Complex.neg_pi_lt_arg r1, Complex.arg_le_pi r1, Complex.neg_pi_lt_arg r2, Complex.arg_le_pi r2, Complex.neg_pi_lt_arg r3, Complex.arg_le_pi r3 ];
  · rcases h_arg_signs.1 with h|h|h <;> rcases h_arg_signs.2 with j|j|j <;> nlinarith [ Real.pi_pos, Complex.neg_pi_lt_arg r1, Complex.arg_le_pi r1, Complex.neg_pi_lt_arg r2, Complex.arg_le_pi r2, Complex.neg_pi_lt_arg r3, Complex.arg_le_pi r3 ]

/-! ## Ear-clip additivity and the remaining point-in-polygon target

`ptWind_ear_clip` below (proved) is the additivity step that carries the
triangle base case `ptWind_triangle` across an ear clip.  The remaining
plane-topological content needed to turn `ptWind` into the point-in-polygon
separator that discharges `chord_ear_empty_other` — the point-in-polygon /
Jordan behaviour of the winding number of a *simple* polygon — is recorded as a
comment target at the end of the file for future rounds. -/

/-
**Ear-clip additivity of the winding number.**  Removing the middle vertex
    `b` of a consecutive triple `a, b, c` from a closed polygon changes the
    winding number about `x` by exactly the winding number of the ear triangle
    `a, b, c` about `x`, provided `x` does not lie on the merged diagonal segment
    `[a, c]`.  Algebraically both closed turnings telescope, and the whole
    difference collapses to `arg ((c-x)/(a-x)) + arg ((a-x)/(c-x))`, which
    vanishes exactly when `(c-x)/(a-x)` is not a negative real, i.e. when `x` is
    not strictly between `a` and `c` (guaranteed by `hac : x ∉ segment ℝ a c`).
    This is the additivity that carries `ptWind_triangle` across the
    ear-clipping induction.

    Note the hypothesis `hac` is essential: if `x` lies strictly between `a` and
    `c` then `(c-x)/(a-x)` is a negative real, both `arg`s equal `π`, and the
    identity fails by `2π`.
-/
lemma ptWind_ear_clip (a b c x : ℂ) (rest : List ℂ)
    (hac : x ∉ segment ℝ a c) :
    ptWind x (a :: b :: c :: rest)
      = ptWind x (a :: c :: rest) + ptWind x [a, b, c] := by
  simp +decide only [ptWind];
  simp +decide [ ptTurn_cons_cons, List.take ];
  rw [ show ( a - x ) / ( c - x ) = ( ( c - x ) / ( a - x ) ) ⁻¹ by rw [ inv_div ], Complex.arg_inv ];
  split_ifs <;> simp_all +decide [ Complex.arg_eq_pi_iff ];
  · -- Since $(c - x) / (a - x)$ is a negative real number, we have $x = t • a + (1 - t) • c$ for some $t \in (0, 1)$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = t • a + (1 - t) • c := by
      -- Since $(c - x) / (a - x)$ is a negative real number, we have $c - x = r • (a - x)$ for some $r < 0$.
      obtain ⟨r, hr⟩ : ∃ r : ℝ, r < 0 ∧ c - x = r • (a - x) := by
        have h_neg_real : ∃ r : ℝ, r < 0 ∧ (c - x) / (a - x) = r := by
          exact ⟨ ( ( c - x ) / ( a - x ) |> Complex.re ), by tauto, by simpa [ Complex.ext_iff, ‹_› ] ⟩;
        by_cases ha : a = x <;> simp_all +decide [ div_eq_iff, sub_eq_iff_eq_add ];
      refine' ⟨ -r / ( 1 - r ), _, _, _ ⟩ <;> try nlinarith [ mul_div_cancel₀ ( -r ) ( by linarith : ( 1 - r ) ≠ 0 ) ];
      simp_all +decide [ sub_eq_iff_eq_add, Complex.ext_iff ];
      norm_cast; norm_num [ show ( 1 - r ) ≠ 0 by linarith ] ; ring_nf;
      grind;
    contrapose! hac;
    rw [ segment_eq_image ];
    exact ⟨ 1 - t, ⟨ by linarith, by linarith ⟩, by simp [ ht.2.2 ] ⟩;
  · ring

/-
**Point-in-polygon via the winding number (Jordan for polygons).**  For a
    simple polygon `V` (non-self-intersecting, `polyCycNondeg` corners) and a
    point `x` not lying on any edge of `V`, the winding number `ptWind x V` is
    `2π·sign(area)` when `x` is enclosed and `0` when it is not.  Phrased in the
    form actually consumed by the Jordan separation: if `x` is a vertex of `V`
    (hence on the boundary of the region) that does *not* lie strictly inside the
    ear triangle region of any single ear, ... — the precise consumable form is
    deferred; recorded here as the target of future rounds.
-/

end HexArea

end