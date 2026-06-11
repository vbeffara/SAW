/-
# Signed area (shoelace) infrastructure for hex-lattice polygons

This file develops the elementary, fully-proved theory of the *signed area*
(shoelace functional) of a closed polygon, as a foundation for the signed-area
route to the discrete Hopf Umlaufsatz `umlaufsatz_pm_one`
(in `RequestProject.SAWTurningNumber`).

The plan of the signed-area route to the Umlaufsatz is:

  * the total turning of a simple closed polygon equals `2π · sign(A)`, where
    `A` is the signed area; and
  * a simple polygon has `A ≠ 0`,

so the turning number is `±1`.  This file establishes the *algebraic* half of
that program: the shoelace functional, its antisymmetry under reversal, its
translation invariance, and its behaviour under inserting/removing a vertex
(the "ear" step).  The genuinely topological half (sign of `A` = turning
number, and `A ≠ 0` for simple polygons) is left to future work; it is the
same irreducible content as the Jordan curve theorem for polygons.

All declarations live in the `HexArea` namespace to avoid clashes with
Mathlib.

This file is imported from `RequestProject.SAWFinal` so that it is part of the
build; it is **preparation** for the Umlaufsatz and is not yet consumed by
another declaration.
-/

import Mathlib

open Complex

noncomputable section

namespace HexArea

/-- Twice the signed area of the triangle `0, z, w`; equivalently the 2-D cross
    product `z.re * w.im - z.im * w.re = Im (conj z * w)`. -/
def cross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

@[simp] lemma cross_eq_zero_self (z : ℂ) : cross z z = 0 := by
  simp [cross]; ring

lemma cross_antisymm (z w : ℂ) : cross z w = - cross w z := by
  simp [cross]; ring

lemma cross_add_left (a b w : ℂ) : cross (a + b) w = cross a w + cross b w := by
  simp [cross]; ring

lemma cross_add_right (a w v : ℂ) : cross a (w + v) = cross a w + cross a v := by
  simp [cross]; ring

/-- The shoelace sum over the *open* polygonal chain `L`: the sum of `cross`
    over consecutive pairs, without the wrap-around edge. -/
def shoelaceOpen : List ℂ → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => cross a b + shoelaceOpen (b :: rest)

@[simp] lemma shoelaceOpen_nil : shoelaceOpen [] = 0 := rfl
@[simp] lemma shoelaceOpen_singleton (a : ℂ) : shoelaceOpen [a] = 0 := rfl
@[simp] lemma shoelaceOpen_cons_cons (a b : ℂ) (rest : List ℂ) :
    shoelaceOpen (a :: b :: rest) = cross a b + shoelaceOpen (b :: rest) := rfl

/-- Twice the signed area of the *closed* polygon with vertex list `L`.
    The wrap-around edge from the last vertex back to the first is included. -/
def shoelace2 (L : List ℂ) : ℝ :=
  shoelaceOpen L + cross (L.getLastD 0) L.headI

@[simp] lemma shoelace2_nil : shoelace2 [] = 0 := by simp [shoelace2, cross]
@[simp] lemma shoelace2_singleton (a : ℂ) : shoelace2 [a] = 0 := by
  simp [shoelace2]

/-- For a triangle, the signed area is the sum of the three edge cross-terms. -/
lemma shoelace2_triple (a b c : ℂ) :
    shoelace2 [a, b, c] = cross a b + cross b c + cross c a := by
  simp [shoelace2, shoelaceOpen]

/-
Reversing the vertex order negates the signed area.
-/
lemma shoelace2_reverse (L : List ℂ) : shoelace2 L.reverse = - shoelace2 L := by
  induction' L with a L ih ; simp_all +decide [ shoelace2 ];
  · unfold cross; norm_num;
  · induction' L using List.reverseRecOn with b L ih <;> simp_all +decide [ shoelace2 ];
    cases b <;> simp_all +decide [ List.getLast? ];
    · unfold cross; ring;
    · -- By definition of `shoelaceOpen`, we can expand both sides.
      have h_expand : ∀ (L : List ℂ) (a b : ℂ), shoelaceOpen (L ++ [a, b]) = shoelaceOpen (L ++ [a]) + cross a b := by
        intros L a b; induction' L with c L ih <;> simp_all +decide [ shoelaceOpen ] ;
        cases L <;> simp_all +decide [ shoelaceOpen ] ; ring;
      grind +suggestions

/-
**Ear step.** Removing a single vertex `b` lying between its neighbours `a`
    and `c` changes the signed area by exactly twice the area of the cut-off
    triangle `a, b, c`.  This is the algebraic backbone of the ear-clipping
    induction toward the Umlaufsatz: the wrap-around edge `cross (last) a` is the
    same for both polygons (they share the same last vertex), and the open chain
    changes by `cross a b + cross b c - cross a c = cross a b + cross b c +
    cross c a`.
-/
lemma shoelace2_ear (a b c : ℂ) (rest : List ℂ) :
    shoelace2 (a :: b :: c :: rest) =
      shoelace2 (a :: c :: rest) + (cross a b + cross b c + cross c a) := by
  unfold shoelace2;
  simp +arith +decide [ shoelaceOpen_cons_cons ];
  unfold cross; ring;

/-
The signed area is invariant under translating every vertex by a constant.
-/
lemma shoelace2_map_add_const (L : List ℂ) (c : ℂ) :
    shoelace2 (L.map (· + c)) = shoelace2 L := by
  unfold shoelace2;
  rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> simp_all +decide [ List.getLastD ];
  induction L generalizing x y <;> simp_all +decide [ cross, List.getLast ] ; ring;
  grind

end HexArea

end