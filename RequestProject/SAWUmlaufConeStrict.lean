import Mathlib
import RequestProject.SAWUmlaufCornerEscapeAux

/-!
# `SAWUmlaufConeStrict` — strict interiority of the *corner cone*

The chord machinery of the Umlaufsatz (`RequestProject.SAWUmlaufChordCorner` and
everything downstream of it) roots a diagonal `u–v` at a strictly extreme vertex
`u` with cyclic neighbours `pu`, `nu`, and records the validity of the diagonal
by the predicate `InteriorChord`, whose geometric clause used to be
`HexArea.inTriangleStrict pu u nu v`: the far endpoint lies strictly inside the
*corner triangle*.

That clause is stronger than anything the machinery uses.  Every consumer only
ever needs `v` to lie strictly inside the *corner cone* at `u`, i.e.

    v - u = α • (pu - u) + γ • (nu - u)   with   α, γ > 0,

together with the non-degeneracy `cross (pu - u) (nu - u) ≠ 0` of the corner.
This file introduces that weaker predicate, `HexArea.inConeStrict`, and proves

* `inConeStrict_of_inTriangleStrict` — the strict triangle is inside the strict
  cone, so nothing that used the old clause is lost;
* `inConeStrict_of_mem_openSegment` — the case the *blocked-base* branch of the
  Meisters recursion needs: a point of the open base segment `(pu, nu)` is
  strictly inside the cone even though it is **not** strictly inside the
  triangle;
* `cone_cross_ne`, `inConeStrict_swap13`, `not_mem_cornerCone_of_inConeStrict`
  and its mirror — the three consequences the chord machinery consumes.

The whole file is `sorry`-free.  NOT a dead branch: `InteriorChord`
(`RequestProject.SAWUmlaufChordCorner`) is stated with `inConeStrict`.
-/

open Real Complex

noncomputable section

namespace HexArea

/-- **`v` lies strictly inside the corner cone at `u` spanned by `p` and `n`.**
The corner itself is non-degenerate and `v - u` is a *strictly* positive
combination of the two edge directions. -/
def inConeStrict (p u n v : ℂ) : Prop :=
  cross (p - u) (n - u) ≠ 0 ∧
    ∃ α γ : ℝ, 0 < α ∧ 0 < γ ∧ v - u = α • (p - u) + γ • (n - u)

/-- A point strictly inside the corner triangle is strictly inside the corner
cone. -/
lemma inConeStrict_of_inTriangleStrict (p u n v : ℂ)
    (h : inTriangleStrict p u n v) : inConeStrict p u n v := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hv⟩ := inTriangleStrict_convexCombo p u n v h
  refine ⟨?_, α, γ, hα, hγ, ?_⟩
  · have hnd := inTriangleStrict_nondeg p u n v h
    simpa [cross, Complex.ext_iff] using
      fun hc => hnd (by simp [cross] at hc ⊢; linarith)
  · rw [hv]
    have hb : β = 1 - α - γ := by linarith
    rw [hb]
    push_cast [Complex.real_smul]
    ring

/-- **The case the blocked-base branch needs.**  A point of the *open* segment
`(p, n)` — the base of the corner triangle — lies strictly inside the corner
cone, although it is never strictly inside the triangle. -/
lemma inConeStrict_of_mem_openSegment (p u n v : ℂ)
    (hnd : cross (p - u) (n - u) ≠ 0) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv : v = p + (s : ℂ) * (n - p)) : inConeStrict p u n v := by
  refine ⟨hnd, 1 - s, s, by linarith, hs0, ?_⟩
  rw [hv]
  push_cast [Complex.real_smul]
  ring

/-- The three corner cross products of a strict cone point are non-zero. -/
lemma cone_cross_ne (p u n v : ℂ) (h : inConeStrict p u n v) :
    cross (p - u) (n - u) ≠ 0 ∧ cross (p - u) (v - u) ≠ 0 ∧
      cross (n - u) (v - u) ≠ 0 := by
  obtain ⟨hpn, α, γ, hα, hγ, hvu⟩ := h
  refine ⟨hpn, ?_, ?_⟩
  · have hc : cross (p - u) (v - u) = γ * cross (p - u) (n - u) := by
      rw [hvu]; simp [cross, Complex.real_smul]; ring
    rw [hc]
    exact mul_ne_zero (ne_of_gt hγ) hpn
  · have hc : cross (n - u) (v - u) = -(α * cross (p - u) (n - u)) := by
      rw [hvu]; simp [cross, Complex.real_smul]; ring
    rw [hc]
    exact neg_ne_zero.mpr (mul_ne_zero (ne_of_gt hα) hpn)

/-- Strict interiority of the corner cone is invariant under swapping the two
spanning directions. -/
lemma inConeStrict_swap13 (p u n v : ℂ) (h : inConeStrict p u n v) :
    inConeStrict n u p v := by
  obtain ⟨hpn, α, γ, hα, hγ, hvu⟩ := h
  refine ⟨?_, γ, α, hγ, hα, by rw [hvu]; ring⟩
  intro hc
  exact hpn (by simp only [cross] at hc ⊢; linarith)

/-- **A strict cone point pins the neighbour outside the cut cone.**  If `v` is
strictly inside the cone at `u` spanned by `p` and `n`, then `p` is not a
nonnegative combination of `n - u` and `v - u`: `p ∉ cornerCone u n v`.  This is
the hypothesis `hcone` of `ptWind_zero_of_extreme_corner` for the left chord
piece. -/
lemma not_mem_cornerCone_of_inConeStrict (p u n v : ℂ)
    (h : inConeStrict p u n v) : p ∉ cornerCone u n v := by
  obtain ⟨hnd, α, γ, hα, hγ, hvu⟩ := h
  rintro ⟨s, t, hs, ht, hp⟩
  rw [hvu] at hp
  set A := p - u with hA
  set B := n - u with hB
  have hX : (1 - t * α) • A = (s + t * γ) • B := by
    push_cast [Complex.real_smul] at hp ⊢
    linear_combination hp
  have hcross : (1 - t * α) * cross A B = 0 := by
    have h1 := congrArg (fun z => cross z B) hX
    simp [cross, Complex.real_smul] at h1
    simp only [cross]
    linear_combination h1
  have ht1 : t * α = 1 := by
    rcases mul_eq_zero.mp hcross with h1 | h2
    · linarith
    · exact absurd h2 hnd
  have hY : (s + t * γ) • B = 0 := by rw [← hX, ht1]; simp
  have hBne : B ≠ 0 := by
    intro h0; apply hnd; simp [cross, h0]
  have hzero : s + t * γ = 0 := by
    rcases smul_eq_zero.mp hY with h1 | h2
    · exact h1
    · exact absurd h2 hBne
  have htpos : 0 < t := by nlinarith
  nlinarith

/-- The mirror form of `not_mem_cornerCone_of_inConeStrict`, used for the right
chord piece: there the two polygon edges at `u` are `u–v` and `u–p`, and the far
neighbour is `n`. -/
lemma not_mem_cornerCone_of_inConeStrict' (p u n v : ℂ)
    (h : inConeStrict p u n v) : n ∉ cornerCone u v p := by
  rw [cornerCone_comm]
  exact not_mem_cornerCone_of_inConeStrict n u p v (inConeStrict_swap13 p u n v h)

/-- A strict cone point is distinct from the first spanning vertex. -/
lemma inConeStrict_ne_left (p u n v : ℂ) (h : inConeStrict p u n v) : v ≠ p := by
  intro hvp
  refine (cone_cross_ne p u n v h).2.1 ?_
  rw [hvp]; simp only [cross]; ring

/-- A strict cone point is distinct from the second spanning vertex. -/
lemma inConeStrict_ne_right (p u n v : ℂ) (h : inConeStrict p u n v) : v ≠ n := by
  intro hvn
  refine (cone_cross_ne p u n v h).2.2 ?_
  rw [hvn]; simp only [cross]; ring

/-- **Corner signs at a strict cone chord endpoint (pure algebra).**  The cone
relaxation of `HexArea.corner_signs_of_inTriangleStrict`: if `v` lies strictly
inside the corner cone at `u` spanned by `pu` and `nu`, then the two corners the
chord `u–v` creates at `u` — `pu → u → v` and `v → u → nu` — turn the same way as
the polygon corner `pu → u → nu`, and neither of them is flat.

Both sub-corner cross products are *positive multiples* of the corner cross
product: writing `v - u = α • (pu - u) + γ • (nu - u)` with `α, γ > 0`, one has
`cross (pu - u) (v - u) = γ * cross (pu - u) (nu - u)` and
`cross (v - u) (nu - u) = α * cross (pu - u) (nu - u)`. -/
lemma corner_signs_of_inConeStrict (pu u nu v : ℂ) (h : inConeStrict pu u nu v) :
    (((0:ℝ) < cross (u - pu) (v - u)) ↔ ((0:ℝ) < cross (u - pu) (nu - u))) ∧
    (((0:ℝ) < cross (u - v) (nu - u)) ↔ ((0:ℝ) < cross (u - pu) (nu - u))) ∧
    cross (v - u) (nu - u) ≠ 0 ∧ cross (pu - u) (v - u) ≠ 0 := by
  obtain ⟨hpn, α, γ, hα, hγ, hvu⟩ := h
  have hA : cross (pu - u) (v - u) = γ * cross (pu - u) (nu - u) := by
    rw [hvu]; simp [cross, Complex.real_smul]; ring
  have hB : cross (v - u) (nu - u) = α * cross (pu - u) (nu - u) := by
    rw [hvu]; simp [cross, Complex.real_smul]; ring
  have e1 : cross (u - pu) (v - u) = - cross (pu - u) (v - u) := by
    simp [cross]; ring
  have e2 : cross (u - v) (nu - u) = - cross (v - u) (nu - u) := by
    simp [cross]; ring
  have e3 : cross (u - pu) (nu - u) = - cross (pu - u) (nu - u) := by
    simp [cross]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, hA, e3]
    constructor <;> intro h <;> nlinarith
  · rw [e2, hB, e3]
    constructor <;> intro h <;> nlinarith
  · rw [hB]; exact mul_ne_zero (ne_of_gt hα) hpn
  · rw [hA]; exact mul_ne_zero (ne_of_gt hγ) hpn

end HexArea

end
