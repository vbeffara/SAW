import Mathlib
import RequestProject.SAWUmlaufPtWindMove
import RequestProject.SAWUmlaufPtWindHalfPlane
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarExtreme

/-!
# Escape from a strictly extreme corner: elementary ingredients

This file supplies the missing *point-in-polygon* input of the chord branch of
the Umlaufsatz (`chord_ear_other_ptWind_zero` in
`RequestProject.SAWUmlaufPolyEscape`), **without** any Jordan-curve machinery.

## The construction

Let `P` be a closed polygon (a list of vertices, read cyclically) and let `u` be
a vertex of `P` which is *strictly extreme*: there is a direction `d` with

```
0 < cdot d (y - u)      for every vertex `y ≠ u` of `P`,
```

i.e. every other vertex lies strictly inside the open half plane on one side of
the line through `u` orthogonal to `d`.  Let `n₁, n₂` be the two neighbours of
`u` in `P`, so that the two cycle edges incident to `u` are contained in the
closed convex cone

```
u + K,      K = { α • (n₁ - u) + β • (n₂ - u) : α, β ≥ 0 }.
```

Finally let `x₀` be a point whose direction from `u` lies **outside** that cone,
and such that the segment `[u, x₀]` meets the polygon only at `u` (in the
application `[u, x₀]` is an edge of the ambient polygon leaving `u` on the other
side of the cut chord).

Then `ptWind x₀ P = 0`: the polygon does not wind around `x₀`.

The proof is completely explicit and elementary — no separation theorem is
needed:

* pick `z` on the segment `(u, x₀]`, so close to `u` that
  `cdot d (z - u) < h`, where `h > 0` is the minimum of `cdot d (y - u)` over
  the vertices `y ≠ u`;
* run the straight ray from `z` in the direction `-g`, where
  `g = (n₁ - u) + (n₂ - u)` points *into* the cone;
* along that ray `cdot d (· - u)` decreases, so the ray never meets a cycle edge
  whose two endpoints are `≠ u` (all points of such an edge have
  `cdot d (· - u) ≥ h`), and it never meets an edge inside `u + K` either — a
  meeting point would exhibit `x₀ - u` as a nonnegative combination of
  `n₁ - u` and `n₂ - u`, contradicting the choice of `x₀`;
* far out on that ray `cdot d (· - u) < 0`, so the whole polygon lies in an open
  half plane as seen from there, and `ptWind = 0` by
  `HexArea.ptWind_eq_zero_of_halfplane`;
* `ptWind` is constant along the ray and along `[z, x₀]`
  (`HexArea.ptWind_eq_of_segment_avoids`), which gives the claim.

The escape theorem itself is `HexArea.ptWind_zero_of_extreme_corner` in
`RequestProject.SAWUmlaufCornerEscape`, which imports this file; that file is in
turn imported by `RequestProject.SAWUmlaufChordCorner` and
`RequestProject.SAWUmlaufPolyEscape`, so both lie on the live route to the main
theorem.
-/

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 1000000

/-- **A two-vertex "polygon" never winds.**  The degenerate cycle `[a, b]`
traverses the segment back and forth, so its winding around any point off the
segment is `0`.  This is the base case of the ear-clipping recursion: clipping
the ear of a triangle leaves exactly such a pair. -/
lemma ptWind_pair_zero (x a b : ℂ) (h : x ∉ segment ℝ a b) : ptWind x [a, b] = 0 := by
  have hslit : (b - x) / (a - x) ∈ Complex.slitPlane := ratio_mem_slitPlane a b x h
  have hargne : Complex.arg ((b - x) / (a - x)) ≠ Real.pi := by
    intro hpi
    rcases hslit with hre | him
    · have hpi' := Complex.arg_eq_pi_iff.mp hpi
      linarith [hpi'.1]
    · exact him (Complex.arg_eq_pi_iff.mp hpi).2
  have harg : Complex.arg ((a - x) / (b - x)) = - Complex.arg ((b - x) / (a - x)) := by
    rw [show (a - x) / (b - x) = ((b - x) / (a - x))⁻¹ by field_simp]
    rw [Complex.arg_inv, if_neg hargne]
  simp [ptWind, ptTurn, harg]

/-- The real pairing `⟪w, d⟫` of two complex numbers regarded as plane vectors. -/
def cdot (d w : ℂ) : ℝ := (w * (starRingEnd ℂ) d).re

@[simp] lemma cdot_zero (d : ℂ) : cdot d 0 = 0 := by simp [cdot]

lemma cdot_add (d w₁ w₂ : ℂ) : cdot d (w₁ + w₂) = cdot d w₁ + cdot d w₂ := by
  simp [cdot, add_mul]

lemma cdot_sub (d w₁ w₂ : ℂ) : cdot d (w₁ - w₂) = cdot d w₁ - cdot d w₂ := by
  simp [cdot, sub_mul]

lemma cdot_smul (d : ℂ) (t : ℝ) (w : ℂ) : cdot d (t • w) = t * cdot d w := by
  simp [cdot, Complex.real_smul]
  ring

/-- The closed convex cone with apex `u` spanned by the two directions
`n₁ - u`, `n₂ - u`. -/
def cornerCone (u n₁ n₂ : ℂ) : Set ℂ :=
  {w : ℂ | ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ w - u = α • (n₁ - u) + β • (n₂ - u)}

lemma mem_cornerCone_self (u n₁ n₂ : ℂ) : u ∈ cornerCone u n₁ n₂ :=
  ⟨0, 0, le_rfl, le_rfl, by simp⟩

lemma mem_cornerCone_left (u n₁ n₂ : ℂ) : n₁ ∈ cornerCone u n₁ n₂ :=
  ⟨1, 0, zero_le_one, le_rfl, by simp⟩

lemma mem_cornerCone_right (u n₁ n₂ : ℂ) : n₂ ∈ cornerCone u n₁ n₂ :=
  ⟨0, 1, le_rfl, zero_le_one, by simp⟩

/-- The corner cone is convex, so it contains the whole edge `[u, n₁]`. -/
lemma segment_subset_cornerCone (u n₁ n₂ : ℂ) (a b : ℂ)
    (ha : a ∈ cornerCone u n₁ n₂) (hb : b ∈ cornerCone u n₁ n₂) :
    segment ℝ a b ⊆ cornerCone u n₁ n₂ := by
  rintro w ⟨s, t, hs, ht, hst, rfl⟩
  obtain ⟨α₁, β₁, hα₁, hβ₁, h₁⟩ := ha
  obtain ⟨α₂, β₂, hα₂, hβ₂, h₂⟩ := hb
  refine ⟨s * α₁ + t * α₂, s * β₁ + t * β₂, by positivity, by positivity, ?_⟩
  have ha' : a = u + (α₁ • (n₁ - u) + β₁ • (n₂ - u)) := by linear_combination (norm := module) h₁
  have hb' : b = u + (α₂ • (n₁ - u) + β₂ • (n₂ - u)) := by linear_combination (norm := module) h₂
  subst ha' hb'
  have hc : (s : ℂ) + t = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hst
  push_cast [Complex.real_smul]
  ring_nf
  linear_combination (norm := ring) (u - n₁ * 0) * hc

/-- Splitting a convex combination around the base point `u`. -/
lemma smul_sub_base (u a b : ℂ) (s t : ℝ) (hst : s + t = 1) :
    s • a + t • b - u = s • (a - u) + t • (b - u) := by
  have hc : (s : ℂ) + t = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hst
  push_cast [Complex.real_smul]
  linear_combination (norm := ring) u * hc

/-- A positive uniform lower bound for a strictly positive quantity over the
(finitely many) vertices of a list. -/
lemma exists_pos_lower_bound (P : List ℂ) (u d : ℂ)
    (hpos : ∀ y ∈ P, y ≠ u → 0 < cdot d (y - u)) :
    ∃ h : ℝ, 0 < h ∧ ∀ y ∈ P, y ≠ u → h ≤ cdot d (y - u) := by
  induction P with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a L ih =>
      obtain ⟨h, hh, hL⟩ := ih (fun y hy hyu => hpos y (List.mem_cons_of_mem _ hy) hyu)
      by_cases hau : a = u
      · refine ⟨h, hh, ?_⟩
        intro y hy hyu
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hau hyu
        · exact hL y hy' hyu
      · refine ⟨min h (cdot d (a - u)), lt_min hh (hpos a (by simp) hau), ?_⟩
        intro y hy hyu
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact min_le_right _ _
        · exact le_trans (min_le_left _ _) (hL y hy' hyu)

/-- Points of a segment both of whose endpoints have `cdot d (· - u) ≥ h`
also satisfy that bound. -/
lemma cdot_ge_of_mem_segment (u d a b : ℂ) (h : ℝ)
    (ha : h ≤ cdot d (a - u)) (hb : h ≤ cdot d (b - u)) :
    ∀ w ∈ segment ℝ a b, h ≤ cdot d (w - u) := by
  rintro w ⟨s, t, hs, ht, hst, rfl⟩
  rw [smul_sub_base u a b s t hst, cdot_add, cdot_smul, cdot_smul]
  have hsum : s * h + t * h = h := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left ha hs, mul_le_mul_of_nonneg_left hb ht]

/-- Both endpoints of a cycle edge are vertices of the list. -/
lemma mem_of_mem_cycleEdges (P : List ℂ) (e : ℂ × ℂ) (he : e ∈ cycleEdges P) :
    e.1 ∈ P ∧ e.2 ∈ P := by
  have hsub : ∀ z ∈ P ++ P.take 1, z ∈ P := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact h
    · exact List.mem_of_mem_take h
  obtain ⟨h1, h2⟩ := List.of_mem_zip he
  exact ⟨hsub _ h1, hsub _ (List.mem_of_mem_drop h2)⟩

/-- The pairing against the tilted direction `1 + ε i`. -/
lemma cdot_dir (ε : ℝ) (w : ℂ) : cdot (1 + ε * Complex.I) w = w.re + ε * w.im := by
  simp [cdot]; ring

/-- Shrinking the tilt `ε` preserves strict lexicographic positivity. -/
lemma lex_mono (v y : ℂ) (h : v.re < y.re ∨ (v.re = y.re ∧ v.im ≤ y.im)) (hyv : y ≠ v)
    (ε ε' : ℝ) (hε' : 0 < ε') (hle : ε' ≤ ε)
    (hpos : 0 < (y.re - v.re) + ε * (y.im - v.im)) :
    0 < (y.re - v.re) + ε' * (y.im - v.im) := by
  rcases h with h | ⟨hre, him⟩
  · by_cases hs : 0 ≤ y.im - v.im
    · nlinarith
    · push_neg at hs; nlinarith
  · have hlt : v.im < y.im := by
      rcases lt_or_eq_of_le him with h' | h'
      · exact h'
      · exact absurd (Complex.ext hre.symm h'.symm) hyv
    rw [hre]
    have : (0:ℝ) < ε' * (y.im - v.im) := by nlinarith
    linarith

/-- **Lex-minimal vertices are strictly extreme.**  If `v` is lexicographically
minimal in `L` (leftmost, ties broken lowest) then a single direction
`d = 1 + ε·i` with `ε > 0` small separates `v` strictly from every other point of
`L`: `0 < cdot d (y - v)` for all `y ∈ L`, `y ≠ v`.

Indeed `cdot (1 + ε i) w = w.re + ε * w.im`; for `y` with `v.re < y.re` this is
positive as soon as `ε` is smaller than `(y.re - v.re) / (1 + |y.im - v.im|)`,
and for `y` with `v.re = y.re` lex-minimality and `y ≠ v` give `v.im < y.im`, so
the value is positive for every `ε > 0`.  Take the minimum of the finitely many
constraints. -/
lemma exists_dir_of_lexMin (L : List ℂ) (v : ℂ)
    (hlex : ∀ w ∈ L, v.re < w.re ∨ (v.re = w.re ∧ v.im ≤ w.im)) :
    ∃ d : ℂ, ∀ y ∈ L, y ≠ v → 0 < cdot d (y - v) := by
  suffices h : ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ L, y ≠ v → 0 < (y.re - v.re) + ε * (y.im - v.im) by
    obtain ⟨ε, hε, hprop⟩ := h
    refine ⟨1 + ε * Complex.I, fun y hy hyv => ?_⟩
    rw [cdot_dir]
    simpa using hprop y hy hyv
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a L ih =>
      obtain ⟨ε, hε, hP⟩ := ih (fun w hw => hlex w (List.mem_cons_of_mem _ hw))
      by_cases hav : a = v
      · refine ⟨ε, hε, ?_⟩
        intro y hy hyv
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hav hyv
        · exact hP y hy' hyv
      · rcases hlex a (by simp) with hre | ⟨hre, him⟩
        · have hden : (0:ℝ) < 1 + |a.im - v.im| := by positivity
          set ε' := min ε ((a.re - v.re) / (1 + |a.im - v.im|)) with hε'def
          have hε'pos : 0 < ε' := lt_min hε (div_pos (by linarith) hden)
          refine ⟨ε', hε'pos, ?_⟩
          intro y hy hyv
          rcases List.mem_cons.mp hy with rfl | hy'
          · by_cases hs : 0 ≤ y.im - v.im
            · nlinarith
            · push_neg at hs
              have h1 : ε' ≤ (y.re - v.re) / (1 + |y.im - v.im|) := min_le_right _ _
              have habs : |y.im - v.im| = -(y.im - v.im) := abs_of_neg hs
              rw [habs] at h1
              have h2 : ε' * (1 + -(y.im - v.im)) ≤ y.re - v.re := by
                rw [le_div_iff₀ (by linarith)] at h1; linarith
              nlinarith
          · exact lex_mono v y (hlex y (List.mem_cons_of_mem _ hy')) hyv ε ε' hε'pos
              (min_le_left _ _) (hP y hy' hyv)
        · refine ⟨ε, hε, ?_⟩
          intro y hy hyv
          rcases List.mem_cons.mp hy with rfl | hy'
          · have hlt : v.im < y.im := by
              rcases lt_or_eq_of_le him with h' | h'
              · exact h'
              · exact absurd (Complex.ext hre.symm h'.symm) hyv
            rw [hre]; nlinarith
          · exact hP y hy' hyv

/-- The corner cone does not depend on the order of its two spanning directions. -/
lemma cornerCone_comm (u n₁ n₂ : ℂ) : cornerCone u n₁ n₂ = cornerCone u n₂ n₁ := by
  ext w
  constructor <;> rintro ⟨α, β, hα, hβ, h⟩ <;> exact ⟨β, α, hβ, hα, by rw [h]; ring⟩

/-- Strict interiority of a triangle is invariant under swapping the two outer
vertices (it flips the orientation, and both orientations are allowed). -/
lemma inTriangleStrict_swap13 (a b c x : ℂ) (h : inTriangleStrict a b c x) :
    inTriangleStrict c b a x := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inr ⟨by simp [cross] at h2 ⊢; linarith, by simp [cross] at h1 ⊢; linarith,
      by simp [cross] at h3 ⊢; linarith⟩
  · exact Or.inl ⟨by simp [cross] at h2 ⊢; linarith, by simp [cross] at h1 ⊢; linarith,
      by simp [cross] at h3 ⊢; linarith⟩

/-- **A strict interior point of the corner triangle pins the neighbour outside
the cut cone.**  If `v` lies strictly inside the triangle `p, u, n`, then
`v - u = α • (p - u) + γ • (n - u)` with `α, γ > 0`, so `p` cannot be written as a
nonnegative combination of `n - u` and `v - u`: `p ∉ cornerCone u n v`.  This is
exactly the hypothesis `hcone` of `ptWind_zero_of_extreme_corner` for the left
chord piece (and, symmetrically, for the right one). -/
lemma not_mem_cornerCone_of_inTriangleStrict (p u n v : ℂ)
    (h : inTriangleStrict p u n v) :
    p ∉ cornerCone u n v := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hv⟩ := inTriangleStrict_convexCombo p u n v h
  have hnd : cross (p - u) (n - u) ≠ 0 := by
    have := inTriangleStrict_nondeg p u n v h
    simpa [cross, Complex.ext_iff] using fun hc => this (by simp [cross] at hc ⊢; linarith)
  rintro ⟨s, t, hs, ht, hp⟩
  have hvu : v - u = α • (p - u) + γ • (n - u) := by
    rw [hv]
    have hb : β = 1 - α - γ := by linarith
    rw [hb]
    push_cast [Complex.real_smul]
    ring
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

/-- The mirror form of `not_mem_cornerCone_of_inTriangleStrict`, used for the
right chord piece: there the two polygon edges at `u` are `u–v` and `u–p`, and
the far neighbour is `n`. -/
lemma not_mem_cornerCone_of_inTriangleStrict' (p u n v : ℂ)
    (h : inTriangleStrict p u n v) :
    n ∉ cornerCone u v p := by
  rw [cornerCone_comm]
  exact not_mem_cornerCone_of_inTriangleStrict n u p v (inTriangleStrict_swap13 p u n v h)

end HexArea

end
