/-
# The flat-clip counterexample: an ear clip of a simple polygon may be *degenerate*

This file is a **soundness audit** of the ear-existence core of the polygon
Umlaufsatz (`exists_empty_corner_avoiding` / `exists_empty_convex_ear` in
`RequestProject.SAWUmlaufPolyMeisters`, and the inductive invariants
`EmptyCornerData` / `EmptyCornerData2` of `RequestProject.SAWUmlaufPolyBase`).

Those statements ask for an *empty convex ear* `a, b, c` of a simple,
cyclically non-degenerate polygon `V` such that, in addition, **both clip
corners survive**:

```
HexArea.cross (a - p) (c - a) ≠ 0   and   HexArea.cross (c - a) (q - c) ≠ 0
```

where `p` is the cyclic predecessor of `a` and `q` the cyclic successor of `c`.
Equivalently: after cutting the ear off, the clipped polygon `a :: c :: rest`
is again cyclically non-degenerate.  **That is false.**

The pentagon

```
  v₀ = 0,  v₁ = i,  v₂ = 1 + i,  v₃ = 2 + 2i,  v₄ = 2 + i
```

is simple and cyclically non-degenerate (`badV_simple`, `badV_nondeg`), yet
**every one** of its five corners fails the ear data:

* `b = v₁`: the clip corner at `c = v₂` is flat — `v₁, v₂, v₃` become
  `0, 1+i, 2+2i` after the clip, which are collinear;
* `b = v₂`: the corner is reflex (its orientation is opposite to the polygon's);
* `b = v₃`: the clip corner at `a = v₂` is flat (`v₁, v₂, v₄` are collinear:
  all have imaginary part `1`);
* `b = v₄`: the clip corner at `a = v₃` is flat (`v₂, v₃, v₀` are collinear:
  all lie on the diagonal line `y = x`);
* `b = v₀`: the clip corner at `c = v₁` is flat (`v₄, v₁, v₂` are collinear,
  imaginary part `1`).

So the pentagon has genuine ears (`v₁`, `v₃` and `v₄` are all *bona fide* ears:
convex, with an empty triangle), but **clipping any of them leaves a flat
vertex** in the remaining quadrilateral.  Hence the "clip corners are non-flat"
clauses cannot be part of a true ear-existence statement, and the ear-clipping
induction must instead be prepared to **delete flat vertices** after a clip
(the toolkit `PolygonSimple_remove_flat_mid`, `cross_pred_corner_remove_flat`,
`cross_succ_corner_remove_flat` in `RequestProject.SAWUmlaufPolyBase`, and the
new flat-removal invariance results in
`RequestProject.SAWUmlaufFlatRemoval`).

Everything in this file is `sorry`-free, and the disproofs are stated exactly in
the shape of the affected declarations:

* `flat_clip_no_ear_data` — the conclusion of `exists_empty_corner_avoiding`
  (with the `b ≠ z` clause dropped, so this is stronger than needed) fails;
* `flat_clip_EmptyCornerData_false`, `flat_clip_EmptyCornerData2_false`;
* `flat_clip_no_empty_convex_ear` — the conclusion of `exists_empty_convex_ear`
  fails.

This file is imported by `RequestProject.SAWFinal`.
-/
import Mathlib
import RequestProject.SAWUmlaufPolyBase

open Real Complex

namespace FlatClipCE

/-- The counterexample pentagon `0, i, 1+i, 2+2i, 2+i`. -/
def badV : List ℂ := [0, Complex.I, 1 + Complex.I, 2 + 2 * Complex.I, 2 + Complex.I]

lemma badV_len : badV.length = 5 := by simp [badV]

/-! ### The pentagon is a simple polygon

Five pairs of non-adjacent edges have to be separated.  Each pair is separated
by the line through one of the two edges: both endpoints of the other edge lie
*strictly* on one side of it, which is exactly the hypothesis of
`HexArea.segment_disjoint_of_strictSameSide`. -/

lemma dis₁ : Disjoint (segment ℝ (0 : ℂ) Complex.I)
    (segment ℝ (1 + Complex.I) (2 + 2 * Complex.I)) := by
  refine HexArea.segment_disjoint_of_strictSameSide 0 Complex.I _ _ ?_
  norm_num [HexArea.cross]

lemma dis₂ : Disjoint (segment ℝ (0 : ℂ) Complex.I)
    (segment ℝ (2 + 2 * Complex.I) (2 + Complex.I)) := by
  refine HexArea.segment_disjoint_of_strictSameSide 0 Complex.I _ _ ?_
  norm_num [HexArea.cross]

lemma dis₃ : Disjoint (segment ℝ (2 + 2 * Complex.I : ℂ) (2 + Complex.I))
    (segment ℝ Complex.I (1 + Complex.I)) := by
  refine HexArea.segment_disjoint_of_strictSameSide (2 + 2 * Complex.I) (2 + Complex.I) _ _ ?_
  norm_num [HexArea.cross]

lemma dis₄ : Disjoint (segment ℝ (2 + Complex.I : ℂ) 0)
    (segment ℝ Complex.I (1 + Complex.I)) := by
  refine HexArea.segment_disjoint_of_strictSameSide (2 + Complex.I) 0 _ _ ?_
  norm_num [HexArea.cross]

lemma dis₅ : Disjoint (segment ℝ (2 + Complex.I : ℂ) 0)
    (segment ℝ (1 + Complex.I) (2 + 2 * Complex.I)) := by
  refine HexArea.segment_disjoint_of_strictSameSide (2 + Complex.I) 0 _ _ ?_
  norm_num [HexArea.cross]

lemma badV_nodup : badV.Nodup := by
  norm_num [badV, Complex.ext_iff]

lemma badV_simple : PolygonSimple badV := by
  refine ⟨badV_nodup, ?_⟩
  intro e1 h1 e2 h2 hne1 hne2 hne3 hne4
  simp [closedEdges, badV] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp_all [Complex.ext_iff] <;>
    first
      | exact dis₁ | exact dis₁.symm
      | exact dis₂ | exact dis₂.symm
      | exact dis₃ | exact dis₃.symm
      | exact dis₄ | exact dis₄.symm
      | exact dis₅ | exact dis₅.symm

lemma badV_nondeg : polyCycNondeg badV := by
  norm_num [polyCycNondeg, polyNondeg, badV, HexArea.cross]

/-! ### No corner of the pentagon carries the ear data -/

/-- **The ear-existence conclusion fails for `badV`.**  This is exactly the
conclusion of `exists_empty_corner_avoiding` (the `b ≠ z` clause dropped, so the
disproof is stronger), and only the two clip-corner clauses and the orientation
clause are used: for four of the five rotations a clip corner is flat, and for
the fifth the corner is reflex. -/
theorem flat_clip_no_ear_data :
    ¬ ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      badV.rotate r = a :: b :: c :: rest ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      HexArea.cross (a - p) (c - a) ≠ 0 ∧ HexArea.cross (c - a) (q - c) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  rintro ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hqc, -, -, horient⟩
  rw [← List.rotate_mod, badV_len] at hrot
  have hr : r % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (r % 5) <;>
    simp [badV, List.rotate_eq_drop_append_take] at hrot <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hrot <;>
    simp at hp hq
  · -- `b = i`: the clip corner at `c = 1 + i` is flat (`0, 1+i, 2+2i` collinear).
    subst hq
    exact hqc (by norm_num [HexArea.cross])
  · -- `b = 1 + i`: the corner is reflex — its orientation is opposite to the
    -- polygon's, so the ear/clip orientation clause fails.
    refine absurd (horient.mp ?_) ?_
    · norm_num [HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross]
    · norm_num [HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross]
  · -- `b = 2 + 2i`: the clip corner at `a = 1 + i` is flat (`i, 1+i, 2+i`).
    subst hp
    exact hpa (by norm_num [HexArea.cross])
  · -- `b = 2 + i`: the clip corner at `a = 2 + 2i` is flat (`1+i, 2+2i, 0`).
    subst hp
    exact hpa (by norm_num [HexArea.cross])
  · -- `b = 0`: the clip corner at `c = i` is flat (`2+i, i, 1+i`).
    subst hq
    exact hqc (by norm_num [HexArea.cross])

/-- **Consequence: the inductive invariant `EmptyCornerData` is false for
`badV`** — for *every* forbidden vertex `z`. -/
theorem flat_clip_EmptyCornerData_false (z : ℂ) : ¬ EmptyCornerData badV z := by
  rintro ⟨r, a, b, c, p, q, rest, hrot, -, hp, hq, hpa, hqc, h1, h2, horient⟩
  exact flat_clip_no_ear_data ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hqc, h1, h2, horient⟩

/-- **Consequence: the two-forbidden inductive invariant `EmptyCornerData2` is
false for `badV`** — for every pair of forbidden vertices, in particular for
every cyclic edge of `badV`. -/
theorem flat_clip_EmptyCornerData2_false (z1 z2 : ℂ) : ¬ EmptyCornerData2 badV z1 z2 := by
  rintro ⟨r, a, b, c, p, q, rest, hrot, -, -, hp, hq, hpa, hqc, h1, h2, horient⟩
  exact flat_clip_no_ear_data ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hqc, h1, h2, horient⟩

/-- **Consequence: the one-ear conclusion `exists_empty_convex_ear` is false for
`badV`.**  Its `polyCycNondeg (a :: c :: rest)` clause packages exactly the two
clip-corner non-flatness conditions (plus the corners internal to `rest`), so the
same five-way case analysis applies. -/
theorem flat_clip_no_empty_convex_ear :
    ¬ ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      badV.rotate r = a :: b :: c :: rest ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  rintro ⟨r, a, b, c, p, q, rest, hrot, hp, hq, -, -, -, -, -, -, -, -, hclip, horient⟩
  rw [← List.rotate_mod, badV_len] at hrot
  have hr : r % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (r % 5) <;>
    simp [badV, List.rotate_eq_drop_append_take] at hrot <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hrot
  · exact absurd hclip (by norm_num [polyCycNondeg, polyNondeg, HexArea.cross])
  · refine absurd (horient.mp ?_) ?_
    · norm_num [HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross]
    · norm_num [HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross]
  · exact absurd hclip (by norm_num [polyCycNondeg, polyNondeg, HexArea.cross])
  · exact absurd hclip (by norm_num [polyCycNondeg, polyNondeg, HexArea.cross])
  · exact absurd hclip (by norm_num [polyCycNondeg, polyNondeg, HexArea.cross])

end FlatClipCE
