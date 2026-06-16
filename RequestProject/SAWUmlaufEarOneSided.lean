/-
# Ear-existence geometry, part VI: the *one-sided* ear and the clip clauses it feeds

This file continues the plane-geometry preparation begun in
`RequestProject.SAWUmlaufEar` … `RequestProject.SAWUmlaufEarSide` for the single
remaining topological core of the discrete Hopf Umlaufsatz, the two-ears /
ear-existence theorem, isolated in `RequestProject.SAWUmlaufPolygon` as
`exists_front_ear`.

## What a *one-sided* ear is, and why it is the right notion

`exists_front_ear` must produce a cyclic rotation `V.rotate r = a :: b :: c :: rest`
whose middle vertex `b` is an ear *together with* the algebraic
**far-edge same-side** clause

```
∀ e ∈ (c :: rest).zip (rest ++ [a]),
    a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
    0 < cross (c - a) (e.1 - a) * cross (c - a) (e.2 - a)
```

— every *guarded* far edge (one sharing no endpoint with the diagonal `a–c`)
has both endpoints strictly on the **same side** of the line `a–c`.  As a
worked example shows, a *generic* empty convex ear (e.g. the one at the extreme
vertex) does **not** satisfy this: a far edge may cross the *infinite* line
`a–c` outside the segment.  The clause holds exactly for a **one-sided ear** —
one whose diagonal `a–c` has *all* the far vertices `rest` strictly on one side
of the line.  Such an ear always exists (the genuine Meisters / convex-hull
content concentrated in `exists_front_ear`), and it is the satisfiable form the
surrounding bookkeeping consumes.

## Contents (all sorry-free)

* `sameSide_pairwise_of_allPos` / `sameSide_pairwise_of_allNeg` — repackage
  one-sidedness given as "every `rest` vertex has `cross (c-a) (·-a) > 0`"
  (resp. `< 0`) into the symmetric *pairwise-positive-product* form
  `0 < cross (c-a) (x-a) * cross (c-a) (y-a)` consumed below.
* `oneSided_far_edges_sameSide` — the **bridge to the same-side clause**: from
  the pairwise one-sidedness of `rest`, every guarded far edge
  `e ∈ (c :: rest).zip (rest ++ [a])` lands both endpoints in `rest`, hence on
  the same side, giving exactly the far-edge same-side clause of
  `exists_front_ear`.
* `clip_turn_at_a_ne_zero` / `clip_turn_at_c_ne_zero` — the two **new** cyclic
  turns created by clipping `b` (at `a`, between predecessor `p` and `c`; and at
  `c`, between `a` and successor `q`) are non-degenerate, derived purely from the
  one-sidedness facts `cross (c-a) (p-a) ≠ 0`, `cross (c-a) (q-a) ≠ 0` (true for
  `p, q ∈ rest`).  These feed the `polyCycNondeg (a :: c :: rest)` clause of
  `exists_front_ear`.

This file is **preparation**: it is imported by
`RequestProject.SAWUmlaufPolygon` (hence transitively from
`RequestProject.SAWFinal`), so it is part of the build chain.  Its lemmas are
designed to be consumed by the eventual proof of `exists_front_ear`; they are
not yet referenced by another declaration only because the core they feed is
still open.  This is intentional, recorded partial progress, not a dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEar
import RequestProject.SAWUmlaufEarSide

open Complex

noncomputable section

namespace HexArea

/-! ## Repackaging one-sidedness into pairwise positive products -/

/-- If every vertex of `rest` lies strictly on the **positive** side of the line
    `a–c` (`0 < cross (c-a) (x-a)`), then any two of them have strictly positive
    side-test product.  This is the all-positive form of one-sidedness, in the
    symmetric shape consumed by `oneSided_far_edges_sameSide`. -/
lemma sameSide_pairwise_of_allPos (a c : ℂ) (rest : List ℂ)
    (h : ∀ x ∈ rest, 0 < cross (c - a) (x - a)) :
    ∀ x ∈ rest, ∀ y ∈ rest,
      0 < cross (c - a) (x - a) * cross (c - a) (y - a) := by
  intro x hx y hy; exact mul_pos (h x hx) (h y hy)

/-- If every vertex of `rest` lies strictly on the **negative** side of the line
    `a–c` (`cross (c-a) (x-a) < 0`), then any two of them have strictly positive
    side-test product.  This is the all-negative form of one-sidedness. -/
lemma sameSide_pairwise_of_allNeg (a c : ℂ) (rest : List ℂ)
    (h : ∀ x ∈ rest, cross (c - a) (x - a) < 0) :
    ∀ x ∈ rest, ∀ y ∈ rest,
      0 < cross (c - a) (x - a) * cross (c - a) (y - a) := by
  intro x hx y hy; exact mul_pos_of_neg_of_neg (h x hx) (h y hy)

/-! ## The bridge to the far-edge same-side clause of `exists_front_ear` -/

/-- **One-sidedness of `rest` ⟹ the far-edge same-side clause.**  If any two
    vertices of `rest` have strictly positive side-test product against the line
    `a–c` (pairwise one-sidedness, supplied by `sameSide_pairwise_of_allPos` /
    `…AllNeg`), then every *guarded* far edge of the clip — `e` in
    `(c :: rest).zip (rest ++ [a])` sharing no endpoint with the diagonal — has
    both endpoints strictly on the same side of `a–c`.

    Proof: a guarded far edge `e` has `e.1 ∈ c :: rest` with `e.1 ≠ c`, hence
    `e.1 ∈ rest`; and `e.2 ∈ rest ++ [a]` with `e.2 ≠ a`, hence `e.2 ∈ rest`; so
    the hypothesis applies to `x := e.1`, `y := e.2`.

    This is exactly the same-side clause `exists_front_ear` must output (feeding
    `diag_disjoint_of_far_sameSide'` and hence planar-simplicity preservation),
    reduced to the single geometric fact that a *one-sided ear* exists. -/
lemma oneSided_far_edges_sameSide (a c : ℂ) (rest : List ℂ)
    (hside : ∀ x ∈ rest, ∀ y ∈ rest,
       0 < cross (c - a) (x - a) * cross (c - a) (y - a)) :
    ∀ e ∈ (c :: rest).zip (rest ++ [a]),
       a ≠ e.1 → a ≠ e.2 → c ≠ e.1 → c ≠ e.2 →
       0 < cross (c - a) (e.1 - a) * cross (c - a) (e.2 - a) := by
  intro e he _ h2 h3 _
  obtain ⟨he1, he2⟩ := List.of_mem_zip he
  have h1rest : e.1 ∈ rest := by
    rcases List.mem_cons.mp he1 with h | h
    · exact absurd h.symm h3
    · exact h
  have h2rest : e.2 ∈ rest := by
    rcases List.mem_append.mp he2 with h | h
    · exact h
    · simp only [List.mem_singleton] at h; exact absurd h.symm h2
  exact hside e.1 h1rest e.2 h2rest

/-! ## Non-degeneracy of the two new cyclic turns of the clip -/

/-- **The new turn at `a` is non-degenerate.**  Clipping the ear `b` from
    `… p :: a :: b :: c …` creates the new corner `p → a → c`, whose turn cross
    product is `cross (a - p) (c - a)`.  It equals `cross (c - a) (p - a)`, which
    is nonzero because the cyclic predecessor `p` of `a` lies (strictly) off the
    line `a–c` — a consequence of one-sidedness, since `p ∈ rest`.  Feeds the
    `polyCycNondeg (a :: c :: rest)` clause of `exists_front_ear`. -/
lemma clip_turn_at_a_ne_zero (a c p : ℂ) (hp : cross (c - a) (p - a) ≠ 0) :
    cross (a - p) (c - a) ≠ 0 := by
  intro hh; apply hp
  have : cross (a - p) (c - a) = cross (c - a) (p - a) := by
    simp only [cross, Complex.sub_re, Complex.sub_im]; ring
  rw [this] at hh; exact hh

/-- **The new turn at `c` is non-degenerate.**  Clipping the ear `b` from
    `… a :: b :: c :: q …` creates the new corner `a → c → q`, whose turn cross
    product is `cross (c - a) (q - c)`.  It equals `cross (c - a) (q - a)`, which
    is nonzero because the cyclic successor `q` of `c` lies (strictly) off the
    line `a–c` — a consequence of one-sidedness, since `q ∈ rest`.  Feeds the
    `polyCycNondeg (a :: c :: rest)` clause of `exists_front_ear`. -/
lemma clip_turn_at_c_ne_zero (a c q : ℂ) (hq : cross (c - a) (q - a) ≠ 0) :
    cross (c - a) (q - c) ≠ 0 := by
  intro hh; apply hq
  have : cross (c - a) (q - c) = cross (c - a) (q - a) := by
    simp only [cross, Complex.sub_re, Complex.sub_im]; ring
  rw [this] at hh; exact hh

end HexArea

end
