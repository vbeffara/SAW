/-
# Convex-hull containment bricks for the escape-walk residues of the Umlaufsatz

This file collects small, fully general, **`sorry`-free** convex-geometry lemmas
that feed the two remaining *escape-walk* residues of the discrete Hopf
Umlaufsatz in `RequestProject.SAWUmlaufPolygon`:

* `clipped_ear_escape_walk` and `chord_ear_other_escape_walk`

Both residues must exhibit an edge-avoiding polyline from a forbidden point out
past the convex hull of a *sub-polygon* `P` (a chord piece, or an ear-clipped
chord piece).  The natural place to route such a polyline is the exterior of the
*whole* polygon `W`, and the convex hull of any sub-polygon is contained in the
convex hull of `W`.  Hence it suffices to reach a point outside `convexHull W`:
that point is automatically outside `convexHull P`.

The bricks here make this reduction explicit and reusable:

* `not_mem_convexHull_sub` — the fully general monotonicity form: if every vertex
  of `L1` is a vertex of `L2`, then a point outside `convexHull (L2.toFinset)`
  is outside `convexHull (L1.toFinset)`.
* `chordLeft_toFinset_subset` / `chordRight_toFinset_subset` — the vertex sets of
  the two chord pieces are subsets of `W`'s vertex set (both pieces are sublists
  of `W`).
* `convexHull_chordLeft_subset` / `convexHull_chordRight_subset` — the hull of a
  chord piece sits inside the hull of `W`.
* `not_mem_convexHull_chordPiece_of_not_mem` — the packaged consequence used by
  `chord_ear_other_escape_walk`: reaching outside `convexHull W` discharges the
  "outside `convexHull P`" endpoint clause.

**Status.**  All lemmas are proved `sorry`-free.  They are *preparation*
consumed by the two escape-walk residues (still `sorry` in `SAWUmlaufPolygon`,
which imports this file): the escape-walk goals are reformulated to target the
larger hull `convexHull W` via these bricks, isolating the genuine remaining
plane-topology content (routing through the exterior of `W`).  This is **not** a
dead branch.
-/

import Mathlib
import RequestProject.SAWUmlaufEarSplit

open Real Complex

noncomputable section

namespace HexArea

/-- **General hull-monotonicity brick.**  If every vertex of `L1` occurs in `L2`,
    a point outside the convex hull of `L2`'s vertices is outside the convex hull
    of `L1`'s vertices.  Reusable; consumed by both escape-walk residues to
    upgrade a "reach outside `convexHull W`" endpoint to the required "outside
    `convexHull P`" (resp. the ear-clipped sub-polygon). -/
lemma not_mem_convexHull_sub (L1 L2 : List ℂ) (hsub : ∀ y ∈ L1, y ∈ L2) (x : ℂ)
    (hx : x ∉ convexHull ℝ (L2.toFinset : Set ℂ)) :
    x ∉ convexHull ℝ (L1.toFinset : Set ℂ) := by
  intro h
  apply hx
  refine convexHull_mono ?_ h
  intro y hy
  simp only [Finset.mem_coe, List.mem_toFinset] at *
  exact hsub y hy

/-- The left chord piece is a sublist of `V`, so its vertex set is a subset. -/
lemma chordLeft_toFinset_subset (V : List ℂ) (k : ℕ) :
    (chordLeft V k).toFinset ⊆ V.toFinset := by
  intro x hx
  simp only [List.mem_toFinset] at hx ⊢
  exact (List.take_subset _ _) hx

/-- The right chord piece is a concatenation of two sublists of `V`, so its
    vertex set is a subset. -/
lemma chordRight_toFinset_subset (V : List ℂ) (k : ℕ) :
    (chordRight V k).toFinset ⊆ V.toFinset := by
  intro x hx
  simp only [List.mem_toFinset, chordRight, List.mem_append] at hx ⊢
  rcases hx with h | h
  · exact (List.drop_subset _ _) h
  · exact (List.take_subset _ _) h

/-- The convex hull of the left chord piece sits inside the convex hull of `V`. -/
lemma convexHull_chordLeft_subset (V : List ℂ) (k : ℕ) :
    convexHull ℝ ((chordLeft V k).toFinset : Set ℂ)
      ⊆ convexHull ℝ (V.toFinset : Set ℂ) := by
  apply convexHull_mono
  exact_mod_cast Finset.coe_subset.mpr (chordLeft_toFinset_subset V k)

/-- The convex hull of the right chord piece sits inside the convex hull of `V`. -/
lemma convexHull_chordRight_subset (V : List ℂ) (k : ℕ) :
    convexHull ℝ ((chordRight V k).toFinset : Set ℂ)
      ⊆ convexHull ℝ (V.toFinset : Set ℂ) := by
  apply convexHull_mono
  exact_mod_cast Finset.coe_subset.mpr (chordRight_toFinset_subset V k)

/-- **Packaged consequence (escape-walk brick).**  A point outside the convex
    hull of the whole polygon `V` is outside the convex hull of either chord
    piece.  Consumed by `chord_ear_other_escape_walk` to discharge the endpoint
    clause once a point outside `convexHull V` has been reached. -/
lemma not_mem_convexHull_chordPiece_of_not_mem (V : List ℂ) (k : ℕ) (P : List ℂ)
    (hP : P = chordLeft V k ∨ P = chordRight V k) (x : ℂ)
    (hx : x ∉ convexHull ℝ (V.toFinset : Set ℂ)) :
    x ∉ convexHull ℝ (P.toFinset : Set ℂ) := by
  rcases hP with rfl | rfl
  · exact fun h => hx (convexHull_chordLeft_subset V k h)
  · exact fun h => hx (convexHull_chordRight_subset V k h)

end HexArea
