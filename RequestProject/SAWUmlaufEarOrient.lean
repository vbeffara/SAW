import Mathlib
import RequestProject.SAWUmlaufJordanStep
import RequestProject.SAWUmlaufExtremeOrient

/-!
# `SAWUmlaufEarOrient` — the ear at a strictly extreme tip is coherently oriented

The Meisters ear data (`EmptyCornerData2`, `RequestProject.SAWUmlaufPolyBase`)
carries an *orientation* clause: the ear triangle `[a, b, c]` and the clip
`a :: c :: rest` must have the same sign of `shoelace2`.  In the empty branch of
the Meisters search the tip `b` is the lexicographically minimal vertex, hence a
*strictly extreme* vertex of the polygon, and this file shows that in that
situation the orientation clause is **automatic**:

* `HexArea.not_mem_convexHull_of_extreme` — a point strictly on one side of an
  open half plane containing a set is outside the convex hull of that set;
* `clip_orient_below` — the coherence of the ear with its clip, given the
  keystone (the ear region is outside the clip) and the dichotomy for shorter
  polygons; a direct consequence of `clip_orient_of_keystone`
  (`RequestProject.SAWUmlaufJordanStep`);
* `clip_orient_of_extreme_tip` — the coherence at a strictly extreme tip, with
  no orientation input at all: the tip is outside the convex hull of the clip's
  vertices, so the keystone holds by
  `ear_interior_clip_ptWind_zero_of_tip_not_hull`.

NOT a dead branch: `clip_orient_of_extreme_tip` is consumed by
`meisters_reduction_empty2` (`RequestProject.SAWUmlaufPolyMeisters`), where it
removes the orientation clause from the empty branch's case split.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

namespace HexArea

/-- **A point strictly on one side of a set is outside its convex hull.**  If
every point `v` of `S` satisfies `0 < cdot d (v - b)` then `b ∉ convexHull ℝ S`:
the open half plane is convex, contains `S`, and misses `b`. -/
lemma not_mem_convexHull_of_extreme (d b : ℂ) (S : Set ℂ)
    (hS : ∀ v ∈ S, 0 < cdot d (v - b)) : b ∉ convexHull ℝ S := by
  intro hb
  have hconv : Convex ℝ {z : ℂ | 0 < cdot d (z - b)} := by
    intro z hz w hw t1 t2 ht1 ht2 ht
    simp only [Set.mem_setOf_eq] at hz hw ⊢
    have key : t1 • (z - b) + t2 • (w - b) = t1 • z + t2 • w - (t1 + t2) • b := by
      rw [add_smul, smul_sub, smul_sub]; abel
    rw [ht, one_smul] at key
    rw [← key, cdot_add, cdot_smul, cdot_smul]
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · have ht2' : 0 < t2 := by rw [← h1] at ht; linarith
      rw [← h1]
      have := mul_pos ht2' hw
      linarith
    · have h2 := mul_pos h1 hz
      have h3 : 0 ≤ t2 * cdot d (w - b) := mul_nonneg ht2 (le_of_lt hw)
      linarith
  have hmem : 0 < cdot d (b - b) := convexHull_min hS hconv hb
  rw [sub_self, cdot_zero] at hmem
  exact lt_irrefl 0 hmem

end HexArea

/-- **Coherent ear orientation from the keystone, relative to the dichotomy for
shorter polygons.**  The `DichBelow`-relative packaging of
`clip_orient_of_keystone`: the clip is a simple polygon with one vertex fewer, so
the dichotomy for it is available from `DichBelow N` as soon as the polygon
itself has at most `N` vertices. -/
theorem clip_orient_below (N : ℕ) (hN : DichBelow N) (a b c : ℂ) (rest : List ℂ)
    (hlen : rest.length + 3 ≤ N) (hrest : rest ≠ [])
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hkey : ∀ x : ℂ, HexArea.inTriangleStrict a b c x →
        HexArea.ptWind x (a :: c :: rest) = 0) :
    (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: c :: rest)) := by
  have hrpos : 0 < rest.length := List.length_pos_iff.mpr hrest
  have h4 : 4 ≤ (a :: b :: c :: rest).length := by simp; omega
  have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
  have hca : c - a ≠ 0 := by
    refine sub_ne_zero.mpr (fun h => ?_)
    exact (List.nodup_cons.mp hnd).1 (by simp [← h])
  have hCs : PolygonSimple (a :: c :: rest) :=
    PolygonSimple_clip a b c rest hsimple
      (diag_disjoint_of_empty_corner a b c rest hsimple hD hca hempty hdiag)
  have hdich : PolyDichotomy (a :: c :: rest) :=
    hN (a :: c :: rest) (by simp; omega) (by simp; omega) hCs
  exact clip_orient_of_keystone a b c rest h4 hsimple hD hempty hdiag hdich hkey

/-- **The ear at a strictly extreme tip is coherently oriented with its clip
(no orientation input).**

Let `a :: b :: c :: rest` be a simple polygon with a non-degenerate corner at `b`
whose corner triangle contains no vertex of `rest`, either strictly (`hempty`) or
on the closed base (`hdiag`), and let the tip `b` be *strictly extreme*: all other
vertices lie in the open half plane `cdot d (· - b) > 0`.  Then the ear triangle
and the clip carry the same orientation.

This is exactly the orientation clause of `EmptyCornerData2`, and it is what
makes that clause free in the empty branch of the Meisters search, where the tip
is the lexicographically minimal vertex.

Proof: the strict extremality puts `b` outside the convex hull of the clip's
vertices, hence the clip does not wind around the ear region
(`ear_interior_clip_ptWind_zero_of_tip_not_hull`); `clip_orient_below` then reads
the orientation off the winding jump across the base. -/
theorem clip_orient_of_extreme_tip (N : ℕ) (hN : DichBelow N) (a b c : ℂ) (rest : List ℂ)
    (hlen : rest.length + 3 ≤ N) (hrest : rest ≠ [])
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (d : ℂ)
    (hdir : ∀ y ∈ (a :: b :: c :: rest), y ≠ b → 0 < HexArea.cdot d (y - b)) :
    (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: c :: rest)) := by
  have hrpos : 0 < rest.length := List.length_pos_iff.mpr hrest
  have h4 : 4 ≤ (a :: b :: c :: rest).length := by simp; omega
  have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
  -- the tip is not a vertex of the clip
  have hbnot : b ∉ (a :: c :: rest) := by
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact (List.nodup_cons.mp hnd).1 (by simp)
    · exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hmem'
  -- the tip is outside the convex hull of the clip
  have hhull : b ∉ convexHull ℝ (((a :: c :: rest).toFinset : Finset ℂ) : Set ℂ) := by
    refine HexArea.not_mem_convexHull_of_extreme d b _ ?_
    intro v hv
    have hvl : v ∈ (a :: c :: rest) := by simpa using hv
    have hvb : v ≠ b := by intro h; exact hbnot (h ▸ hvl)
    refine hdir v ?_ hvb
    rcases List.mem_cons.mp hvl with rfl | hv'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv')
  -- hence the clip does not wind around the ear region
  have hkey : ∀ x : ℂ, HexArea.inTriangleStrict a b c x →
      HexArea.ptWind x (a :: c :: rest) = 0 := by
    intro x hin
    exact ear_interior_clip_ptWind_zero_of_tip_not_hull (a :: b :: c :: rest) h4 hsimple 0
      a b c rest (by simp) hD hempty hdiag hhull x hin
  exact clip_orient_below N hN a b c rest hlen hrest hsimple hD hempty hdiag hkey

end
