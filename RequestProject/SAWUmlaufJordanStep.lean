import Mathlib
import RequestProject.SAWUmlaufJordanDichotomy
import RequestProject.SAWUmlaufEarTipEscape
import RequestProject.SAWUmlaufTriangleClosed

/-!
# `SAWUmlaufJordanStep` — the ear induction step for the point-in-polygon dichotomy

The single remaining plane-topology input of the polygonal Umlaufsatz is the
point-in-polygon dichotomy `polygon_ptWind_dichotomy`
(`RequestProject.SAWUmlaufJordanDichotomy`).  Its classical proof is an induction
on the number of vertices along an *ear clip*: if `a :: b :: c :: rest` is a
rotation of the simple polygon `V` exhibiting an empty, coherently oriented ear at
the tip `b`, then the clip `C = a :: c :: rest` is a simple polygon with one
vertex less, and

  `ptWind x V = ptWind x C + ptWind x [a, b, c]`   (`HexArea.ptWind_ear_clip`)

for every `x` off the base `[a, c]`.  This file proves, **sorry-free**, both
halves of the induction step:

* `keystone_of_dichotomy_clip` — the dichotomy for the clip `C` implies the
  *keystone* for `V`: the ear region is outside `C`, i.e. `ptWind x C = 0` for `x`
  strictly inside the ear triangle.  The proof crosses the ear **base** `[a, c]`
  (an edge of `C`, but not of `V`): the winding of `C` jumps by `2π` there
  (`HexArea.ptWind_jump_edge`) whereas the winding of `V` does not change, and the
  ear triangle contributes `2π·sign` on the inner side and `0` on the outer one.
  The dichotomy for `C` turns this into a two-case computation, and the wrong case
  is excluded by the coherence `0 < shoelace2 [a,b,c] ↔ 0 < shoelace2 C`.
* `dichotomy_of_keystone_clip` — conversely, the dichotomy for `C` together with
  the keystone for `V` gives the dichotomy for `V`: a point strictly inside the ear
  triangle gets `2π·sign` from the triangle and `0` from the clip; any other point
  gets `0` from the triangle and the clip's value, whose sign is again that of `V`.

Together: `dichotomy(C) ⟹ dichotomy(V)` for a polygon with an empty coherently
oriented ear, which is precisely the induction step.  What is still missing in
order to close the induction is ear *existence* at each vertex count: the
Meisters chain (`SAWUmlaufPolyBase → … → SAWUmlaufPolyMeisters`) proves it, but
its proof consumes the keystone for the strictly shorter chord pieces, so the
loop can only be closed by restating that chain relative to a "keystone holds
below `n`" hypothesis.  That refactor is the next task recorded in
`PROOF_STATUS.md`.

NOT a dead branch: the two theorems below are the mathematical content of the
induction that discharges `polygon_ptWind_dichotomy`, the last topological gap of
the Umlaufsatz.  The file is imported by `RequestProject.SAWUmlaufSignedArea`, so
it is built as part of the live chain.

## Reusable bricks proved here

* `HexArea.hull_halfplane` — a closed half-plane containing a set contains its
  convex hull (in the *scaled* form used throughout the ear development);
* `HexArea.ptWind_triple_zero_of_neg_scaled` — a point with a negative scaled
  barycentric coordinate is outside the triangle, so the triangle does not wind
  around it;
* `HexArea.ptWind_triple_zero_or_strict` — a point off the three closed sides of a
  non-degenerate triangle is either strictly inside it or has winding `0`;
* `HexArea.inTriangleStrict_cyc` — cyclic invariance of the strict interior.
-/

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 1000000

/-! ## 1. Triangle bricks -/

/-- Cyclic invariance of the strict interior of a triangle. -/
lemma inTriangleStrict_cyc (a b c x : ℂ) :
    inTriangleStrict c a b x ↔ inTriangleStrict a b c x := by
  simp only [inTriangleStrict]
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> [left; right; left; right] <;>
    exact ⟨by assumption, by assumption, by assumption⟩

/-- The three "cyclic" evaluations of the doubled area. -/
lemma cross_area_a (a b c : ℂ) : cross (b - a) (c - a) = cross (b - a) (c - b) := by
  simp only [cross, Complex.sub_re, Complex.sub_im]; ring

lemma cross_area_b (a b c : ℂ) : cross (c - b) (a - b) = cross (b - a) (c - b) := by
  simp only [cross, Complex.sub_re, Complex.sub_im]; ring

lemma cross_area_c (a b c : ℂ) : cross (a - c) (b - c) = cross (b - a) (c - b) := by
  simp only [cross, Complex.sub_re, Complex.sub_im]; ring

/-- The cross product of a vector with itself vanishes. -/
lemma cross_self (u : ℂ) : cross u u = 0 := by
  simp only [cross]; ring

/-- **A scaled half-plane containing a set contains its convex hull.** -/
lemma hull_halfplane (u p : ℂ) (k : ℝ) (S : Set ℂ)
    (hS : ∀ v ∈ S, 0 ≤ cross u (v - p) * k)
    (x : ℂ) (hx : x ∈ convexHull ℝ S) : 0 ≤ cross u (x - p) * k := by
  have hconv : Convex ℝ {z : ℂ | 0 ≤ cross u (z - p) * k} := by
    intro z hz w hw t1 t2 ht1 ht2 ht
    simp only [Set.mem_setOf_eq] at hz hw ⊢
    have hrw : t1 • z + t2 • w = (1 - t2) • z + t2 • w := by
      rw [show t1 = 1 - t2 by linarith]
    rw [hrw, cross_affine]
    nlinarith
  exact convexHull_min hS hconv hx

/-- **A point with a negative scaled barycentric coordinate is outside the
triangle**, so the triangle does not wind around it. -/
lemma ptWind_triple_zero_of_neg_scaled (a b c x : ℂ)
    (h : cross (b - a) (x - a) * cross (b - a) (c - b) < 0 ∨
         cross (c - b) (x - b) * cross (b - a) (c - b) < 0 ∨
         cross (a - c) (x - c) * cross (b - a) (c - b) < 0) :
    ptWind x [a, b, c] = 0 := by
  set D : ℝ := cross (b - a) (c - b) with hD
  refine ptWind_zero_of_not_mem_convexHull x [a, b, c] ?_
  have hset : (([a, b, c] : List ℂ).toFinset : Set ℂ) = {a, b, c} := by
    ext w; simp
  rw [hset]
  intro hx
  rcases h with h | h | h
  · have := hull_halfplane (b - a) a D {a, b, c} ?_ x hx
    · linarith
    · intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · simp [cross]
      · rw [cross_self]; simp
      · rw [cross_area_a a b c]; nlinarith [sq_nonneg D]
  · have := hull_halfplane (c - b) b D {a, b, c} ?_ x hx
    · linarith
    · intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · rw [cross_area_b a b c]; nlinarith [sq_nonneg D]
      · simp [cross]
      · rw [cross_self]; simp
  · have := hull_halfplane (a - c) c D {a, b, c} ?_ x hx
    · linarith
    · intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv | hv <;> rw [hv]
      · rw [cross_self]; simp
      · rw [cross_area_c a b c]; nlinarith [sq_nonneg D]
      · simp [cross]

/-- **A point off the three closed sides of a non-degenerate triangle is either
strictly inside it, or the triangle does not wind around it.** -/
lemma ptWind_triple_zero_or_strict (a b c x : ℂ) (hD : cross (b - a) (c - b) ≠ 0)
    (hab : x ∉ segment ℝ a b) (hbc : x ∉ segment ℝ b c) (hac : x ∉ segment ℝ a c) :
    inTriangleStrict a b c x ∨ ptWind x [a, b, c] = 0 := by
  set D : ℝ := cross (b - a) (c - b) with hDdef
  by_cases h1 : cross (b - a) (x - a) * D < 0
  · exact Or.inr (ptWind_triple_zero_of_neg_scaled a b c x (Or.inl h1))
  by_cases h2 : cross (c - b) (x - b) * D < 0
  · exact Or.inr (ptWind_triple_zero_of_neg_scaled a b c x (Or.inr (Or.inl h2)))
  by_cases h3 : cross (a - c) (x - c) * D < 0
  · exact Or.inr (ptWind_triple_zero_of_neg_scaled a b c x (Or.inr (Or.inr h3)))
  push_neg at h1 h2 h3
  have hclosed : inTriangleClosed a b c x := ⟨h1, h2, h3⟩
  -- on the closed triangle, a vanishing coordinate puts `x` on a side
  rcases eq_or_lt_of_le h1 with he1 | hp1
  · exfalso
    have hz : cross (b - a) (x - a) = 0 := by
      rcases mul_eq_zero.mp he1.symm with h | h
      · exact h
      · exact absurd h hD
    exact hab (mem_side_ab_of_closed a b c x hD hclosed hz)
  rcases eq_or_lt_of_le h2 with he2 | hp2
  · exfalso
    have hz : cross (c - b) (x - b) = 0 := by
      rcases mul_eq_zero.mp he2.symm with h | h
      · exact h
      · exact absurd h hD
    exact hbc (mem_side_bc_of_closed a b c x hD hclosed hz)
  rcases eq_or_lt_of_le h3 with he3 | hp3
  · exfalso
    have hz : cross (a - c) (x - c) = 0 := by
      rcases mul_eq_zero.mp he3.symm with h | h
      · exact h
      · exact absurd h hD
    have := mem_side_ca_of_closed a b c x hD hclosed hz
    rw [segment_symm] at this
    exact hac this
  exact Or.inl (inTriangleStrict_of_closed_pos a b c x hp1 hp2 hp3)

end HexArea

/-! ## 2. Orientation bookkeeping for a clip -/

/-- For an ear clip, the orientation of the ear triangle, of the clip and of the
whole polygon coincide. -/
lemma clip_orient_iff (a b c : ℂ) (rest : List ℂ)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: c :: rest))) :
    ((0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: b :: c :: rest)) ∧
     (0 < HexArea.shoelace2 (a :: c :: rest)
        ↔ 0 < HexArea.shoelace2 (a :: b :: c :: rest))) := by
  have hsplit : HexArea.shoelace2 (a :: b :: c :: rest)
      = HexArea.shoelace2 (a :: c :: rest) + HexArea.shoelace2 [a, b, c] :=
    shoelace2_clip_second a b c rest
  constructor
  · constructor
    · intro h
      have := hor.mp h
      rw [hsplit]; linarith
    · intro h
      by_contra hcon
      push_neg at hcon
      have h2 : ¬ (0 < HexArea.shoelace2 (a :: c :: rest)) := fun hh =>
        absurd (hor.mpr hh) (by linarith)
      push_neg at h2
      rw [hsplit] at h; linarith
  · constructor
    · intro h
      have := hor.mpr h
      rw [hsplit]; linarith
    · intro h
      by_contra hcon
      push_neg at hcon
      have h2 : ¬ (0 < HexArea.shoelace2 [a, b, c]) := fun hh =>
        absurd (hor.mp hh) (by linarith)
      push_neg at h2
      rw [hsplit] at h; linarith

/-! ## 3. The induction step: from the clip to the polygon -/

/-- **The dichotomy for the clip, plus the keystone, gives the dichotomy for the
polygon.**

`a :: b :: c :: rest` is a simple polygon with a non-degenerate corner at the tip
`b`, coherently oriented with its clip `C = a :: c :: rest` (`hor`).  If `C`
satisfies the point-in-polygon dichotomy and the ear region lies outside `C`
(`hkey`, the keystone), then `a :: b :: c :: rest` satisfies the dichotomy. -/
theorem dichotomy_of_keystone_clip (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: c :: rest)))
    (hdich : PolyDichotomy (a :: c :: rest))
    (hkey : ∀ x : ℂ, HexArea.inTriangleStrict a b c x →
        HexArea.ptWind x (a :: c :: rest) = 0) :
    PolyDichotomy (a :: b :: c :: rest) := by
  classical
  obtain ⟨horT, horC⟩ := clip_orient_iff a b c rest hor
  -- the two ear sides are edges of the polygon
  have habE : (a, b) ∈ closedEdges (a :: b :: c :: rest) := by
    have h := cycleEdges_cons_cons a b (c :: rest)
    rw [HexArea.cycleEdges_eq_closedEdges] at h
    rw [h]; exact List.mem_cons_self
  have hbcE : (b, c) ∈ closedEdges (a :: b :: c :: rest) := by
    simp [closedEdges, List.rotate_cons_succ]
  -- the main case: a point off the base
  have key : ∀ w : ℂ, (∀ e ∈ HexArea.cycleEdges (a :: b :: c :: rest),
        w ∉ segment ℝ e.1 e.2) → w ∉ segment ℝ a c →
      HexArea.ptWind w (a :: b :: c :: rest) = 0 ∨
        HexArea.ptWind w (a :: b :: c :: rest)
          = 2 * Real.pi * (if 0 < HexArea.shoelace2 (a :: b :: c :: rest) then 1 else -1) := by
    intro w hw hwac
    have hclip := HexArea.ptWind_ear_clip a b c w rest hwac
    -- `w` avoids the edges of the clip as well
    have hwC : ∀ e ∈ HexArea.cycleEdges (a :: c :: rest), w ∉ segment ℝ e.1 e.2 := by
      intro e he
      rw [HexArea.cycleEdges_eq_closedEdges] at he
      rcases closedEdges_clip_cases a b c rest e he with rfl | heM
      · exact hwac
      · exact hw e (by rw [HexArea.cycleEdges_eq_closedEdges]; exact heM)
    rcases HexArea.ptWind_triple_zero_or_strict a b c w hD
        (hw (a, b) (by rw [HexArea.cycleEdges_eq_closedEdges]; exact habE))
        (hw (b, c) (by rw [HexArea.cycleEdges_eq_closedEdges]; exact hbcE)) hwac with hin | h0
    · -- inside the ear triangle
      right
      rw [hclip, hkey w hin, zero_add, HexArea.ptWind_triangle a b c w hin]
      by_cases hT : 0 < HexArea.shoelace2 [a, b, c]
      · rw [if_pos hT, if_pos (horT.mp hT)]
      · rw [if_neg hT, if_neg (fun hh => hT (horT.mpr hh))]
    · -- outside the ear triangle: the clip decides
      rw [hclip, h0, add_zero]
      rcases hdich w hwC with h | h
      · exact Or.inl h
      · right
        rw [h]
        by_cases hC : 0 < HexArea.shoelace2 (a :: c :: rest)
        · rw [if_pos hC, if_pos (horC.mp hC)]
        · rw [if_neg hC, if_neg (fun hh => hC (horC.mpr hh))]
  -- the general case: perturb a point of the base off it
  intro x hx
  by_cases hxac : x ∈ segment ℝ a c
  · -- `x` lies on the ear base, which is not an edge of the polygon: move off it
    have hxE : ∀ e ∈ closedEdges (a :: b :: c :: rest), x ∉ segment ℝ e.1 e.2 := by
      intro e he
      exact hx e (by rw [HexArea.cycleEdges_eq_closedEdges]; exact he)
    obtain ⟨ε, hεpos, hclear⟩ := exists_clearance (closedEdges (a :: b :: c :: rest)) x hxE
    have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
    have hac : a ≠ c := by
      simp only [List.nodup_cons, List.mem_cons] at hnd
      exact fun h => hnd.1 (Or.inr (Or.inl h))
    set d : ℂ := Complex.I * (c - a) with hd
    have hdne : d ≠ 0 := by
      rw [hd]
      exact mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr (Ne.symm hac))
    have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdne
    set η : ℝ := (ε / 2) / ‖d‖ with hη
    have hηpos : 0 < η := by positivity
    set x' : ℂ := x + (η : ℂ) * d with hx'
    have hdist : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → dist (x + ((s * η : ℝ) : ℂ) * d) x < ε := by
      intro s hs0 hs1
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have h1 : s * η * ‖d‖ ≤ η * ‖d‖ := by
        have h1' : s * η * ‖d‖ ≤ 1 * η * ‖d‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs1 hηpos.le) hdnorm.le
        linarith [h1']
      have h2 : η * ‖d‖ = ε / 2 := by
        rw [hη]; field_simp
      linarith
    -- `x'` is off all edges and off the base
    have hx'E : ∀ e ∈ closedEdges (a :: b :: c :: rest), x' ∉ segment ℝ e.1 e.2 := by
      intro e he
      refine hclear x' ?_ e he
      have := hdist 1 (by norm_num) (by norm_num)
      simpa [hx'] using this
    have hcross : HexArea.cross (c - a) (x' - a) = η * Complex.normSq (c - a) := by
      have h0 : HexArea.cross (c - a) (x - a) = 0 := HexArea.cross_combo_segment a c x hxac
      have hsplit : x' - a = (x - a) + (η : ℂ) * d := by rw [hx']; ring
      rw [hsplit, HexArea.cross_add_right, h0, cross_real_mul, hd, cross_I_mul_self]
      ring
    have hx'ac : x' ∉ segment ℝ a c := by
      intro hmem
      have h0 : HexArea.cross (c - a) (x' - a) = 0 := HexArea.cross_combo_segment a c x' hmem
      rw [hcross] at h0
      have : 0 < η * Complex.normSq (c - a) := by
        have : 0 < Complex.normSq (c - a) :=
          Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hac))
        positivity
      linarith
    -- the winding number is unchanged along the perturbation
    have hsame : HexArea.ptWind x (a :: b :: c :: rest)
        = HexArea.ptWind x' (a :: b :: c :: rest) := by
      refine HexArea.ptWind_eq_of_segment_avoids _ x x' ?_
      intro e he
      rw [Set.disjoint_left]
      intro q hq hqe
      obtain ⟨t1, t2, ht1, ht2, htsum, hqeq⟩ := hq
      have hqform : q = x + ((t2 * η : ℝ) : ℂ) * d := by
        rw [← hqeq, hx']
        have : t1 = 1 - t2 := by linarith
        rw [this]
        push_cast [Complex.real_smul]
        ring
      rw [HexArea.cycleEdges_eq_closedEdges] at he
      refine hclear q ?_ e he hqe
      rw [hqform]
      exact hdist t2 ht2 (by linarith)
    rw [hsame]
    exact key x' (fun e he => hx'E e (by rwa [HexArea.cycleEdges_eq_closedEdges] at he)) hx'ac
  · exact key x hx hxac

/-! ## 3.5 A generic point on the ear base

To compare the winding numbers on the two sides of the ear base `[a, c]` one needs
a point of the *open* base that lies on no edge of the polygon.  The midpoint need
not qualify (an edge may cross the base at the midpoint), but a *generic* point
does: every closed edge meets the open base in at most one point, because two
distinct common points would force the edge to lie on the base line, which is
excluded by `ear_base_collinear_case` (for edges not incident to the ear tip) and
by the non-degeneracy `hD` of the tip corner (for the two ear sides).  Since the
open base is infinite and there are finitely many edges, a good point exists.

NOT a dead branch: this is what makes the keystone below independent of any
non-degeneracy hypothesis beyond the ear tip — essential because the chord pieces
handled by the Meisters recursion may have flat corners at the cut seam.
-/

/-- **A point of the open ear base lying on no edge of the polygon.** -/
lemma exists_base_point_off_edges (a b c : ℂ) (rest : List ℂ)
    (h4 : 4 ≤ (a :: b :: c :: rest).length)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    ∃ m ∈ openSegment ℝ a c,
      ∀ e ∈ closedEdges (a :: b :: c :: rest), m ∉ segment ℝ e.1 e.2 := by
  classical
  have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
  have hac : a ≠ c := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  set pt : ℝ → ℂ := fun t => a + (t : ℂ) * (c - a) with hpt
  have hptinj : Function.Injective pt := by
    intro t1 t2 h
    simp only [hpt, add_right_inj] at h
    exact_mod_cast mul_right_cancel₀ hca h
  have hptopen : ∀ t : ℝ, 0 < t → t < 1 → pt t ∈ openSegment ℝ a c := by
    intro t h0 h1
    refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
    simp only [hpt, Complex.real_smul]
    push_cast
    ring
  have hptbase : ∀ t : ℝ, HexArea.cross (a - c) (pt t - c) = 0 := by
    intro t
    simp only [hpt, HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hbline : HexArea.cross (a - c) (b - c) ≠ 0 := by
    have h : HexArea.cross (a - c) (b - c) = HexArea.cross (b - a) (c - b) := by
      simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
    rw [h]; exact hD
  -- every closed edge meets the open base in at most one parameter
  have huniq : ∀ e ∈ closedEdges (a :: b :: c :: rest), ∀ t1 t2 : ℝ,
      0 < t1 → t1 < 1 → 0 < t2 → t2 < 1 →
      pt t1 ∈ segment ℝ e.1 e.2 → pt t2 ∈ segment ℝ e.1 e.2 → t1 = t2 := by
    rintro ⟨p, q⟩ hpq t1 t2 h01 h11 h02 h12 hm1 hm2
    by_contra hne
    have hpne : pt t1 ≠ pt t2 := fun h => hne (hptinj h)
    obtain ⟨u1, s1, hu1, hs1, hsum1, he1⟩ := hm1
    obtain ⟨u2, s2, hu2, hs2, hsum2, he2⟩ := hm2
    have hx1 : pt t1 = (1 - s1) • p + s1 • q := by
      rw [← he1, show u1 = 1 - s1 by linarith]
    have hx2 : pt t2 = (1 - s2) • p + s2 • q := by
      rw [← he2, show u2 = 1 - s2 by linarith]
    have hsne : s1 ≠ s2 := by
      intro h; exact hpne (by rw [hx1, hx2, h])
    have hf1 : (1 - s1) * HexArea.cross (a - c) (p - c)
        + s1 * HexArea.cross (a - c) (q - c) = 0 := by
      rw [← HexArea.cross_affine, ← hx1]; exact hptbase t1
    have hf2 : (1 - s2) * HexArea.cross (a - c) (p - c)
        + s2 * HexArea.cross (a - c) (q - c) = 0 := by
      rw [← HexArea.cross_affine, ← hx2]; exact hptbase t2
    have hfq : HexArea.cross (a - c) (q - c) = HexArea.cross (a - c) (p - c) := by
      have hd : (s1 - s2) * (HexArea.cross (a - c) (q - c)
          - HexArea.cross (a - c) (p - c)) = 0 := by linear_combination hf1 - hf2
      rcases mul_eq_zero.mp hd with h | h
      · exact absurd (by linarith : s1 = s2) hsne
      · linarith
    have hfp : HexArea.cross (a - c) (p - c) = 0 := by
      rw [hfq] at hf1; linear_combination hf1
    have hfq0 : HexArea.cross (a - c) (q - c) = 0 := by rw [hfq]; exact hfp
    have hbp : b ≠ p := by rintro rfl; exact hbline hfp
    have hbq : b ≠ q := by rintro rfl; exact hbline hfq0
    -- the midpoint of the two intersection points is interior to the edge
    have hs0 : 0 < (s1 + s2) / 2 := by
      rcases lt_or_gt_of_ne hsne with h | h <;> linarith
    have hs1' : (s1 + s2) / 2 < 1 := by
      have hs1le : s1 ≤ 1 := by linarith
      have hs2le : s2 ≤ 1 := by linarith
      rcases lt_or_gt_of_ne hsne with h | h <;> linarith
    have hmid : pt ((t1 + t2) / 2) = (1 - (s1 + s2) / 2) • p + ((s1 + s2) / 2) • q := by
      have h2 : pt ((t1 + t2) / 2) = ((2:ℝ)⁻¹ : ℝ) • (pt t1 + pt t2) := by
        simp only [hpt, Complex.real_smul]
        push_cast
        ring
      rw [h2, hx1, hx2]
      module
    have hvopen : pt ((t1 + t2) / 2) ∈ openSegment ℝ p q :=
      ⟨1 - (s1 + s2) / 2, (s1 + s2) / 2, by linarith, hs0, by ring, hmid.symm⟩
    have hvac : pt ((t1 + t2) / 2) ∈ segment ℝ a c :=
      openSegment_subset_segment ℝ a c (hptopen _ (by linarith) (by linarith))
    exact ear_base_collinear_case (a :: b :: c :: rest) h4 hsimple 0 a b c rest (by simp)
      hD hempty hdiag p q hpq hbp hbq hfp hfq0 (pt ((t1 + t2) / 2)) hvopen hvac
  -- the bad parameters form a finite set
  set B : Set ℝ := {t | (0 < t ∧ t < 1) ∧
    ∃ e ∈ closedEdges (a :: b :: c :: rest), pt t ∈ segment ℝ e.1 e.2} with hB
  have hBfin : B.Finite := by
    have hsub : B ⊆ ⋃ e ∈ {e | e ∈ closedEdges (a :: b :: c :: rest)},
        {t : ℝ | (0 < t ∧ t < 1) ∧ pt t ∈ segment ℝ e.1 e.2} := by
      rintro t ⟨ht01, e, he, hmem⟩
      exact Set.mem_biUnion he ⟨ht01, hmem⟩
    refine Set.Finite.subset (Set.Finite.biUnion (List.finite_toSet _) ?_) hsub
    intro e he
    refine Set.Subsingleton.finite ?_
    intro t1 h1 t2 h2
    exact huniq e he t1 t2 h1.1.1 h1.1.2 h2.1.1 h2.1.2 h1.2 h2.2
  have hinf : (Set.Ioo (0:ℝ) 1).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨t, ht, htB⟩ := (hinf.diff hBfin).nonempty
  refine ⟨pt t, hptopen t ht.1 ht.2, ?_⟩
  intro e he hmem
  exact htB ⟨⟨ht.1, ht.2⟩, e, he, hmem⟩

/-! ## 4. The induction step: the keystone from the dichotomy for the clip -/

/-- **The dichotomy for the clip implies the keystone for the polygon.**

`a :: b :: c :: rest` is a simple, cyclically non-degenerate polygon with an
empty ear at the tip `b`, coherently oriented with its clip `C = a :: c :: rest`.
If `C` satisfies the point-in-polygon dichotomy, then the ear region lies outside
`C`: the winding number of `C` around a point strictly inside the ear triangle
vanishes.

The cyclic non-degeneracy `hnondeg` is used only to know that the *interior of the
ear base* meets no edge of the polygon (`ear_edge_interior_not_base`,
`RequestProject.SAWUmlaufTriangleClosed`), so that the winding numbers can be
compared across the base. -/
theorem keystone_of_dichotomy_clip (a b c : ℂ) (rest : List ℂ)
    (h4 : 4 ≤ (a :: b :: c :: rest).length)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: c :: rest)))
    (hdich : PolyDichotomy (a :: c :: rest))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x (a :: c :: rest) = 0 := by
  classical
  have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
  have hsubC : List.Sublist (a :: c :: rest) (a :: b :: c :: rest) :=
    List.cons_sublist_cons.mpr (List.sublist_cons_self b (c :: rest))
  have hndC : (a :: c :: rest).Nodup := hsubC.nodup hnd
  have hac : a ≠ c := by
    intro h
    exact (List.nodup_cons.mp hnd).1 (by simp [h])
  -- a generic point of the ear base, lying on no edge of the polygon
  obtain ⟨m, hmopen, hmoff⟩ :=
    exists_base_point_off_edges a b c rest h4 hsimple hD hempty hdiag
  have hmseg : m ∈ segment ℝ a c := openSegment_subset_segment ℝ a c hmopen
  -- the path edges of the clip avoid the midpoint
  have hpath : ∀ p ∈ (c :: (rest ++ [a])).zip ((c :: (rest ++ [a])).drop 1),
      m ∉ segment ℝ p.1 p.2 := by
    intro p hp
    obtain ⟨hpC, hpne⟩ := mem_closedEdges_of_mem_tail_zip a c rest hndC p hp
    rcases closedEdges_clip_cases a b c rest p hpC with rfl | hpM
    · exact absurd ⟨rfl, rfl⟩ hpne
    · exact hmoff p hpM
  obtain ⟨δ, hδpos, hjump⟩ := HexArea.ptWind_jump_edge a c rest m hac hmopen hpath
  obtain ⟨ε, hεpos, hclear⟩ := exists_clearance (closedEdges (a :: b :: c :: rest)) m hmoff
  -- the perturbation pair across the base, in the rotated triangle `c, a, b`
  have hDrot : HexArea.cross (a - c) (b - a) ≠ 0 := by
    have : HexArea.cross (a - c) (b - a) = HexArea.cross (b - a) (c - b) := by
      simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
    rw [this]; exact hD
  obtain ⟨y, z, hym, hzm, hcy, hcz, hyin, hzin⟩ :=
    exists_perturb_pair c a b m (Ne.symm hac) (by rwa [openSegment_symm] at hmopen) hDrot
      (min δ ε) (lt_min hδpos hεpos)
  -- both points are off all edges of the polygon and of the clip
  have hoffM : ∀ w : ℂ, dist w m < min δ ε →
      ∀ e ∈ closedEdges (a :: b :: c :: rest), w ∉ segment ℝ e.1 e.2 := by
    intro w hw e he
    exact hclear w (lt_of_lt_of_le hw (min_le_right _ _)) e he
  have hnotbase : ∀ w : ℂ, HexArea.cross (a - c) (w - c) ≠ 0 → w ∉ segment ℝ a c := by
    intro w hw hmem
    rw [segment_symm] at hmem
    exact hw (HexArea.cross_combo_segment c a w hmem)
  have hoffC : ∀ w : ℂ, dist w m < min δ ε → HexArea.cross (a - c) (w - c) ≠ 0 →
      ∀ e ∈ HexArea.cycleEdges (a :: c :: rest), w ∉ segment ℝ e.1 e.2 := by
    intro w hw hcw e he
    rw [HexArea.cycleEdges_eq_closedEdges] at he
    rcases closedEdges_clip_cases a b c rest e he with rfl | heM
    · exact hnotbase w hcw
    · exact hoffM w hw e heM
  have hoffCy := hoffC y hym (ne_of_gt hcy)
  have hoffCz := hoffC z hzm (ne_of_lt hcz)
  have hvy : ∀ v ∈ (a :: c :: rest), v ≠ y :=
    fun v hv => HexArea.vertices_ne_of_avoids_cycleEdges _ y hoffCy v hv
  have hvz : ∀ v ∈ (a :: c :: rest), v ≠ z :=
    fun v hv => HexArea.vertices_ne_of_avoids_cycleEdges _ z hoffCz v hv
  -- the jump across the base: the `z` side is the positive one for `cross (c - a)`
  have hsign : ∀ w : ℂ, HexArea.cross (c - a) (w - a) = - HexArea.cross (a - c) (w - c) := by
    intro w
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
  have hjmp : HexArea.ptWind z (a :: c :: rest) - HexArea.ptWind y (a :: c :: rest)
      = 2 * Real.pi := by
    refine hjump z y (lt_of_lt_of_le hzm (min_le_left _ _)) (lt_of_lt_of_le hym (min_le_left _ _))
      hvz hvy ?_ ?_
    · rw [hsign z]; linarith
    · rw [hsign y]; linarith
  -- the dichotomy for the clip pins both values
  have hdy := hdich y hoffCy
  have hdz := hdich z hoffCz
  have hpi : 0 < Real.pi := Real.pi_pos
  have htri : HexArea.shoelace2 [a, b, c] = HexArea.cross (b - a) (c - b) :=
    shoelace2_triple_eq_cross a b c
  -- the inside point has vanishing clip winding
  have key : ∃ w : ℂ, HexArea.inTriangleStrict a b c w ∧ HexArea.ptWind w (a :: c :: rest) = 0 := by
    rcases lt_or_gt_of_ne hD with hDneg | hDpos
    · -- negatively oriented ear: `z` is the inner point, and the clip is negative
      have hnotpos : ¬ (0 < HexArea.shoelace2 (a :: c :: rest)) := by
        intro hcon
        have := hor.mpr hcon
        rw [htri] at this; linarith
      rw [if_neg hnotpos] at hdy hdz
      refine ⟨z, (HexArea.inTriangleStrict_cyc a b c z).mp (hzin (by rw [show HexArea.cross (a - c) (b - a)
        = HexArea.cross (b - a) (c - b) from by
          simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring]; exact hDneg)), ?_⟩
      rcases hdy with hy0 | hy1 <;> rcases hdz with hz0 | hz1
      · rw [hy0, hz0] at hjmp; linarith
      · rw [hy0, hz1] at hjmp; nlinarith
      · exact hz0
      · rw [hy1, hz1] at hjmp; linarith
    · -- positively oriented ear: `y` is the inner point, and the clip is positive
      have hpos : 0 < HexArea.shoelace2 (a :: c :: rest) := by
        exact hor.mp (by rw [htri]; exact hDpos)
      rw [if_pos hpos] at hdy hdz
      refine ⟨y, (HexArea.inTriangleStrict_cyc a b c y).mp (hyin (by rw [show HexArea.cross (a - c) (b - a)
        = HexArea.cross (b - a) (c - b) from by
          simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring]; exact hDpos)), ?_⟩
      rcases hdy with hy0 | hy1 <;> rcases hdz with hz0 | hz1
      · rw [hy0, hz0] at hjmp; linarith
      · exact hy0
      · rw [hy1, hz0] at hjmp; linarith
      · rw [hy1, hz1] at hjmp; linarith
  obtain ⟨w, hwin, hwzero⟩ := key
  -- transport the value along the (convex) open ear triangle
  have hxw : HexArea.ptWind x (a :: c :: rest) = HexArea.ptWind w (a :: c :: rest) := by
    refine HexArea.ptWind_eq_of_segment_avoids _ x w ?_
    intro p hp
    rw [Set.disjoint_left]
    intro q hq hqp
    have hqin : HexArea.inTriangleStrict a b c q :=
      inTriangleStrict_of_segment a b c x w q hin hwin hq
    rw [HexArea.cycleEdges_eq_closedEdges] at hp
    rcases closedEdges_clip_cases a b c rest p hp with rfl | hpM
    · -- the base: a strict interior point is off it
      refine hnotbase q ?_ hqp
      rcases hqin with ⟨_, _, h3⟩ | ⟨_, _, h3⟩
      · exact ne_of_gt h3
      · exact ne_of_lt h3
    · exact ear_strict_interior_off_closedEdges (a :: b :: c :: rest) h4 hsimple 0 a b c rest
        (by simp) hD hempty hdiag q hqin p.1 p.2 hpM hqp
  rw [hxw, hwzero]

/-! ## 5. The keystone relative to the dichotomy for shorter polygons

The two step lemmas above turn the point-in-polygon dichotomy into an induction on
the number of vertices.  The *consumers* of the keystone inside the Meisters
ear-existence chain always apply it to polygons that are **strictly shorter** than
the polygon currently under consideration (the two pieces of a chord cut).  This
section packages the keystone in exactly that relative form: everything is stated
relative to a bound `N` and the hypothesis `DichBelow N` that the dichotomy is
already known for all simple polygons with fewer than `N` vertices.

NOT a dead branch: `keystone_below` and `ear_interior_ptWind_ne_zero_of_rotation_below`
are the interfaces through which the Meisters chain is being re-derived without
assuming the dichotomy, so that the induction can be closed.
-/

/-- `DichBelow N` — the point-in-polygon dichotomy for all simple polygons with
fewer than `N` vertices. -/
def DichBelow (N : ℕ) : Prop :=
  ∀ Q : List ℂ, Q.length < N → 3 ≤ Q.length → PolygonSimple Q → PolyDichotomy Q

/-- `DichBelow` is antitone. -/
lemma DichBelow.mono {N M : ℕ} (h : N ≤ M) (hM : DichBelow M) : DichBelow N :=
  fun Q hQ h3 hs => hM Q (lt_of_lt_of_le hQ h) h3 hs

/-- **The keystone, relative to the dichotomy for shorter polygons.**  If the
dichotomy holds for all simple polygons with fewer than `N` vertices and
`a :: b :: c :: rest` is a simple polygon with at most `N` vertices carrying an
empty, coherently oriented ear at `b`, then the clip does not wind around the ear
interior. -/
theorem keystone_below (N : ℕ) (hN : DichBelow N) (a b c : ℂ) (rest : List ℂ)
    (hlen : rest.length + 3 ≤ N) (hrest : rest ≠ [])
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 (a :: c :: rest)))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x (a :: c :: rest) = 0 := by
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
  exact keystone_of_dichotomy_clip a b c rest h4 hsimple hD hempty hdiag hor hdich x hin

/-- **Ear-interior nonvanishing, relative to the dichotomy for shorter polygons.**
The relative form of `ear_interior_ptWind_ne_zero_of_rotation`
(`RequestProject.SAWUmlaufEarTipEscape`): the winding number of `P` around a point
strictly inside an empty, coherently oriented ear of `P` is nonzero, assuming the
dichotomy only for polygons with fewer than `N` vertices (`P` itself has at most
`N`).  The degenerate case `tlP = []` (the polygon *is* the triangle) needs no
hypothesis at all. -/
theorem ear_interior_ptWind_ne_zero_of_rotation_below (N : ℕ) (hN : DichBelow N)
    (P : List ℂ) (hPN : P.length ≤ N) (hPsimple : PolygonSimple P)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ) (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hDP : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (hdiagP : ∀ y ∈ tlP, y ∉ segment ℝ a' c')
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (y : ℂ) (hin : HexArea.inTriangleStrict a' b' c' y) :
    HexArea.ptWind y P ≠ 0 := by
  -- `y` is off the ear base
  have hac : y ∉ segment ℝ a' c' := by
    intro hmem
    have h0 : HexArea.cross (a' - c') (y - c') = 0 := by
      have := HexArea.cross_combo_segment a' c' y hmem
      have hrw : HexArea.cross (a' - c') (y - c') = - HexArea.cross (c' - a') (y - a') := by
        simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
      rw [hrw, this]; ring
    rcases hin with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;> rw [h0] at h3 <;> exact absurd h3 (by norm_num)
  by_cases htl : tlP = []
  · subst htl
    have hP3 : HexArea.ptWind y P = HexArea.ptWind y [a', b', c'] := by
      rw [← HexArea.ptWind_rotate y P s, hrotP]
    rw [hP3]
    exact HexArea.ptWind_triangle_ne_zero a' b' c' y hin
  have hlen' : P.length = tlP.length + 3 := by
    have hlen : (P.rotate s).length = tlP.length + 3 := by rw [hrotP]; simp
    simpa using hlen
  have hMsimple : PolygonSimple (a' :: b' :: c' :: tlP) := by
    have := (PolygonSimple_rotate P s).2 hPsimple
    rwa [hrotP] at this
  have hzero := keystone_below N hN a' b' c' tlP (by omega) htl hMsimple hDP
    hemptyP hdiagP horientP y hin
  have hsplit := HexArea.ptWind_ear_split y a' b' c' P s tlP hrotP hac hin
  rw [hzero, zero_add] at hsplit
  rw [hsplit]
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases h : 0 < HexArea.shoelace2 [a', b', c']
  · rw [if_pos h]; intro hcon; nlinarith
  · rw [if_neg h]; intro hcon; nlinarith

end
