import Mathlib
import RequestProject.SAWUmlaufEarClearance
import RequestProject.SAWUmlaufPtWindJordan
import RequestProject.SAWUmlaufExterior

/-!
# `SAWUmlaufEarTipEscape` — the ear tip is outside the clipped polygon

This file isolates the **single remaining plane-topology input** of the polygonal
Umlaufsatz in its sharpest form, and derives from it the ear-interior winding
statement that the Meisters induction consumes.

Let `L` be a simple polygon with a cyclic rotation `a :: b :: c :: rest`
exhibiting an *empty ear* at the tip `b`: the corner is non-degenerate
(`cross (b-a) (c-b) ≠ 0`), no far vertex lies strictly inside the triangle
`a b c` or on the closed diagonal `[a, c]`, and the ear is *coherently oriented*
with `L` (`hor`).  Clipping the tip leaves the shorter cycle `a :: c :: rest`.

The keystone is

  `ear_interior_clip_ptWind_zero` :
      `HexArea.ptWind x (a :: c :: rest) = 0`   for `x` strictly inside `a b c`,

i.e. *the ear region lies outside the clipped polygon*.  Because the winding
number of the ear triangle around such an `x` is `±2π` (`HexArea.ptWind_triangle`)
and the two add up to the winding number of `L` (`HexArea.ptWind_ear_split`), the
keystone immediately gives

  `ear_interior_ptWind_ne_zero_via_clip` : `HexArea.ptWind x L ≠ 0`,

which is exactly the ear-interior input of
`RequestProject.SAWUmlaufJordanCore` (previously derived from the much stronger
point-in-polygon dichotomy `polygon_ptWind_dichotomy`).

## Why the orientation hypothesis is needed

Without `hor` the statement is **false**: for a dart (a non-convex quadrilateral,
see `RequestProject.SAWUmlaufDartCounterexample`) the reflex corner spans an
*exterior* empty ear, and clipping it there *adds* the triangle to the enclosed
region, so the ear interior is *inside* the clip and the winding is `±2π`.  The
orientation clause `hor` is exactly what rules the exterior ear out; it is part of
the ear data produced by the Meisters search
(`exists_empty_corner_avoiding`, `RequestProject.SAWUmlaufPolyMeisters`).

## What is proved here

* `closedEdges_clip_cases` — every closed edge of the clip is either the new
  diagonal `(a, c)` or a closed edge of `L`;
* `tip_not_mem_segment_ac`, `tip_off_clip_edges` — the tip lies off every edge of
  the clip;
* `inTriangleStrict_toward_tip` — the segment from an interior point of the ear
  triangle to the tip stays in the (open) triangle until it reaches the tip;
* `ptWind_clip_eq_tip` — hence the winding number of the clip is constant on the
  ear interior and equals its value at the tip `b`;
* `ear_interior_clip_ptWind_zero_of_tip_not_hull` — **the keystone in the
  convex-position case (proved)**: if the tip is not in the convex hull of the
  clip's vertices (e.g. when the tip is the lex-minimal vertex of `L`), the
  winding of the clip around the ear interior vanishes, by
  `HexArea.ptWind_zero_of_not_mem_convexHull`;
* `ear_interior_clip_ptWind_zero` — the keystone in general (**`sorry`**);
* `ear_interior_ptWind_ne_zero_via_clip` — the ear-interior consequence (proved
  from the keystone).

NOT a dead branch: imported by `RequestProject.SAWUmlaufJordanCore`, which is on
the live route to `polygon_umlaufsatz`.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The edges of the clipped cycle -/

/-- The closed cycle `a :: c :: rest` obtained by clipping the tip `b` has, as its
closed edges, the new diagonal `(a, c)` and closed edges of `a :: b :: c :: rest`. -/
lemma closedEdges_clip_cases (a b c : ℂ) (rest : List ℂ) (e : ℂ × ℂ)
    (he : e ∈ closedEdges (a :: c :: rest)) :
    e = (a, c) ∨ e ∈ closedEdges (a :: b :: c :: rest) := by
  have hr1 : (a :: c :: rest).rotate 1 = (c :: rest) ++ [a] := by
    rw [List.rotate_cons_succ]; simp
  have hr2 : (a :: b :: c :: rest).rotate 1 = (b :: c :: rest) ++ [a] := by
    rw [List.rotate_cons_succ]; simp
  have h1 : closedEdges (a :: c :: rest) = (a, c) :: (c :: rest).zip (rest ++ [a]) := by
    rw [closedEdges, hr1]; simp
  have h2 : closedEdges (a :: b :: c :: rest)
      = (a, b) :: (b, c) :: (c :: rest).zip (rest ++ [a]) := by
    rw [closedEdges, hr2]; simp
  rw [h1, List.mem_cons] at he
  rcases he with rfl | he
  · exact Or.inl rfl
  · exact Or.inr (by rw [h2]; simp [he])

/-! ## 2. Cross-product bookkeeping inside the ear triangle -/

/-- The three edge cross products of a point sum to the doubled signed area. -/
lemma cross_sum_edges_tip (a b c x : ℂ) :
    HexArea.cross (b - a) (x - a) + HexArea.cross (c - b) (x - b)
      + HexArea.cross (a - c) (x - c) = HexArea.cross (b - a) (c - b) := by
  simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]
  ring

/-- The doubled signed area seen from the third corner. -/
lemma cross_ac_bc (a b c : ℂ) :
    HexArea.cross (a - c) (b - c) = HexArea.cross (b - a) (c - b) := by
  simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]
  ring

/-- **The tip is not on the closed ear diagonal**, for a non-degenerate corner. -/
lemma tip_not_mem_segment_ac (a b c : ℂ) (hD : HexArea.cross (b - a) (c - b) ≠ 0) :
    b ∉ segment ℝ a c := by
  intro hb
  have h0 : HexArea.cross (c - a) (b - a) = 0 := HexArea.cross_combo_segment a c b hb
  apply hD
  have : HexArea.cross (b - a) (c - b) = - HexArea.cross (c - a) (b - a) := by
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
  rw [this, h0]; ring

/-- **Moving from an interior point of the ear triangle towards the tip stays
inside**, until the tip is reached. -/
lemma inTriangleStrict_toward_tip (a b c x w : ℂ)
    (hin : HexArea.inTriangleStrict a b c x) (hw : w ∈ segment ℝ x b) (hwb : w ≠ b) :
    HexArea.inTriangleStrict a b c w := by
  obtain ⟨t1, t2, ht1, ht2, hsum, hweq⟩ := hw
  have ht1pos : 0 < t1 := by
    rcases lt_or_eq_of_le ht1 with h | h
    · exact h
    · exfalso
      apply hwb
      have ht2' : t2 = 1 := by linarith
      rw [← hweq, ← h, ht2']
      simp
  have ht1' : t1 = 1 - t2 := by linarith
  have hweq' : w = ((1 - t2 : ℝ) : ℂ) * x + ((t2 : ℝ) : ℂ) * b := by
    rw [← hweq, ht1']
    simp [Complex.real_smul]
  have hD : HexArea.cross (b - a) (c - b)
      = HexArea.cross (b - a) (x - a) + HexArea.cross (c - b) (x - b)
        + HexArea.cross (a - c) (x - c) := (cross_sum_edges_tip a b c x).symm
  have e1 : HexArea.cross (b - a) (w - a) = (1 - t2) * HexArea.cross (b - a) (x - a) := by
    rw [hweq']
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e2 : HexArea.cross (c - b) (w - b) = (1 - t2) * HexArea.cross (c - b) (x - b) := by
    rw [hweq']
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e3 : HexArea.cross (a - c) (w - c)
      = (1 - t2) * HexArea.cross (a - c) (x - c) + t2 * HexArea.cross (b - a) (c - b) := by
    rw [hweq']
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ht2lt : t2 < 1 := by linarith
  rcases hin with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    have hDpos : 0 < HexArea.cross (b - a) (c - b) := by rw [hD]; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact mul_pos (by linarith) h1
    · rw [e2]; exact mul_pos (by linarith) h2
    · rw [e3]; nlinarith
  · right
    have hDneg : HexArea.cross (b - a) (c - b) < 0 := by rw [hD]; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; nlinarith
    · rw [e2]; nlinarith
    · rw [e3]; nlinarith

/-! ## 3. The ear region misses the clipped polygon's boundary -/

/-- **A vertex of a simple polygon lies off every closed edge it is not an
endpoint of.**  (The two adjacent edges are handled by the short-cycle lemmas of
`RequestProject.SAWUmlaufCycleAdjacent`.) -/
lemma vertex_off_nonincident_edge (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L) (x : ℂ) (hx : x ∈ L) (p q : ℂ)
    (hpq : (p, q) ∈ closedEdges L) (hxp : x ≠ p) (hxq : x ≠ q) :
    x ∉ segment ℝ p q := by
  have hnd : L.Nodup := hsimple.1
  obtain ⟨x', hx'⟩ := exists_closedEdges_succ L x hx
  obtain ⟨x'', hx''⟩ := exists_closedEdges_pred L x hx
  by_cases h1 : x' = p
  · -- the successor of `x` is `p`; look at the predecessor
    by_cases h2 : x'' = p
    · exact absurd (closedEdges_no_two_cycle L hnd (by omega) x p (h1 ▸ hx') (h2 ▸ hx'')) (by simp)
    · by_cases h3 : x'' = q
      · exact absurd
          (closedEdges_no_three_cycle L hnd h4 q x p (h3 ▸ hx'') (h1 ▸ hx') hpq) (by simp)
      · exact vertex_off_edge_via_pred L hsimple p q x x'' hpq hx'' h2 h3 hxp hxq
  · by_cases h2 : x' = q
    · -- both `x` and `p` have successor `q`
      exact absurd (closedEdges_pred_unique L hnd q x p (h2 ▸ hx') hpq) hxp
    · exact vertex_off_edge_via_succ L hsimple p q x x' hpq hx' hxp hxq h1 h2

/-- **The clipped tip lies off every closed edge of the clipped cycle.** -/
lemma tip_off_clip_edges (a b c : ℂ) (rest : List ℂ)
    (h4 : 4 ≤ (a :: b :: c :: rest).length)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (e : ℂ × ℂ) (he : e ∈ closedEdges (a :: c :: rest)) :
    b ∉ segment ℝ e.1 e.2 := by
  have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
  have hbnot : b ∉ (a :: c :: rest) := by
    simp only [List.nodup_cons, List.mem_cons] at hnd ⊢
    push_neg
    refine ⟨fun h => hnd.1 (by rw [← h]; simp), fun h => hnd.2.1 (by rw [h]; simp), ?_⟩
    intro hmem
    exact hnd.2.1 (by simp [hmem])
  rcases closedEdges_clip_cases a b c rest e he with rfl | heM
  · exact tip_not_mem_segment_ac a b c hD
  · have h1 : e.1 ∈ (a :: c :: rest) := mem_of_fst_mem_closedEdges _ e.1 e.2 (by simpa using he)
    have h2 : e.2 ∈ (a :: c :: rest) := mem_of_snd_mem_closedEdges _ e.1 e.2 (by simpa using he)
    refine vertex_off_nonincident_edge (a :: b :: c :: rest) h4 hsimple b (by simp)
      e.1 e.2 (by simpa using heM) ?_ ?_
    · intro h; exact hbnot (h ▸ h1)
    · intro h; exact hbnot (h ▸ h2)

/-- Points of the closed segment from an interior point of the ear triangle to the
tip lie off every closed edge of the clipped cycle. -/
lemma segment_to_tip_off_clip_edges (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x)
    (w : ℂ) (hw : w ∈ segment ℝ x b)
    (e : ℂ × ℂ) (he : e ∈ closedEdges (a :: c :: rest)) :
    w ∉ segment ℝ e.1 e.2 := by
  have hMsimple : PolygonSimple (a :: b :: c :: rest) := by
    rw [← hrot]; exact (PolygonSimple_rotate L ρ).mpr hsimple
  have hMlen : (a :: b :: c :: rest).length = L.length := by rw [← hrot]; simp
  have h4M : 4 ≤ (a :: b :: c :: rest).length := by omega
  by_cases hwb : w = b
  · rw [hwb]
    exact tip_off_clip_edges a b c rest h4M hMsimple hD e he
  · have hwin : HexArea.inTriangleStrict a b c w :=
      inTriangleStrict_toward_tip a b c x w hin hw hwb
    rcases closedEdges_clip_cases a b c rest e he with rfl | heM
    · -- the new diagonal `(a, c)`
      intro hmem
      have h0 : HexArea.cross (a - c) (w - c) = 0 := by
        have hcc := HexArea.cross_combo_segment a c w (by simpa using hmem)
        have hrw : HexArea.cross (a - c) (w - c) = - HexArea.cross (c - a) (w - a) := by
          simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
        rw [hrw, hcc]; ring
      rcases hwin with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;> rw [h0] at h3 <;> exact absurd h3 (by norm_num)
    · exact ear_strict_interior_off_closedEdges (a :: b :: c :: rest) h4M hMsimple 0 a b c rest
        (by simp) hD hempty hdiag w hwin e.1 e.2 heM

/-! ## 4. The winding number of the clip on the ear region -/

/-- **The winding number of the clipped cycle is constant on the ear region** and
equals its value at the clipped tip. -/
lemma ptWind_clip_eq_tip (L : List ℂ) (h4 : 4 ≤ L.length) (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x (a :: c :: rest) = HexArea.ptWind b (a :: c :: rest) := by
  refine HexArea.ptWind_eq_of_segment_avoids (a :: c :: rest) x b ?_
  intro p hp
  rw [Set.disjoint_left]
  intro w hw hwp
  rw [HexArea.cycleEdges_eq_closedEdges] at hp
  exact segment_to_tip_off_clip_edges L h4 hsimple ρ a b c rest hrot hD hempty hdiag
    x hin w hw p hp hwp

/-! ## 5. The keystone -/

/-- **The ear region lies outside the clipped polygon (keystone, `sorry`).**

For a simple polygon `L` with an empty, coherently oriented ear `a, b, c`
(`hor`), the winding number of the clipped cycle `a :: c :: rest` around any point
strictly inside the ear triangle vanishes.

**Status: `sorry`.**  This is the single remaining plane-topology input of the
polygonal Umlaufsatz.  It replaces the strictly stronger point-in-polygon
dichotomy `polygon_ptWind_dichotomy` that the previous route used.  By
`ptWind_clip_eq_tip` it is equivalent to `ptWind b (a :: c :: rest) = 0`: *the ear
tip escapes the clipped polygon*.  It is proved below in the convex-position case
(`ear_interior_clip_ptWind_zero_of_tip_not_hull`), which is exactly the case the
Meisters search realises at the lex-minimal vertex; the general case needs the
orientation hypothesis `hor` (see the module docstring: for an exterior ear of a
dart the statement is false). -/
theorem ear_interior_clip_ptWind_zero (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 L))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x (a :: c :: rest) = 0 := by
  sorry

/-- **The keystone in convex position (PROVED).**  If the ear tip `b` is not in
the convex hull of the clipped polygon's vertices — the situation at a strictly
extreme (e.g. lex-minimal) vertex of `L` — then the winding number of the clip
around the ear interior vanishes, with no orientation hypothesis needed. -/
theorem ear_interior_clip_ptWind_zero_of_tip_not_hull (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hhull : b ∉ convexHull ℝ (((a :: c :: rest).toFinset : Finset ℂ) : Set ℂ))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x (a :: c :: rest) = 0 := by
  rw [ptWind_clip_eq_tip L h4 hsimple ρ a b c rest hrot hD hempty hdiag x hin]
  exact HexArea.ptWind_zero_of_not_mem_convexHull b (a :: c :: rest) hhull

/-! ## 6. The ear-interior consequence -/

/-- **The winding number of a simple polygon around a point of an empty ear's
interior is nonzero** — derived from the keystone.  The ear triangle contributes
`±2π` (`HexArea.ptWind_triangle`) and the clip contributes `0`. -/
theorem ear_interior_ptWind_ne_zero_via_clip (L : List ℂ) (h4 : 4 ≤ L.length)
    (hsimple : PolygonSimple L)
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hempty : ∀ y ∈ rest, ¬ HexArea.inTriangleStrict a b c y)
    (hdiag : ∀ y ∈ rest, y ∉ segment ℝ a c)
    (hor : (0 < HexArea.shoelace2 [a, b, c] ↔ 0 < HexArea.shoelace2 L))
    (x : ℂ) (hin : HexArea.inTriangleStrict a b c x) :
    HexArea.ptWind x L ≠ 0 := by
  have hac : x ∉ segment ℝ a c := by
    intro hmem
    have h0 : HexArea.cross (a - c) (x - c) = 0 := by
      have := HexArea.cross_combo_segment a c x hmem
      have hrw : HexArea.cross (a - c) (x - c) = - HexArea.cross (c - a) (x - a) := by
        simp only [HexArea.cross, Complex.sub_re, Complex.sub_im]; ring
      rw [hrw, this]; ring
    rcases hin with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;> rw [h0] at h3 <;> exact absurd h3 (by norm_num)
  have hsplit := HexArea.ptWind_ear_split x a b c L ρ rest hrot hac hin
  have hzero := ear_interior_clip_ptWind_zero L h4 hsimple ρ a b c rest hrot hD hempty hdiag hor
    x hin
  rw [hzero, zero_add] at hsplit
  rw [hsplit]
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases h : 0 < HexArea.shoelace2 [a, b, c]
  · rw [if_pos h]; intro hcon; nlinarith
  · rw [if_neg h]; intro hcon; nlinarith

/-! ## 7. The ear-interior statement in "ear rotation of a piece" form -/

/-- **Ear-interior nonvanishing, packaged for a polygon presented by an ear
rotation.**  If `P.rotate s = a' :: b' :: c' :: tlP` exhibits an empty ear whose
orientation matches that of the clip `a' :: c' :: tlP`, then the winding number of
`P` around any point strictly inside the ear triangle is nonzero.  The degenerate
case `tlP = []` (the polygon *is* the triangle) is covered by
`HexArea.ptWind_triangle_ne_zero`. -/
theorem ear_interior_ptWind_ne_zero_of_rotation (P : List ℂ) (hPsimple : PolygonSimple P)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ) (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hDP : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (hdiagP : ∀ y ∈ tlP, y ∉ segment ℝ a' c')
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (y : ℂ) (hin : HexArea.inTriangleStrict a' b' c' y) :
    HexArea.ptWind y P ≠ 0 := by
  by_cases htl : tlP = []
  · subst htl
    have hP3 : HexArea.ptWind y P = HexArea.ptWind y [a', b', c'] := by
      rw [← HexArea.ptWind_rotate y P s, hrotP]
    rw [hP3]
    exact HexArea.ptWind_triangle_ne_zero a' b' c' y hin
  have hP4 : 4 ≤ P.length := by
    have hlen : (P.rotate s).length = tlP.length + 3 := by rw [hrotP]; simp
    have hlen' : P.length = tlP.length + 3 := by simpa using hlen
    have hpos : 0 < tlP.length := List.length_pos_iff.mpr htl
    omega
  have hclipP : HexArea.shoelace2 P
      = HexArea.shoelace2 (a' :: c' :: tlP) + HexArea.shoelace2 [a', b', c'] := by
    have h1 : HexArea.shoelace2 (P.rotate s) = HexArea.shoelace2 P := shoelace2_rotate P s
    rw [← h1, hrotP]
    exact shoelace2_clip_second a' b' c' tlP
  have hor : (0 < HexArea.shoelace2 [a', b', c'] ↔ 0 < HexArea.shoelace2 P) := by
    constructor
    · intro h
      have := horientP.mp h
      rw [hclipP]; linarith
    · intro h
      by_contra hcon
      push_neg at hcon
      have h2 : ¬ (0 < HexArea.shoelace2 (a' :: c' :: tlP)) := fun hh =>
        absurd (horientP.mpr hh) (by linarith)
      push_neg at h2
      rw [hclipP] at h
      linarith
  exact ear_interior_ptWind_ne_zero_via_clip P hP4 hPsimple s a' b' c' tlP hrotP hDP
    hemptyP hdiagP hor y hin

/-! ## 8. Perturbing a point of the open ear base into the ear interior -/

/-- **Moving from a relative-interior point of the ear base towards the tip enters
the open triangle.** -/
lemma inTriangleStrict_base_perturb (a b c x : ℂ) (hD : HexArea.cross (b - a) (c - b) ≠ 0)
    (hx : x ∈ openSegment ℝ a c) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    HexArea.inTriangleStrict a b c (((1 - t : ℝ) : ℂ) * x + ((t : ℝ) : ℂ) * b) := by
  obtain ⟨hA, hB, hC⟩ := HexArea.scaled_pos_of_mem_openSegment_ac a b c x hD hx
  set w : ℂ := ((1 - t : ℝ) : ℂ) * x + ((t : ℝ) : ℂ) * b with hw
  have e1 : HexArea.cross (b - a) (w - a) = (1 - t) * HexArea.cross (b - a) (x - a) := by
    rw [hw]
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e2 : HexArea.cross (c - b) (w - b) = (1 - t) * HexArea.cross (c - b) (x - b) := by
    rw [hw]
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have e3 : HexArea.cross (a - c) (w - c)
      = (1 - t) * HexArea.cross (a - c) (x - c) + t * HexArea.cross (b - a) (c - b) := by
    rw [hw]
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hC, mul_zero, zero_add] at e3
  rcases lt_or_gt_of_ne hD with hDneg | hDpos
  · right
    have hA' : HexArea.cross (b - a) (x - a) < 0 := by nlinarith
    have hB' : HexArea.cross (c - b) (x - b) < 0 := by nlinarith
    exact ⟨by rw [e1]; nlinarith, by rw [e2]; nlinarith, by rw [e3]; nlinarith⟩
  · left
    have hA' : 0 < HexArea.cross (b - a) (x - a) := by nlinarith
    have hB' : 0 < HexArea.cross (c - b) (x - b) := by nlinarith
    exact ⟨by rw [e1]; nlinarith, by rw [e2]; nlinarith, by rw [e3]; nlinarith⟩

/-- A point strictly inside a triangle lies on none of its three sides. -/
lemma inTriangleStrict_not_mem_sides (a b c y : ℂ) (h : HexArea.inTriangleStrict a b c y) :
    y ∉ segment ℝ a b ∧ y ∉ segment ℝ b c ∧ y ∉ segment ℝ c a := by
  have key : ∀ p q : ℂ, HexArea.cross (q - p) (y - p) ≠ 0 → y ∉ segment ℝ p q := by
    intro p q hne hmem
    exact hne (HexArea.cross_combo_segment p q y hmem)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨key a b (by linarith), key b c (by linarith), key c a (by linarith)⟩
  · exact ⟨key a b (by linarith), key b c (by linarith), key c a (by linarith)⟩

/-- The closed edges of a triangle. -/
lemma closedEdges_triple (a b c : ℂ) :
    closedEdges [a, b, c] = [(a, b), (b, c), (c, a)] := by
  have hr : ([a, b, c] : List ℂ).rotate 1 = [b, c, a] := by
    rw [List.rotate_cons_succ]; simp
  rw [closedEdges, hr]
  simp

/-- **A point strictly inside the ear triangle lies off every closed edge of the
polygon**, in the ear-rotation packaging (including the triangle case). -/
lemma ear_interior_off_closedEdges_of_rotation (P : List ℂ) (hPsimple : PolygonSimple P)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ) (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hDP : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (hdiagP : ∀ y ∈ tlP, y ∉ segment ℝ a' c')
    (y : ℂ) (hy : HexArea.inTriangleStrict a' b' c' y)
    (e : ℂ × ℂ) (he : e ∈ closedEdges P) :
    y ∉ segment ℝ e.1 e.2 := by
  by_cases htl : tlP = []
  · subst htl
    have he' : e ∈ closedEdges (P.rotate s) := (mem_closedEdges_rotate P s e).mpr he
    rw [hrotP, closedEdges_triple] at he'
    obtain ⟨h1, h2, h3⟩ := inTriangleStrict_not_mem_sides a' b' c' y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  · have hP4 : 4 ≤ P.length := by
      have hlen : (P.rotate s).length = tlP.length + 3 := by rw [hrotP]; simp
      have hlen' : P.length = tlP.length + 3 := by simpa using hlen
      have hpos : 0 < tlP.length := List.length_pos_iff.mpr htl
      omega
    exact ear_strict_interior_off_closedEdges P hP4 hPsimple s a' b' c' tlP hrotP hDP
      hemptyP hdiagP y hy e.1 e.2 he
