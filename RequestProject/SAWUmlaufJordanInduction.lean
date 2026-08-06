import Mathlib
import RequestProject.SAWUmlaufPolygon

/-!
# `SAWUmlaufJordanInduction` — closing the point-in-polygon induction

This file closes the last genuine loop of the polygonal Umlaufsatz.

`RequestProject.SAWUmlaufJordanStep` proves the two halves of the ear induction
step for the point-in-polygon dichotomy `PolyDichotomy`, *relative* to the
hypothesis `DichBelow N` (the dichotomy for all simple polygons with fewer than
`N` vertices), and `RequestProject.SAWUmlaufPolyMeisters` /
`RequestProject.SAWUmlaufPolygon` re-derive the whole Meisters ear-existence
chain relative to the same hypothesis.  Everything is therefore in place to run
the strong induction on the vertex count, which is what this file does:

* `polyDichotomy_rotate` — the dichotomy is a cyclic invariant;
* `polyDichotomy_triple` — the base case `|V| = 3` (both for a genuine triangle
  and for a degenerate, collinear one);
* `polyDichotomy_of_flat_second` — a flat vertex may be deleted without changing
  the dichotomy, which handles polygons that are not cyclically non-degenerate;
* `polyDichotomy_step` — the induction step: `DichBelow V.length → PolyDichotomy V`;
* `dichBelow_all` / `polygon_ptWind_dichotomy_final` — the dichotomy, unconditionally;
* `polygon_umlaufsatz_final` — the planar Umlaufsatz with no side hypothesis.

NOT a dead branch: this file is the top of the Umlaufsatz route and is imported
by `RequestProject.SAWUmlaufSignedArea`.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 1. The dichotomy is a cyclic invariant -/

/-- The point-in-polygon dichotomy transfers from a rotation back to the
polygon. -/
lemma polyDichotomy_rotate (V : List ℂ) (r : ℕ) (h : PolyDichotomy (V.rotate r)) :
    PolyDichotomy V := by
  intro x hx
  have hx' : ∀ e ∈ HexArea.cycleEdges (V.rotate r), x ∉ segment ℝ e.1 e.2 := by
    intro e he
    rw [HexArea.cycleEdges_eq_closedEdges, mem_closedEdges_rotate] at he
    exact hx e (by rwa [HexArea.cycleEdges_eq_closedEdges])
  have hw := h x hx'
  rwa [HexArea.ptWind_rotate, shoelace2_rotate] at hw

/-! ## 2. The base case: triples -/

/-- Three points with vanishing corner cross product are collinear, so one of
them lies on the closed segment spanned by the other two. -/
lemma collinear_triple_cases (a b c : ℂ) (h : HexArea.cross (b - a) (c - b) = 0) :
    b ∈ segment ℝ a c ∨ a ∈ segment ℝ b c ∨ c ∈ segment ℝ a b := by
  by_cases hu : b - a = 0
  · right; left
    have hba : a = b := by linear_combination -hu
    rw [hba]; exact left_mem_segment ℝ _ _
  obtain ⟨t, ht⟩ := HexArea.exists_real_smul_of_cross_zero (b - a) (c - b) hu h
  rw [Complex.real_smul] at ht
  rcases le_or_gt 0 t with htpos | htneg
  · -- `b` lies between `a` and `c`
    left
    have h1t : (0:ℝ) < 1 + t := by linarith
    have hne : ((1 + t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h1t
    refine mem_segment_of_param a c (1 / (1 + t)) (by positivity) ?_ b ?_
    · rw [div_le_one h1t]; linarith
    · have hca : c - a = ((1 + t : ℝ) : ℂ) * (b - a) := by
        push_cast; linear_combination ht
      rw [hca]
      push_cast
      have hne' : (1 + (t:ℂ)) ≠ 0 := by push_cast at hne; exact hne
      field_simp
  rcases le_or_gt t (-1) with htle | htgt
  · -- `a` lies between `b` and `c`
    right; left
    have ht0 : (0:ℝ) < -t := by linarith
    have hne : (t : ℂ) ≠ 0 := by
      have : t ≠ 0 := by linarith
      exact_mod_cast this
    refine mem_segment_of_param b c (1 / (-t)) (by positivity) ?_ a ?_
    · rw [div_le_one ht0]; linarith
    · rw [ht]
      push_cast
      field_simp
      ring
  · -- `c` lies between `a` and `b`
    right; right
    refine mem_segment_of_param a b (1 + t) (by linarith) (by linarith) c ?_
    push_cast
    linear_combination ht

/-- If `b` lies on `[a, c]`, the convex hull of `{a, b, c}` is contained in
`[a, c]`. -/
lemma convexHull_triple_subset (a b c : ℂ) (hb : b ∈ segment ℝ a c) :
    convexHull ℝ ((([a, b, c] : List ℂ).toFinset : Set ℂ)) ⊆ segment ℝ a c := by
  have hset : ((([a, b, c] : List ℂ).toFinset : Set ℂ)) = {a, b, c} := by ext w; simp
  rw [hset]
  refine convexHull_min ?_ (convex_segment a c)
  rintro v (rfl | rfl | rfl)
  · exact left_mem_segment ℝ _ _
  · exact hb
  · exact right_mem_segment ℝ _ _

/-- The three closed edges of the triple `[a, b, c]`. -/
lemma cycleEdges_triple (a b c : ℂ) :
    HexArea.cycleEdges [a, b, c] = [(a, b), (b, c), (c, a)] := by
  simp [HexArea.cycleEdges]

/-- **Base case of the point-in-polygon induction.**  A triple always satisfies
the dichotomy, degenerate or not. -/
lemma polyDichotomy_triple (a b c : ℂ) : PolyDichotomy [a, b, c] := by
  intro x hx
  rw [cycleEdges_triple] at hx
  have hab : x ∉ segment ℝ a b := hx (a, b) (by simp)
  have hbc : x ∉ segment ℝ b c := hx (b, c) (by simp)
  have hca : x ∉ segment ℝ c a := hx (c, a) (by simp)
  have hac : x ∉ segment ℝ a c := by rwa [segment_symm] at hca
  by_cases hD : HexArea.cross (b - a) (c - b) = 0
  · left
    refine HexArea.ptWind_zero_of_not_mem_convexHull x [a, b, c] ?_
    intro hmem
    rcases collinear_triple_cases a b c hD with hb | ha | hc
    · exact hac (convexHull_triple_subset a b c hb hmem)
    · refine hbc ?_
      have hset : ((([a, b, c] : List ℂ).toFinset : Set ℂ)) = {b, a, c} := by
        ext w; simp; tauto
      have : convexHull ℝ ((([a, b, c] : List ℂ).toFinset : Set ℂ)) ⊆ segment ℝ b c := by
        rw [hset]
        refine convexHull_min ?_ (convex_segment b c)
        rintro v (rfl | rfl | rfl)
        · exact left_mem_segment ℝ _ _
        · exact ha
        · exact right_mem_segment ℝ _ _
      exact this hmem
    · refine hab ?_
      have hset : ((([a, b, c] : List ℂ).toFinset : Set ℂ)) = {a, c, b} := by
        ext w; simp; tauto
      have : convexHull ℝ ((([a, b, c] : List ℂ).toFinset : Set ℂ)) ⊆ segment ℝ a b := by
        rw [hset]
        refine convexHull_min ?_ (convex_segment a b)
        rintro v (rfl | rfl | rfl)
        · exact left_mem_segment ℝ _ _
        · exact hc
        · exact right_mem_segment ℝ _ _
      exact this hmem
  · rcases HexArea.ptWind_triple_zero_or_strict a b c x hD hab hbc hac with hin | hz
    · exact Or.inr (HexArea.ptWind_triangle a b c x hin)
    · exact Or.inl hz

/-! ## 3. Deleting a flat vertex -/

/-- **The dichotomy is inherited across the removal of a flat vertex.**  If the
second vertex `b` lies on the diagonal `[a, c]`, the polygon and its clip have
the same winding numbers and the same signed area. -/
lemma polyDichotomy_of_flat_second (a b c : ℂ) (rest : List ℂ)
    (hflat : b ∈ segment ℝ a c) (hs : ℝ) (hbs : b - a = (hs : ℂ) * (c - a))
    (hC : PolyDichotomy (a :: c :: rest)) :
    PolyDichotomy (a :: b :: c :: rest) := by
  intro x hx
  have hxE : ∀ e ∈ closedEdges (a :: b :: c :: rest), x ∉ segment ℝ e.1 e.2 := by
    intro e he
    exact hx e (by rwa [HexArea.cycleEdges_eq_closedEdges])
  -- `x` is off the two ear sides, hence off the base
  have hab : x ∉ segment ℝ a b := by
    refine hxE (a, b) ?_
    have h := cycleEdges_cons_cons a b (c :: rest)
    rw [HexArea.cycleEdges_eq_closedEdges] at h
    rw [h]; exact List.mem_cons_self
  have hbc : x ∉ segment ℝ b c := by
    refine hxE (b, c) ?_
    simp [closedEdges, List.rotate_cons_succ]
  have hac : x ∉ segment ℝ a c := by
    intro hmem
    rcases segment_subset_union_of_mem a c b hflat hmem with h | h
    · exact hab h
    · exact hbc h
  -- the clip's edges are also avoided
  have hxC : ∀ e ∈ HexArea.cycleEdges (a :: c :: rest), x ∉ segment ℝ e.1 e.2 := by
    intro e he
    rw [HexArea.cycleEdges_eq_closedEdges] at he
    rcases closedEdges_clip_cases a b c rest e he with rfl | heM
    · exact hac
    · exact hxE e heM
  have hsplit := HexArea.ptWind_ear_clip a b c x rest hac
  have htri : HexArea.ptWind x [a, b, c] = 0 :=
    HexArea.ptWind_zero_of_not_mem_convexHull x [a, b, c]
      (fun hmem => hac (convexHull_triple_subset a b c hflat hmem))
  have harea : HexArea.shoelace2 (a :: b :: c :: rest) = HexArea.shoelace2 (a :: c :: rest) :=
    shoelace2_remove_flat_second a b c rest hs hbs
  rw [hsplit, htri, add_zero, harea]
  exact hC x hxC

/-! ## 4. The induction step -/

/-- **The ear induction step for the point-in-polygon dichotomy.**  If the
dichotomy holds for all simple polygons with strictly fewer vertices than `V`,
it holds for `V`. -/
theorem polyDichotomy_step (V : List ℂ) (h3 : 3 ≤ V.length)
    (hsimple : PolygonSimple V) (hIH : DichBelow V.length) :
    PolyDichotomy V := by
  by_cases h4 : 4 ≤ V.length
  · by_cases hnd : polyCycNondeg V
    · -- non-degenerate: clip an ear
      obtain ⟨r, a, b, c, rest, hrot, hD, hempty, hdiag, hor⟩ :=
        exists_front_ear_weak V.length hIH V h4 le_rfl hsimple hnd
      have hM : PolygonSimple (a :: b :: c :: rest) := by
        have := (PolygonSimple_rotate V r).2 hsimple
        rwa [hrot] at this
      have hlen : V.length = rest.length + 3 := by
        have : (V.rotate r).length = rest.length + 3 := by rw [hrot]; simp
        simpa using this
      have hrest : rest ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      have hca : c - a ≠ 0 := by
        refine sub_ne_zero.mpr (fun h => ?_)
        exact (List.nodup_cons.mp hM.1).1 (by simp [← h])
      have hCs : PolygonSimple (a :: c :: rest) :=
        PolygonSimple_clip a b c rest hM
          (diag_disjoint_of_empty_corner a b c rest hM hD hca hempty hdiag)
      have hdich : PolyDichotomy (a :: c :: rest) :=
        hIH (a :: c :: rest) (by simp; omega) (by simp; omega) hCs
      have hkey := keystone_below V.length hIH a b c rest (by omega) hrest hM hD
        hempty hdiag hor
      have := dichotomy_of_keystone_clip a b c rest hM hD hor hdich hkey
      rw [← hrot] at this
      exact polyDichotomy_rotate V r this
    · -- degenerate: delete a flat vertex
      obtain ⟨r, a, b, c, rest, hrot, hzero⟩ := exists_flat_cyclic_corner V h3 hnd
      have hM : PolygonSimple (a :: b :: c :: rest) := by
        have := (PolygonSimple_rotate V r).2 hsimple
        rwa [hrot] at this
      have hlen : V.length = rest.length + 3 := by
        have : (V.rotate r).length = rest.length + 3 := by rw [hrot]; simp
        simpa using this
      have hrest : rest ≠ [] := by
        intro h; rw [h] at hlen; simp at hlen; omega
      obtain ⟨s, hs0, hs1, hbs⟩ := flat_between_of_cross_zero a b c rest hrest hM hzero
      have hflat : b ∈ segment ℝ a c :=
        mem_segment_of_param a c s (le_of_lt hs0) (le_of_lt hs1) b hbs
      have hCs : PolygonSimple (a :: c :: rest) :=
        PolygonSimple_remove_flat_second a b c rest hM hflat
      have hdich : PolyDichotomy (a :: c :: rest) :=
        hIH (a :: c :: rest) (by simp; omega) (by simp; omega) hCs
      have := polyDichotomy_of_flat_second a b c rest hflat s hbs hdich
      rw [← hrot] at this
      exact polyDichotomy_rotate V r this
  · -- base case: a triple
    have hlen3 : V.length = 3 := by omega
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, V = [a, b, c] := by
      match V, hlen3 with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    exact polyDichotomy_triple a b c

/-! ## 5. The dichotomy, unconditionally -/

/-- **The point-in-polygon dichotomy holds for all simple polygons.** -/
theorem dichBelow_all : ∀ N : ℕ, DichBelow N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro Q hQN h3 hs
    refine polyDichotomy_step Q h3 hs ?_
    intro R hR h3R hsR
    exact ih Q.length hQN R hR h3R hsR

/-- **Point-in-polygon dichotomy (Jordan curve theorem for polygons).**  For a
simple closed polygon `V` and a point `x` on no closed edge of `V`, the winding
number of `V` around `x` is either `0` or `2π · sign (shoelace2 V)`. -/
theorem polygon_ptWind_dichotomy_final (V : List ℂ) (h3 : 3 ≤ V.length)
    (hsimple : PolygonSimple V) : PolyDichotomy V :=
  dichBelow_all (V.length + 1) V (by omega) h3 hsimple

/-- **The planar Umlaufsatz (Hopf's Umlaufsatz for polygons), unconditional
form.**  For a simple, cyclically non-degenerate closed polygon with at least
three vertices, the total exterior turning equals `2π · sign` of the signed
area. -/
theorem polygon_umlaufsatz_final (V : List ℂ) (hlen : 3 ≤ V.length)
    (hsimple : PolygonSimple V)
    (hnd : polyNondeg (V ++ [V[0]'(by omega), V[1]'(by omega)])) :
    polyWind (V ++ [V[0]'(by omega), V[1]'(by omega)]) =
      2 * Real.pi * (if 0 < HexArea.shoelace2 V then 1 else -1) :=
  polygon_umlaufsatz V.length (dichBelow_all V.length) V hlen le_rfl hsimple hnd

end
