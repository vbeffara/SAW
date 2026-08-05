import Mathlib
import RequestProject.SAWUmlaufPolyChord

/-!
# `SAWUmlaufPolygon`, part `SAWUmlaufPolyLift`

This file is one of the six parts the (formerly single, 7000-line) planar
polygon Umlaufsatz development was split into.  Parts are chained by imports
`SAWUmlaufPolyBase → SAWUmlaufPolyChord → SAWUmlaufPolyLift →
SAWUmlaufPolyEscape → SAWUmlaufPolyMeisters → SAWUmlaufPolygon`, and the last
part is imported by `RequestProject.SAWUmlaufSignedArea`, hence lies on the live
route to the main theorem.  See `SAWUmlaufPolyBase` for the overview.
-/

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

/-- **Empty-branch lift — the BOUNDARY subcase (now PROVED).**  Same hypotheses
    as `empty_branch_good_lift`, used to discharge the residual case where the
    ear returned by the induction hypothesis on the clip `a :: c :: rest` is
    *adjacent* to the `a–c` junction (its tail does not decompose as
    `s ++ a :: c :: t` with the junction interior).

    The combinatorial seam split `boundary_seam_split` shows that under
    `hnotint` the returned ear sits at one of exactly two seam positions —
    Case A (`c' = a`, `rest'.head? = some c`) or Case B (`a' = c`,
    `rest'.getLast? = some a`) — and in each case it lifts to a genuine
    consecutive triple of `V` (Case A: `(a', b', a)`; Case B: `(c, b', c')`) by
    re-inserting the apex `b` at the junction.

    **History.**  While `EmptyCornerData2` still demanded that the *clip corners*
    of the lifted ear be non-flat, this lemma had two irreducible `sorry`s: one
    of the two clip turns becomes an *apex turn* (`cross (a - a') (b - a)` in
    Case A, `cross (c - b) (c' - c)` in Case B) which can genuinely vanish in a
    "spike" configuration.  That demand is exactly what the pentagon of
    `RequestProject.SAWUmlaufFlatClipCounterexample` refutes; since
    `EmptyCornerData2` was corrected to its weak (true) form, the spike subcases
    are no longer obstructions and the branch is closed unconditionally by
    `boundary_lift_caseA_nonspike` / `boundary_lift_caseB_nonspike` (whose
    non-spike hypotheses were dropped for the same reason). -/
lemma empty_branch_boundary_lift (V : List ℂ) (hlen : 5 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ) (p q : ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpl : HexArea.cross (c - a) (p - a) ≠ 0)
    (hql : HexArea.cross (c - a) (q - a) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hbf : b = z1 ∨ b = z2)
    (a' b' c' p' q' : ℂ) (rest' : List ℂ) (r' : ℕ)
    (hrot' : (a :: c :: rest).rotate r' = a' :: b' :: c' :: rest')
    (hb'a : b' ≠ a) (hb'c : b' ≠ c)
    (hp'M : rest'.getLast? = some p') (hq'M : rest'.head? = some q')
    (hempty' : ∀ x ∈ rest', ¬ HexArea.inTriangleStrict a' b' c' x)
    (hdiag' : ∀ x ∈ rest', x ∉ segment ℝ a' c')
    (horient' : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: rest')))
    (hnotint : ¬ ∃ s t, rest' = s ++ a :: c :: t) :
    EmptyCornerData2 V z1 z2 := by
  -- Derive the combinatorial side facts (mirrors `empty_branch_good_lift`).
  obtain ⟨ha'M, hb'M, hc'M, hrest'M⟩ :=
    rotate_cons3_mem (a :: c :: rest) a' b' c' rest' r' hrot'
  obtain ⟨hac, hanr, hbnr, hba, hbc, hcnr, hrnd⟩ :
      a ≠ c ∧ a ∉ rest ∧ b ∉ rest ∧ b ≠ a ∧ b ≠ c ∧ c ∉ rest ∧ rest.Nodup := by
    have hrot_nodup : List.Nodup (V.rotate r) := List.nodup_rotate.mpr hsimple.1
    rw [hrot] at hrot_nodup
    simp only [List.nodup_cons, List.mem_cons] at hrot_nodup
    grind +qlia
  have hclipnd : (a :: c :: rest).Nodup := by
    simp only [List.nodup_cons, List.mem_cons]; grind
  have hrest_len : 2 ≤ rest.length := by
    have hlenrot := congrArg List.length hrot; simp at hlenrot; omega
  have hclipsub : ∀ x ∈ (a :: c :: rest), x ∈ V := by
    intro x hx
    have hx' : x ∈ a :: b :: c :: rest := by
      simp only [List.mem_cons] at hx ⊢; tauto
    rw [← hrot] at hx'; exact (List.mem_rotate).mp hx'
  have ha'V : a' ∈ V := hclipsub a' ha'M
  have hb'V : b' ∈ V := hclipsub b' hb'M
  have hc'V : c' ∈ V := hclipsub c' hc'M
  have hb'rest : b' ∈ rest := by
    rcases List.mem_cons.mp hb'M with h | h
    · exact absurd h hb'a
    · rcases List.mem_cons.mp h with h2 | h2
      · exact absurd h2 hb'c
      · exact h2
  have ha'b : b ≠ a' := by
    rcases List.mem_cons.mp ha'M with h | h
    · exact fun hb => hba (hb.trans h)
    · rcases List.mem_cons.mp h with h2 | h2
      · exact fun hb => hbc (hb.trans h2)
      · exact fun hb => hbnr (hb ▸ h2)
  have hc'b : b ≠ c' := by
    rcases List.mem_cons.mp hc'M with h | h
    · exact fun hb => hba (hb.trans h)
    · rcases List.mem_cons.mp h with h2 | h2
      · exact fun hb => hbc (hb.trans h2)
      · exact fun hb => hbnr (hb ▸ h2)
  have hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2 := by
    have := forbidden_subset_corner V r a b c rest hsimple hrot z1 z2 hadj hbf
    simp_all +decide [List.nodup_cons]
    grind +ring
  -- Split the seam into the two boundary configurations.
  rcases boundary_seam_split a c rest a' b' c' rest' r' hclipnd hrest_len hrot' hb'a hb'c hnotint
    with ⟨hcA1, hcA2⟩ | ⟨hcB1, hcB2⟩
  · -- **Case A** : `c' = a`, `rest'.head? = some c`.
    subst c'
    obtain ⟨rest'', rfl⟩ : ∃ rest'', rest' = c :: rest'' :=
      List.head?_eq_some_iff.mp hcA2
    exact boundary_lift_caseA_nonspike V z1 z2 a b c rest r hrot hac hanr hba hbconv hbseg
      horient hzrest a' b' p' rest'' r' hrot' hb'rest ha'V hb'V ha'b hp'M hempty' hdiag'
      horient'
  · -- **Case B** : `a' = c`, `rest'.getLast? = some a`.
    subst a'
    obtain ⟨s', rfl⟩ : ∃ s', rest' = s' ++ [a] :=
      List.getLast?_eq_some_iff.mp hcB2
    exact boundary_lift_caseB_nonspike V z1 z2 a b c rest r hrot hac hanr hba hbc hbconv hbseg
      horient hzrest b' c' q' s' r' hrot' hb'rest hc'V hb'V hc'b hq'M hempty' hdiag'
      horient'

/-- **Empty-branch lift — the "good diagonal" subcase (PROVED modulo the boundary
    subcase).**
    This is the half of `meisters_reduction_empty2`'s non-clean case in which the
    clip diagonal `a–c` is *clean*: both clip neighbours `p, q` lie off the line
    `a–c` (`hpl`, `hql`), no far vertex sits on the closed diagonal (`hdiag`),
    and the ear orientation matches the clip (`horient`).  Since the overall
    branch is non-clean while the diagonal is clean, the only obstruction is that
    the convex apex `b` coincides with a forbidden vertex (`hbf : b = z1 ∨
    b = z2`).  We recurse via `IH2` on the strictly-shorter clip `a :: c :: rest`
    (simple and non-degenerate by `clip_simple_nondeg_of_empty`) forbidding the
    clip diagonal `{a, c}` (a genuine cyclic edge of the clip), and lift the
    returned ear — whose tip lies in `rest`, hence avoids `a`, `c`, and (by
    Nodup) `b` — back to `V`.  Because `b`'s only cyclic neighbours in `V` are
    `a` and `c`, the lifted tip avoids both forbidden vertices `z1, z2` (one is
    `b`, the other a neighbour of `b`, i.e. in `{a, c}`).  The orientation /
    diagonal data transfer using `horient` and `hbconv`.

    **Status: proved.**  This lemma is now sorry-free: it recurses on the clip
    via `IH2`, then `by_cases` on whether the returned ear's tail decomposes as
    `s ++ a :: c :: t` (the `a–c` junction interior).  The *interior* subcase is
    discharged by the fully-proved `empty_branch_interior_lift` (the list-surgery
    rotation lift plus the orientation-sign transfer); the *boundary* subcase
    (ear adjacent to the junction) is dispatched to `empty_branch_boundary_lift`,
    which carries the single genuine remaining Jordan-content `sorry` of the
    empty branch.  Consumed by `meisters_reduction_empty2` (good-diagonal
    subcase). -/
lemma empty_branch_good_lift (V : List ℂ) (hlen : 5 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ) (p q : ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpl : HexArea.cross (c - a) (p - a) ≠ 0)
    (hql : HexArea.cross (c - a) (q - a) ≠ 0)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hbf : b = z1 ∨ b = z2) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨hac, hanr, hbnr, hbnea, hbnec⟩ : a ≠ c ∧ a ∉ rest ∧ b ∉ rest ∧ b ≠ a ∧ b ≠ c := by
    have hrot_nodup : List.Nodup (V.rotate r) := by
      exact List.nodup_rotate.mpr hsimple.1;
    grind +qlia;
  have hABCne : HexArea.cross (b - a) (c - b) ≠ 0 := by
    convert polyCycNondeg_rotate_head V a b c rest r ( by omega ) hnd hrot using 1
  have hlenrot := congrArg List.length hrot
  simp at hlenrot
  have hMs : PolygonSimple (a :: c :: rest) := by
    apply (clip_simple_nondeg_of_empty a b c p q rest hp hq (hrot ▸ (PolygonSimple_rotate V r).2 hsimple) (hrot ▸ (polyCycNondeg_rotate V r (by omega)).mpr hnd) hABCne (sub_ne_zero_of_ne hac.symm) hempty hdiag (HexArea.clip_turn_at_a_ne_zero a c p hpl) (HexArea.clip_turn_at_c_ne_zero a c q hql)).left
  have hMn : polyCycNondeg (a :: c :: rest) := by
    apply (clip_simple_nondeg_of_empty a b c p q rest hp hq (by
    exact hrot ▸ ( PolygonSimple_rotate V r ).2 hsimple) (by
    convert hrot ▸ ( polyCycNondeg_rotate V r ( by linarith ) ) |>.mpr hnd using 1) hABCne (sub_ne_zero_of_ne hac.symm) hempty hdiag (HexArea.clip_turn_at_a_ne_zero a c p hpl) (HexArea.clip_turn_at_c_ne_zero a c q hql)).right
  have hMlen : 4 ≤ (a :: c :: rest).length := by
    grind
  have hadjM : IsCycEdge (a :: c :: rest) a c := by
    unfold IsCycEdge; simp +decide [ closedEdges ] ;
  obtain ⟨r', a', b', c', p'M, q'M, rest', hrot', hb'a, hb'c, hp'M, hq'M, hempty', hdiag', horient'⟩ := IH2 (a :: c :: rest) (by simp; omega) hMlen hMs hMn a c (Or.inr hadjM);
  obtain ⟨ha'M, hb'M, hc'M, hrest'M⟩ := rotate_cons3_mem (a :: c :: rest) a' b' c' rest' r' hrot';
  obtain ⟨hb'rest, ha'V, hb'V, hc'V⟩ : b' ∈ rest ∧ a' ∈ V ∧ b' ∈ V ∧ c' ∈ V := by
    replace hrot := congr_arg List.toFinset hrot; rw [ Finset.ext_iff ] at hrot; have := hrot a; have := hrot b; have := hrot c; have := hrot b'; have := hrot c'; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
    grind +qlia;
  have ha'b : b ≠ a' := by
    grind +ring
  have hc'b : b ≠ c' := by
    grind +ring
  have hA'ne : HexArea.cross (b' - a') (c' - b') ≠ 0 := by
    convert polyCycNondeg_rotate_head ( a :: c :: rest ) a' b' c' rest' r' ( by simp; omega ) hMn hrot' using 1
  have hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2 := by
    have := forbidden_subset_corner V r a b c rest hsimple hrot z1 z2 hadj hbf;
    have := hMs.1; simp_all +decide [ List.nodup_cons ] ;
    grind +ring
  generalize_proofs at *; (
  by_cases hnotint : ∃ s t, rest' = s ++ a :: c :: t;
  · obtain ⟨ s, t, rfl ⟩ := hnotint;
    apply empty_branch_interior_lift V z1 z2 a b c rest r hrot hac hanr hbconv hbseg horient hABCne hzrest a' b' c' p'M q'M s t r' hrot' hb'rest ha'V hb'V hc'V ha'b hc'b hA'ne hp'M hq'M hempty' hdiag' horient';
  · exact empty_branch_boundary_lift V ( by omega ) hsimple hnd z1 z2 hadj IH2 r a b c rest p q hrot hbmem hbconv hbseg hp hq hpl hql hempty hdiag horient hbf a' b' c' p'M q'M rest' r' hrot' hb'a hb'c hp'M hq'M hempty' hdiag' horient' hnotint)

/-- **Edge-forbidden selection (pure finite logic).**  If `x ≠ y` and the
    *ordered* pair `(x, y)` and its reverse `(y, x)` are both absent from the
    cyclic edges of `V` (i.e. `{x, y}` is a diagonal, not an edge), then any
    forbidden pair `z1, z2` that is equal or a cyclic edge must miss at least
    one of `x, y`.  This is the combinatorial heart of the quadrilateral
    two-ears base case: the two ears sit at the *diagonal* pair, which no edge
    can cover.  Consumed by `meisters_reduction_quad2`. -/
lemma forbidden_avoids_one (V : List ℂ) (x y z1 z2 : ℂ) (hxy : x ≠ y)
    (hxy1 : (x, y) ∉ closedEdges V) (hxy2 : (y, x) ∉ closedEdges V)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2) :
    (x ≠ z1 ∧ x ≠ z2) ∨ (y ≠ z1 ∧ y ≠ z2) := by
  rcases hadj with rfl | hedge
  · by_cases hx : x = z1
    · exact Or.inr ⟨fun h => hxy ((h.trans hx.symm).symm),
        fun h => hxy ((h.trans hx.symm).symm)⟩
    · exact Or.inl ⟨hx, hx⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- after push_neg: `h1 : x ≠ z1 → x = z2`, `h2 : y ≠ z1 → y = z2`.
    have hx : x = z1 ∨ x = z2 := by
      by_contra hh; push_neg at hh; exact hh.2 (h1 hh.1)
    have hy : y = z1 ∨ y = z2 := by
      by_contra hh; push_neg at hh; exact hh.2 (h2 hh.1)
    rcases hedge with he | he
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        first
        | (exfalso; exact hxy (hx.trans hy.symm))
        | (subst hx; subst hy; exact hxy1 he)
        | (subst hx; subst hy; exact hxy2 he)
    · rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        first
        | (exfalso; exact hxy (hx.trans hy.symm))
        | (subst hx; subst hy; exact hxy2 he)
        | (subst hx; subst hy; exact hxy1 he)

/-
**Ear at `b` of a quadrilateral (rotation 0).**  When `a–c` is an interior
    diagonal (`H`), the vertex `b` is an empty ear; if it avoids `z1, z2` the
    `EmptyCornerData2` is the rotation-0 package.  Mirrors the `H`-left,
    `b ≠ z` branch of `meisters_reduction_quad`.
-/
lemma quad_ear_at_b (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (c - a) (b - a) * HexArea.cross (c - a) (d - a) < 0)
    (hbz1 : b ≠ z1) (hbz2 : b ≠ z2) :
    EmptyCornerData2Strong [a, b, c, d] z1 z2 := by
  refine' ⟨ 0, a, b, c, d, d, [ d ], _, _, _, _, _ ⟩ <;> norm_num;
  · assumption;
  · assumption;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
      grind;
    · contrapose! H;
      have := HexArea.inTriangleStrict_apex_sameSide a b c d H;
      linarith;
    · exact not_mem_segment_of_cross_ne a c d ( by aesop );
    · unfold HexArea.shoelace2 at *; simp_all +decide [ HexArea.cross ] ;
      constructor <;> intro <;> nlinarith

/-
**Ear at `d` of a quadrilateral (rotation 2).**  The opposite ear of the
    `a–c` interior-diagonal case.  Mirrors the `H`-left, `b = z` branch of
    `meisters_reduction_quad` (which produces the opposite ear `d`).
-/
lemma quad_ear_at_d (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (c - a) (b - a) * HexArea.cross (c - a) (d - a) < 0)
    (hdz1 : d ≠ z1) (hdz2 : d ≠ z2) :
    EmptyCornerData2Strong [a, b, c, d] z1 z2 := by
  refine' ⟨ 2, c, d, a, b, b, [ b ], _, _, _, _, _ ⟩ <;> norm_num at *;
  · assumption;
  · assumption;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · contrapose! hbc; simp_all +decide [ HexArea.cross ] ;
      grind;
    · contrapose! H; simp_all +decide [ HexArea.cross ] ;
      grind +qlia;
    · unfold HexArea.inTriangleStrict; norm_num [ Complex.ext_iff ] ;
      unfold HexArea.cross at * ; norm_num [ Complex.ext_iff ] at * ; constructor <;> intros <;> nlinarith;
    · contrapose! H; simp_all +decide [ HexArea.cross ] ;
      rw [ segment_eq_image ] at H ; obtain ⟨ θ, hθ, rfl ⟩ := H ; norm_num [ Complex.ext_iff ] at * ; ring_nf at * ; norm_num at *;
    · unfold HexArea.shoelace2 HexArea.cross at * ; norm_num [ Complex.ext_iff ] at *;
      unfold HexArea.cross ;
      constructor <;> intro <;> nlinarith

/-
**Ear at `c` of a quadrilateral (rotation 1).**  When `b–d` is an interior
    diagonal (`H`), `c` is an empty ear.  Mirrors the `H`-right, `c ≠ z` branch
    of `meisters_reduction_quad`.
-/
lemma quad_ear_at_c (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (d - b) (a - b) * HexArea.cross (d - b) (c - b) < 0)
    (hcz1 : c ≠ z1) (hcz2 : c ≠ z2) :
    EmptyCornerData2Strong [a, b, c, d] z1 z2 := by
  refine' ⟨ 1, b, c, d, a, a, [ a ], _, _, _, _, _ ⟩ <;> simp_all +decide [ EmptyCornerData2Strong ];
  refine' ⟨ _, _, _, _, _ ⟩;
  · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
    grind +qlia;
  · unfold HexArea.cross at *; simp_all +decide [ Complex.ext_iff ] ;
    grind;
  · unfold HexArea.inTriangleStrict;
    unfold HexArea.cross at * ; norm_num [ Complex.ext_iff ] at * ;
    constructor <;> intros <;> nlinarith;
  · rw [ segment_eq_image ] ; contrapose! H ; simp_all +decide [ HexArea.cross ];
    obtain ⟨ x, hx, rfl ⟩ := H; norm_num [ Complex.ext_iff ] ; ring_nf;
    norm_num;
  · unfold HexArea.shoelace2; simp +decide [ HexArea.cross ] ;
    unfold HexArea.cross at * ; norm_num [ Complex.ext_iff ] at * ; constructor <;> intro <;> nlinarith

/-
**Ear at `a` of a quadrilateral (rotation 3).**  The opposite ear of the
    `b–d` interior-diagonal case.  Mirrors the `H`-right, `c = z` branch of
    `meisters_reduction_quad` (which produces the opposite ear `a`).
-/
lemma quad_ear_at_a (a b c d z1 z2 : ℂ)
    (hab : HexArea.cross (b - a) (c - b) ≠ 0)
    (hbc : HexArea.cross (c - b) (d - c) ≠ 0)
    (hcd : HexArea.cross (d - c) (a - d) ≠ 0)
    (hda : HexArea.cross (a - d) (b - a) ≠ 0)
    (H : HexArea.cross (d - b) (a - b) * HexArea.cross (d - b) (c - b) < 0)
    (haz1 : a ≠ z1) (haz2 : a ≠ z2) :
    EmptyCornerData2Strong [a, b, c, d] z1 z2 := by
  use 3, d, a, b, c, c, [c];
  simp_all +decide [ HexArea.cross, HexArea.shoelace2, HexArea.inTriangleStrict ];
  refine' ⟨ _, _, _, _, _ ⟩;
  · grind;
  · grind;
  · constructor <;> intros <;> nlinarith;
  · contrapose! H;
    obtain ⟨ u, v, hu, hv, huv, rfl ⟩ := H;
    norm_num [ show u = 1 - v by linarith ] at *;
    nlinarith [ mul_nonneg hv ( sq_nonneg ( d.re - b.re ) ), mul_nonneg hv ( sq_nonneg ( d.im - b.im ) ) ];
  · constructor <;> intro <;> nlinarith

/-- **The quadrilateral base case in the two-forbidden form.**  A simple,
    non-degenerate quadrilateral, together with a forbidden pair `z1, z2` that
    is either equal or a genuine cyclic edge, has an empty corner whose tip
    avoids both.  The two ears of a quadrilateral are at *opposite* corners
    (non-adjacent), so an edge — whose endpoints are adjacent — can never
    contain both ear tips; hence at least one ear survives.  Genuine finite
    two-ears content; consumed by `meisters_reduction2`.

    **Status: `sorry`.**  True statement (the quadrilateral two-ears fact); the
    finite case analysis mirrors `meisters_reduction_quad` (which already dodges
    a single forbidden vertex to the opposite ear) but must dodge an entire
    edge.  Recorded partial progress toward the Umlaufsatz. -/
lemma meisters_reduction_quad2 (V : List ℂ) (h4 : V.length = 4)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, V = [a, b, c, d] := by
    rcases V with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | t⟩⟩⟩⟩ <;> simp_all
  -- The four consecutive-triple non-degeneracies.
  obtain ⟨hab, hbc, hcd, hda⟩ : HexArea.cross (b - a) (c - b) ≠ 0 ∧
      HexArea.cross (c - b) (d - c) ≠ 0 ∧ HexArea.cross (d - c) (a - d) ≠ 0 ∧
      HexArea.cross (a - d) (b - a) ≠ 0 := by
    unfold polyCycNondeg at hnd; simp_all +decide [polyNondeg]
  -- Vertex distinctness from `Nodup`.
  have hnd4 := hsimple.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil] at hnd4
  have hbd : b ≠ d := by tauto
  have hac : a ≠ c := by tauto
  have had : a ≠ d := by tauto
  have hbc' : b ≠ c := by tauto
  -- The two opposite-edge disjointnesses.
  obtain ⟨hdisj1, hdisj2⟩ : Disjoint (segment ℝ a b) (segment ℝ c d) ∧
      Disjoint (segment ℝ b c) (segment ℝ d a) := by
    have := hsimple.2; simp_all +decide [closedEdges]; grind +locals
  -- The two diagonals are not cyclic edges.
  have hCE : closedEdges [a, b, c, d] = [(a, b), (b, c), (c, d), (d, a)] := by
    simp [closedEdges, List.rotate]
  have hbd1 : (b, d) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  have hbd2 : (d, b) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  have hac1 : (a, c) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  have hac2 : (c, a) ∉ closedEdges [a, b, c, d] := by
    rw [hCE]; simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]
    push_neg; tauto
  -- One diagonal is interior; its two endpoints are the two opposite ears.
  rcases quad_diagonal_interior a b c d hab hbc hcd hda hdisj1 hdisj2 with H | H
  · -- `a–c` interior: ears at `b` and `d`.
    rcases forbidden_avoids_one [a, b, c, d] b d z1 z2 hbd hbd1 hbd2 hadj with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact EmptyCornerData2_of_strong _ _ _ (quad_ear_at_b a b c d z1 z2 hab hbc hcd hda H h1 h2)
    · exact EmptyCornerData2_of_strong _ _ _ (quad_ear_at_d a b c d z1 z2 hab hbc hcd hda H h1 h2)
  · -- `b–d` interior: ears at `a` and `c`.
    rcases forbidden_avoids_one [a, b, c, d] a c z1 z2 hac hac1 hac2 hadj with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact EmptyCornerData2_of_strong _ _ _ (quad_ear_at_a a b c d z1 z2 hab hbc hcd hda H h1 h2)
    · exact EmptyCornerData2_of_strong _ _ _ (quad_ear_at_c a b c d z1 z2 hab hbc hcd hda H h1 h2)

/-
**Interior-split simplicity brick.**  Under the interior-branch hypotheses
    (the chord `b–w` is a genuine diagonal, supplied by
    `interior_chord_is_diagonal`), the two pieces of the `b`-rooted cycle
    `W := b :: c :: rest ++ [a]` cut along `b–w` are both `PolygonSimple`.  Here
    `k` is the index of `w` in `W`, satisfying `2 ≤ k` and `k + 2 ≤ W.length`
    (so both pieces are strictly shorter than `W`).  Pure assembly of
    `interior_chord_is_diagonal` with the banked combinatorial simplicity bricks
    `chordLeft_PolygonSimple` / `chordRight_PolygonSimple` and the rotation
    toolkit (`PolygonSimple_rotate`, `mem_closedEdges_rotate`).  Preparation for
    `meisters_reduction_interior2`.
-/
lemma interior_split_simple (a b c w : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hwrest : w ∈ rest)
    (hwin : HexArea.inTriangleStrict a b c w)
    (hwmax : ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) * HexArea.cross (c - a) (b - a)
          ≤ HexArea.cross (c - a) (w - a) * HexArea.cross (c - a) (b - a)) :
    ∃ k : ℕ, 2 ≤ k ∧ k + 2 ≤ (b :: c :: rest ++ [a]).length ∧
      (b :: c :: rest ++ [a]).head? = some b ∧
      (b :: c :: rest ++ [a])[k]? = some w ∧
      PolygonSimple (HexArea.chordLeft (b :: c :: rest ++ [a]) k) ∧
      PolygonSimple (HexArea.chordRight (b :: c :: rest ++ [a]) k) := by
  -- Write `rest` as `s ++ w :: t`, and set `k := 2 + s.length`.
  obtain ⟨s, t, hrest⟩ : ∃ s t, rest = s ++ w :: t := List.append_of_mem hwrest
  set k := 2 + s.length with hk_def;
  refine' ⟨ k, _, _, _, _, _ ⟩;
  · exact Nat.le_add_right _ _;
  · grind;
  · rfl;
  · simp +arith +decide [ hk_def, hrest ];
  · have hclear : ∀ e ∈ closedEdges (b :: c :: rest ++ [a]), b ≠ e.1 → b ≠ e.2 → w ≠ e.1 → w ≠ e.2 → Disjoint (segment ℝ b w) (segment ℝ e.1 e.2) := by
      convert interior_chord_is_diagonal a b c w rest hsimple hndtri hwrest hwin hwmax using 1;
      rw [ show b :: c :: rest ++ [ a ] = ( a :: b :: c :: rest ).rotate 1 from ?_, mem_closedEdges_rotate ];
      simp +decide [ List.rotate ];
    refine' ⟨ _, _ ⟩;
    · apply HexArea.chordLeft_PolygonSimple;
      any_goals tauto;
      · exact Nat.le_add_right _ _;
      · grind;
      · convert PolygonSimple_rotate ( a :: b :: c :: rest ) 1 |>.2 hsimple using 1;
      · simp +arith +decide [ hk_def, hrest ];
      · intro e he hw1 hw2 hb1 hb2; specialize hclear e; simp_all +decide [ segment_symm ] ;
        exact hclear <| HexArea.mem_closedEdges_of_mem_pathEdges _ _ <| HexArea.mem_pathEdges_take _ _ _ he;
    · apply HexArea.chordRight_PolygonSimple;
      any_goals tauto;
      · grind;
      · simp +arith +decide [ hk_def, hrest ];
      · convert PolygonSimple_rotate _ 1 |>.2 hsimple using 1;
      · grind;
      · intro e he hb1 hb2 hw1 hw2; specialize hclear e; simp_all +decide [ HexArea.pathEdges_chordRight_mem_closedEdges ] ;
        exact hclear ( HexArea.pathEdges_chordRight_mem_closedEdges _ _ ( by simp +arith +decide [ HexArea.chordRight ] ) _ he )

/-
**Interior-split non-degeneracy brick.**  Companion to `interior_split_simple`:
    given the two *genuine* seam clearances at the cut endpoint `w` — the diagonal
    `b–w` is collinear with neither edge of `V` incident to `w` (`hseamL` for the
    predecessor edge `prev–w`, `hseamR` for the successor edge `w–succ`) — both
    pieces `chordLeft`/`chordRight` of the `b`-rooted cycle
    `W := b :: c :: rest ++ [a]` cut along `b–w` are cyclically non-degenerate.
    The other two seam corners (at the apex `b`) are automatic from `w` lying
    strictly inside the corner triangle `a,b,c` (so `w` is off lines `b–c` and
    `a–b`).  Together with `interior_split_simple` this shows both pieces are
    `PolygonSimple` *and* `polyCycNondeg` *and* strictly shorter — fully ready for
    the `IH2` recursion — leaving the interior branch's only remaining content the
    two genuine seam clearances `hseamL`/`hseamR` plus the ear lift.  Preparation
    for `meisters_reduction_interior2`.
-/
lemma interior_split_nondeg (a b c w prev succ : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (hprev : (b :: c :: rest ++ [a])[k-1]? = some prev)
    (hsucc : (b :: c :: rest ++ [a])[k+1]? = some succ)
    (hseamL : HexArea.cross (w - prev) (b - w) ≠ 0)
    (hseamR : HexArea.cross (w - b) (succ - w) ≠ 0) :
    polyCycNondeg (HexArea.chordLeft (b :: c :: rest ++ [a]) k) ∧
    polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) k) := by
  obtain ⟨hwac, hwbc⟩ : HexArea.cross (b - a) (w - a) ≠ 0 ∧ HexArea.cross (c - b) (w - b) ≠ 0 := by
    cases hwin <;> aesop;
  constructor;
  · apply_rules [ HexArea.chordLeft_polyCycNondeg ];
    · linarith;
    · convert polyCycNondeg_rotate1 ( a :: b :: c :: rest ) _;
      · simp +decide [ List.rotate ];
        grind +suggestions;
      · simp +arith +decide;
    · grind +suggestions;
  · apply HexArea.chordRight_polyCycNondeg (b :: c :: rest ++ [a]) k b w succ a;
    any_goals omega;
    · convert polyCycNondeg_rotate1 ( a :: b :: c :: rest ) _;
      · simp +decide [ List.rotate ];
        grind +suggestions;
      · simp +arith +decide;
    · simp +decide;
    · simp +decide [ List.getElem?_append ];
    · convert hwac using 1;
      unfold HexArea.cross; ring;
      norm_num [ Complex.ext_iff ] ; ring

/-- **Interior-split non-degeneracy, LEFT piece only (single-seam form).**
    The `chordLeft` piece's seam corner at the cut endpoint `w` is the triple
    `(prev, w, b)`, so the LEFT piece is cyclically non-degenerate from the
    SINGLE seam clearance `hseamL : cross (w - prev) (b - w) ≠ 0` (the other
    new corner, at the apex `b`, is automatic from `w` lying strictly inside the
    corner triangle).  Specialization of `interior_split_nondeg`; combined with
    `seam_one_nonflat` it makes the non-flat piece directly consumable by the
    interior branch.  Preparation for `meisters_reduction_interior2`. -/
lemma interior_split_nondeg_left (a b c w prev : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (hprev : (b :: c :: rest ++ [a])[k-1]? = some prev)
    (hseamL : HexArea.cross (w - prev) (b - w) ≠ 0) :
    polyCycNondeg (HexArea.chordLeft (b :: c :: rest ++ [a]) k) := by
  obtain ⟨hwac, hwbc⟩ : HexArea.cross (b - a) (w - a) ≠ 0 ∧ HexArea.cross (c - b) (w - b) ≠ 0 := by
    cases hwin <;> aesop
  apply_rules [ HexArea.chordLeft_polyCycNondeg ]
  · linarith
  · convert polyCycNondeg_rotate1 ( a :: b :: c :: rest ) _
    · simp +decide [ List.rotate ]
      grind +suggestions
    · simp +arith +decide
  · grind +suggestions

/-- **Interior-split non-degeneracy, RIGHT piece only (single-seam form).**
    Companion of `interior_split_nondeg_left`: the `chordRight` piece's seam
    corner at `w` is the triple `(b, w, succ)`, so the RIGHT piece is cyclically
    non-degenerate from the SINGLE seam clearance
    `hseamR : cross (w - b) (succ - w) ≠ 0`.  Specialization of
    `interior_split_nondeg`.  Preparation for `meisters_reduction_interior2`. -/
lemma interior_split_nondeg_right (a b c w succ : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (hsucc : (b :: c :: rest ++ [a])[k+1]? = some succ)
    (hseamR : HexArea.cross (w - b) (succ - w) ≠ 0) :
    polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) k) := by
  obtain ⟨hwac, hwbc⟩ : HexArea.cross (b - a) (w - a) ≠ 0 ∧ HexArea.cross (c - b) (w - b) ≠ 0 := by
    cases hwin <;> aesop
  apply HexArea.chordRight_polyCycNondeg (b :: c :: rest ++ [a]) k b w succ a
  any_goals omega
  · convert polyCycNondeg_rotate1 ( a :: b :: c :: rest ) _
    · simp +decide [ List.rotate ]
      grind +suggestions
    · simp +arith +decide
  · simp +decide
  · simp +decide [ List.getElem?_append ]
  · convert hwac using 1
    unfold HexArea.cross; ring
    norm_num [ Complex.ext_iff ] ; ring

/-- **The cut diagonal `{v0, vk}` is a cyclic edge of the LEFT chord piece.**
    Preparation for `meisters_reduction_interior2`: when the interior branch
    recurses via `IH2` on `chordLeft V k`, the forbidden pair it must hand to
    `IH2` is the cut diagonal `v0 = V[0]` / `vk = V[k]`, and this pair is a
    genuine cyclic edge of the piece (its closing chord), so the recursion stays
    inside the `IsCycEdge` invariant.  Sorry-free; consumed by
    `meisters_reduction_interior2`. -/
lemma chordLeft_cut_isCycEdge (V : List ℂ) (k : ℕ) (v0 vk : ℂ)
    (hk : k < V.length) (hhead : V.head? = some v0) (hvk : V[k]? = some vk) :
    IsCycEdge (HexArea.chordLeft V k) vk v0 := by
  have hh : (HexArea.chordLeft V k).head? = some v0 := by
    rw [HexArea.chordLeft_head]; exact hhead
  have hl : (HexArea.chordLeft V k).getLast? = some vk := by
    rw [HexArea.chordLeft_getLast V k hk]; exact hvk
  left
  rw [HexArea.closedEdges_eq_pathEdges (HexArea.chordLeft V k) v0 vk hh hl]
  simp

/-- **The cut diagonal `{v0, vk}` is a cyclic edge of the RIGHT chord piece.**
    Companion of `chordLeft_cut_isCycEdge` for `chordRight V k`.  Sorry-free;
    consumed by `meisters_reduction_interior2`. -/
lemma chordRight_cut_isCycEdge (V : List ℂ) (k : ℕ) (v0 vk : ℂ)
    (hk : k < V.length) (hV : V ≠ []) (hhead : V.head? = some v0)
    (hvk : V[k]? = some vk) :
    IsCycEdge (HexArea.chordRight V k) vk v0 := by
  have hh : (HexArea.chordRight V k).head? = some vk := by
    rw [HexArea.chordRight_head V k hk]; exact hvk
  have hl : (HexArea.chordRight V k).getLast? = some v0 := by
    rw [HexArea.chordRight_getLast V k hV hk]; exact hhead
  right
  rw [HexArea.closedEdges_eq_pathEdges (HexArea.chordRight V k) vk v0 hh hl]
  simp

/-- **Seam collinearity chain (interior-split non-degeneracy brick).**  If the
    two seam corners that the diagonal `b–w` creates at the cut endpoint `w` are
    *both* flat — the predecessor edge `prev–w` is collinear with the diagonal
    (`cross (w - prev) (b - w) = 0`) and the successor edge `w–succ` is collinear
    with the diagonal (`cross (w - b) (succ - w) = 0`) — then the original cyclic
    corner `prev, w, succ` is itself flat (`cross (w - prev) (succ - w) = 0`).
    Algebraically: both edge vectors `w - prev` and `succ - w` are parallel to the
    nonzero diagonal vector `b - w`, hence parallel to each other.

    Contrapositive consequence used by the interior branch: since
    `polyCycNondeg V` makes the genuine cyclic corner `prev, w, succ` non-flat
    (`cross (w - prev) (succ - w) ≠ 0`), the diagonal split along `b–w` can make
    *at most one* of the two pieces' seam corners at `w` flat.  The other piece
    therefore satisfies the `interior_split_nondeg` seam hypothesis automatically;
    the (at most one) flat piece is the residual case handled by flat-cut-vertex
    removal.  Sorry-free preparation for `meisters_reduction_interior2`. -/
lemma seam_flat_chain (prev w b succ : ℂ) (hbw : b ≠ w)
    (h1 : HexArea.cross (w - prev) (b - w) = 0)
    (h2 : HexArea.cross (w - b) (succ - w) = 0) :
    HexArea.cross (w - prev) (succ - w) = 0 := by
  simp only [HexArea.cross, Complex.sub_re, Complex.sub_im] at *
  have hv2 : (b.re - w.re) ^ 2 + (b.im - w.im) ^ 2 > 0 := by
    rcases eq_or_ne b.re w.re with h | h
    · rcases eq_or_ne b.im w.im with h' | h'
      · exact absurd (Complex.ext (by linarith) (by linarith)) hbw
      · have := sub_ne_zero.mpr h'; positivity
    · have := sub_ne_zero.mpr h; positivity
  have key : ((w.re - prev.re) * (succ.im - w.im) - (w.im - prev.im) * (succ.re - w.re))
      * ((b.re - w.re) ^ 2 + (b.im - w.im) ^ 2) = 0 := by
    linear_combination ((b.re - w.re) * (succ.re - w.re) + (b.im - w.im) * (succ.im - w.im)) * h1
      - ((w.re - prev.re) * (b.re - w.re) + (w.im - prev.im) * (b.im - w.im)) * h2
  rcases mul_eq_zero.mp key with h | h
  · linarith
  · linarith

/-- **At most one interior-split seam is flat (consumable form).**  If the
    genuine cyclic corner `prev, w, succ` of the `b`-rooted cycle is non-flat
    (`cross (w - prev) (succ - w) ≠ 0`, supplied by `polyCycNondeg`), then for
    the interior diagonal `b–w` at least one of the two seam corners at `w` is
    non-flat: either the left-piece seam `cross (w - prev) (b - w) ≠ 0` or the
    right-piece seam `cross (w - b) (succ - w) ≠ 0`.  Hence at least one of the
    two split pieces satisfies the `interior_split_nondeg` seam hypothesis at `w`
    outright; the other (at most one) is the flat-cut-vertex residual case.
    Immediate corollary of `seam_flat_chain`.  Sorry-free preparation for
    `meisters_reduction_interior2`. -/
lemma seam_one_nonflat (prev w b succ : ℂ) (hbw : b ≠ w)
    (hpws : HexArea.cross (w - prev) (succ - w) ≠ 0) :
    HexArea.cross (w - prev) (b - w) ≠ 0 ∨ HexArea.cross (w - b) (succ - w) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hpws (seam_flat_chain prev w b succ hbw h.1 h.2)

/-
**Interior consecutive-triple non-flatness from cyclic non-degeneracy.**
    If `V` is cyclically non-degenerate and `prev, w, succ` are three
    *consecutive* vertices of `V` strictly inside the list (indices
    `k-1, k, k+1` with `k + 1 < V.length`), then the corner `prev, w, succ` is
    non-flat: `cross (w - prev) (succ - w) ≠ 0`.  The interior corner lies
    within `V` itself, so it is read off `polyNondeg V` (obtained from the
    cyclic `polyNondeg (V ++ V.take 2)` by `polyNondeg_take`) after dropping the
    first `k-1` vertices.  Sorry-free preparation for
    `meisters_reduction_interior2` (supplies the genuine non-flat seam corner of
    the cut endpoint `w`).
-/
lemma polyCycNondeg_interior_corner (V : List ℂ) (k : ℕ) (prev w succ : ℂ)
    (hnd : polyCycNondeg V) (hk1 : 1 ≤ k) (hk : k + 1 < V.length)
    (hprev : V[k-1]? = some prev) (hw : V[k]? = some w)
    (hsucc : V[k+1]? = some succ) :
    HexArea.cross (w - prev) (succ - w) ≠ 0 := by
  obtain ⟨l, hl⟩ : ∃ l : List ℂ, V.drop (k - 1) = prev :: w :: succ :: l := by
    grind +suggestions;
  have h_nondeg_drop : polyNondeg (List.drop (k - 1) (V ++ List.take 2 V)) := by
    grind +suggestions;
  have h_nondeg_drop : polyNondeg (prev :: w :: succ :: l ++ List.take 2 V) := by
    grind +suggestions;
  have := polyNondeg_cons_cons_cons prev w succ ( l ++ List.take 2 V ) ; aesop;

/-
**At least one interior-split piece is cyclically non-degenerate.**  The
    disjunctive form that discharges the documented "non-degeneracy half"
    obstruction of the interior branch.  The cut endpoint `w` (strictly inside
    the corner triangle `a,b,c`, so `b ≠ w`) is the index-`k` vertex of the
    `b`-rooted cycle `W := b :: c :: rest ++ [a]`; its genuine cyclic corner
    `(prev, w, succ)` is non-flat (`polyCycNondeg_interior_corner` after
    transporting `polyCycNondeg` across the rotation `W = (a::b::c::rest).rotate 1`),
    so by `seam_one_nonflat` at least one of the two seam corners at `w` is
    non-flat, whence `interior_split_nondeg_left` / `interior_split_nondeg_right`
    make the corresponding chord piece `polyCycNondeg`.  Sorry-free preparation
    for `meisters_reduction_interior2`.
-/
lemma interior_split_one_nondeg (a b c w prev succ : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w) (hbw : b ≠ w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (hprev : (b :: c :: rest ++ [a])[k-1]? = some prev)
    (hsucc : (b :: c :: rest ++ [a])[k+1]? = some succ) :
    polyCycNondeg (HexArea.chordLeft (b :: c :: rest ++ [a]) k) ∨
    polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) k) := by
  by_cases hcase : HexArea.cross (w - prev) (b - w) ≠ 0;
  · refine Or.inl ?_;
    apply interior_split_nondeg_left a b c w prev rest k hnd hwin hk2 hk hwk hprev hcase;
  · have hcase2 : HexArea.cross (w - b) (succ - w) ≠ 0 := by
      contrapose! hcase; have := polyCycNondeg_interior_corner ( b :: c :: rest ++ [ a ] ) k prev w succ ?_ ?_ ?_ hprev hwk hsucc <;> simp_all +decide ;
      · exact fun h => this <| by simpa [ hcase ] using seam_flat_chain prev w b succ hbw h hcase;
      · convert polyCycNondeg_rotate1 ( a :: b :: c :: rest ) ( by simp +arith +decide ) |>.2 hnd using 1;
      · linarith;
    exact Or.inr ( interior_split_nondeg_right a b c w succ rest k hnd hwin hk2 hk hwk hsucc hcase2 )


/-
**Recursion-ready interior split (sorry-free combinatorial bundle).**
    Consolidates the banked interior-split bricks into the single package the
    interior branch consumes: from the convex corner `a, b, c` of the simple
    non-degenerate cycle `V.rotate r = a :: b :: c :: rest` and an interior
    vertex `w ∈ rest` farthest from the base diagonal `a–c`, it produces the cut
    index `k` for the `b`-rooted cycle `W := b :: c :: rest ++ [a]` together with
    BOTH pieces `chordLeft W k` / `chordRight W k` being `PolygonSimple` and
    strictly shorter than `V`, plus AT LEAST ONE of them `polyCycNondeg`.  This
    is exactly the data needed to fire the `IH2` recursion on the piece not
    containing the forbidden edge.  Assembled sorry-free from
    `interior_split_simple`, `interior_split_one_nondeg`, `chordLeft_length_lt`,
    `chordRight_length_lt`; preparation for `meisters_reduction_interior2` (NOT a
    dead branch).
-/
lemma interior_split_select (V : List ℂ) (hsimple : PolygonSimple V)
    (hnd : polyCycNondeg V)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (w : ℂ) (hwrest : w ∈ rest) (hwin : HexArea.inTriangleStrict a b c w)
    (hwmax : ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) * HexArea.cross (c - a) (b - a)
          ≤ HexArea.cross (c - a) (w - a) * HexArea.cross (c - a) (b - a)) :
    ∃ k : ℕ, 2 ≤ k ∧ k + 2 ≤ (b :: c :: rest ++ [a]).length ∧
      (b :: c :: rest ++ [a])[k]? = some w ∧
      PolygonSimple (HexArea.chordLeft (b :: c :: rest ++ [a]) k) ∧
      PolygonSimple (HexArea.chordRight (b :: c :: rest ++ [a]) k) ∧
      (HexArea.chordLeft (b :: c :: rest ++ [a]) k).length < V.length ∧
      (HexArea.chordRight (b :: c :: rest ++ [a]) k).length < V.length ∧
      (polyCycNondeg (HexArea.chordLeft (b :: c :: rest ++ [a]) k) ∨
       polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) k)) := by
  have hW_length : (a :: b :: c :: rest).length = V.length := by
    rw [ ← hrot, List.length_rotate ];
  have := interior_split_simple a b c w rest ?_ hndtri hwrest hwin hwmax;
  · obtain ⟨ k, hk₁, hk₂, hk₃, hk₄, hk₅, hk₆ ⟩ := this; use k; simp_all +decide [ List.length_append ] ;
    refine' ⟨ _, _, _ ⟩;
    · grind +suggestions;
    · rw [ HexArea.chordRight_length ] <;> norm_num <;> omega;
    · apply interior_split_one_nondeg a b c w ( ( b :: c :: ( rest ++ [ a ] ) )[k - 1]! ) ( ( b :: c :: ( rest ++ [ a ] ) )[k + 1]! ) rest k ?_ hwin ?_ hk₁ ?_ hk₄ ?_ ?_;
      · convert polyCycNondeg_rotate V r _ using 1;
        · aesop;
        · linarith;
      · intro h; simp_all +decide [ HexArea.inTriangleStrict ] ;
      · grind;
      · grind;
      · grind +splitImp;
  · have := PolygonSimple_rotate V r;
    grind

end
