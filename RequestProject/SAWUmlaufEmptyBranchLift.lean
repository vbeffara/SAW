import Mathlib
import RequestProject.SAWUmlaufPolyLift

/-!
# `SAWUmlaufEmptyBranchLift` — lifting an ear of a *possibly degenerate* clip

This file closes the last combinatorial residue of the **empty branch** of the
Meisters ear recursion (`RequestProject.SAWUmlaufPolyMeisters`).

Setting.  `V.rotate r = a :: b :: c :: rest` with a convex apex `b` that is one
of the two forbidden vertices, so the ear at `b` cannot be used and the
recursion must clip `b` and find an ear of the clip `M = a :: c :: rest`
avoiding the junction `{a, c}`.  When the clip is cyclically non-degenerate this
lift is `empty_branch_good_lift` (`RequestProject.SAWUmlaufPolyLift`).  The
residual case — clipping `b` leaves a *flat seam* at `a` or at `c`, so `M` is
cyclically degenerate — is the one treated here: the clip ear is produced by
`clip_flat_ear` (`RequestProject.SAWUmlaufFlatClipLift`) and only comes as a bare
`EmptyCornerData2 M a c`, without the corner non-flatness `cross (b' - a')
(c' - b') ≠ 0` that `empty_branch_interior_lift` reads off `polyCycNondeg M`.

Two observations make the lift go through anyway.

* The *boundary* half of the lift never used the two clip-corner clauses
  `cross (c - a) (p - a) ≠ 0`, `cross (c - a) (q - a) ≠ 0` in the first place:
  `empty_branch_boundary_lift_weak` below is `empty_branch_boundary_lift` with
  those (and every other unused) hypothesis removed.
* In the *interior* half, a clip ear with a **degenerate** corner still lifts:
  a degenerate triangle has empty strict interior (`inTriangleStrict_nondeg`),
  the re-inserted apex `b` is off the ear diagonal (`hbseg`), and the
  orientation `iff` becomes the implication `shoelace2 (a' :: c' :: …) ≤ 0`,
  which follows from the two given orientation equivalences because both the
  clip area and the corner area `shoelace2 [a, b, c]` are then non-positive.
  This is `empty_branch_interior_lift_flat`.

The two halves are assembled into `empty_branch_lift_of_clip_data`, which is
consumed by `empty_branch_flat_clip_lift` (`SAWUmlaufPolyMeisters`).

The whole file is `sorry`-free.
-/

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 1. The boundary half, with the unused hypotheses removed -/

/-- **Empty-branch lift — the BOUNDARY subcase, weak form.**  This is exactly
`empty_branch_boundary_lift` (`RequestProject.SAWUmlaufPolyLift`) with every
hypothesis its proof does not use dropped: in particular the two clip-corner
non-flatness clauses `cross (c - a) (p - a) ≠ 0`, `cross (c - a) (q - a) ≠ 0`,
the cyclic non-degeneracy of `V`, the emptiness/diagonal clauses of the corner
`a, b, c`, and the induction hypothesis.  Only the combinatorics of the seam and
the convexity of the apex `b` are needed.

Consumed by `empty_branch_lift_of_clip_data` below, where those clauses are
genuinely unavailable (the clip is degenerate at a seam). -/
lemma empty_branch_boundary_lift_weak (V : List ℂ) (hlen : 5 ≤ V.length)
    (hsimple : PolygonSimple V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
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
    simp_all +decide
    grind +ring
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

/-! ## 2. The interior half for a degenerate clip ear -/

/-- **Interior-ear lift for a DEGENERATE clip ear.**  The exact analogue of
`empty_branch_interior_lift` (`RequestProject.SAWUmlaufPolyBase`) when the ear
triangle of the clip is *flat*, `shoelace2 [a', b', c'] = 0` — the case that
lemma excludes through its hypothesis `cross (b' - a') (c' - b') ≠ 0`.

All three clauses of the lifted `EmptyCornerData2` become easier, not harder:

* emptiness is automatic, since a flat triangle has no strict interior point
  (`HexArea.inTriangleStrict_nondeg`);
* diagonal-clearance for the re-inserted apex `b` is `hbseg`;
* the orientation `iff` degenerates to the single implication
  `¬ (0 < shoelace2 (a' :: c' :: (s ++ a :: b :: c :: t)))`.  Writing `X` for the
  area of the clipped clip and `T` for `shoelace2 [a, b, c]`, `horient'` reads
  `False ↔ 0 < X`, so `X ≤ 0`; the clip area is then `X` as well, so `horient`
  gives `T ≤ 0`; and the target area is `X + T ≤ 0`. -/
lemma empty_branch_interior_lift_flat (V : List ℂ) (z1 z2 : ℂ)
    (a b c : ℂ) (rest : List ℂ) (r : ℕ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hac : a ≠ c) (hanr : a ∉ rest)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hzrest : ∀ y ∈ rest, y ≠ z1 ∧ y ≠ z2)
    (a' b' c' : ℂ) (s t : List ℂ) (r' : ℕ)
    (hrot' : (a :: c :: rest).rotate r' = a' :: b' :: c' :: (s ++ a :: c :: t))
    (hb'rest : b' ∈ rest) (ha'V : a' ∈ V) (hc'V : c' ∈ V)
    (ha'b : b ≠ a') (hc'b : b ≠ c')
    (hA'zero : HexArea.shoelace2 [a', b', c'] = 0)
    (hdiag' : ∀ x ∈ (s ++ a :: c :: t), x ∉ segment ℝ a' c')
    (horient' : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t)))) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨r'', hrnewrot⟩ :
      ∃ r'', (V.rotate (r + r'')) = a' :: b' :: c' :: (s ++ a :: b :: c :: t) := by
    obtain ⟨r'', hr''⟩ := clip_ear_lift_interior a b c a' b' c' rest s t r' hac hanr hrot'
    exact ⟨r'', by rw [← hr'', ← hrot, List.rotate_rotate]⟩
  -- the tail is nonempty, so it has a first and a last element
  obtain ⟨p', hp'⟩ : ∃ p', (s ++ a :: b :: c :: t).getLast? = some p' := by
    cases h : (s ++ a :: b :: c :: t).getLast? with
    | none =>
        rw [List.getLast?_eq_none_iff] at h
        cases s <;> simp at h
    | some x => exact ⟨x, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q', (s ++ a :: b :: c :: t).head? = some q' := by
    cases s <;> simp
  refine ⟨r + r'', a', b', c', p', q', s ++ a :: b :: c :: t, hrnewrot,
    (hzrest _ hb'rest).1, (hzrest _ hb'rest).2, hp', hq', ?_, ?_, ?_⟩
  · intro x hx hin
    refine (HexArea.inTriangleStrict_nondeg a' b' c' x hin) ?_
    have hc : HexArea.cross (b' - a') (c' - b') = HexArea.shoelace2 [a', b', c'] := by
      simp [HexArea.shoelace2_triple, HexArea.cross]; ring
    rw [hc, hA'zero]
  · intro x hx
    have hxcases : x ∈ (s ++ a :: c :: t) ∨ x = b := by
      simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto
    rcases hxcases with h | rfl
    · exact hdiag' x h
    · exact hbseg a' c' ha'V hc'V ha'b hc'b
  · have hX0 : HexArea.shoelace2 (a :: c :: rest)
        = HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t)) := by
      have h1 : HexArea.shoelace2 (a :: c :: rest)
          = HexArea.shoelace2 (a' :: b' :: c' :: (s ++ a :: c :: t)) := by
        rw [← hrot', shoelace2_rotate]
      rw [h1, shoelace2_clip_second, hA'zero, add_zero]
    have hins : HexArea.shoelace2 (a' :: c' :: (s ++ a :: b :: c :: t))
        = HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t))
          + HexArea.shoelace2 [a, b, c] := by
      simpa using shoelace2_insert_mid (a' :: c' :: s) t a b c
    rw [hA'zero, hins]
    rw [hA'zero] at horient'
    constructor
    · intro h; exact absurd h (lt_irrefl 0)
    · intro h
      exfalso
      have hXle : HexArea.shoelace2 (a' :: c' :: (s ++ a :: c :: t)) ≤ 0 := by
        by_contra hpos
        exact absurd (horient'.mpr (not_le.mp hpos)) (lt_irrefl 0)
      have hTle : HexArea.shoelace2 [a, b, c] ≤ 0 := by
        by_contra hpos
        have := horient.mp (not_le.mp hpos)
        rw [hX0] at this
        linarith
      linarith

/-! ## 3. The lift -/

/-- **Lifting an ear of the clip back to the polygon (PROVED).**

Setting: `V.rotate r = a :: b :: c :: rest`, the apex `b` is convex (`hbconv`,
`hbseg`), the ear at `b` is coherently oriented with the clip `M = a :: c :: rest`
(`horient`), and `b` is a forbidden vertex (`hbf`), so the ear at `b` cannot be
used.  Given *any* ear of the clip avoiding the clip junction `{a, c}`
(`hdata : EmptyCornerData2 M a c`), re-inserting `b` produces an ear of `V`
avoiding both forbidden vertices.

Unlike `empty_branch_good_lift` this needs **no** non-degeneracy of the clip: the
seam/boundary case is `empty_branch_boundary_lift_weak` and the interior case
splits on whether the clip ear triangle is flat
(`empty_branch_interior_lift_flat`) or not (`empty_branch_interior_lift`).

The tip `b'` of the clip ear lies in `rest`, hence avoids `a`, `c` and, by
`Nodup`, `b`; since `b`'s only cyclic neighbours in `V` are `a` and `c`, and one
of `z1, z2` is `b` while the other is `b` or a neighbour of `b`, the tip avoids
both forbidden vertices (`forbidden_subset_corner`).

Consumed by `empty_branch_flat_clip_lift` (`RequestProject.SAWUmlaufPolyMeisters`). -/
lemma empty_branch_lift_of_clip_data (V : List ℂ) (hlen : 5 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (horient : ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))
    (hbf : b = z1 ∨ b = z2)
    (hdata : EmptyCornerData2 (a :: c :: rest) a c) :
    EmptyCornerData2 V z1 z2 := by
  obtain ⟨r', a', b', c', p'M, q'M, rest', hrot', hb'a, hb'c, hp'M, hq'M,
    hempty', hdiag', horient'⟩ := hdata
  obtain ⟨ha'M, hb'M, hc'M, hrest'M⟩ :=
    rotate_cons3_mem (a :: c :: rest) a' b' c' rest' r' hrot'
  obtain ⟨hac, hanr, hbnr, hba, hbc, hcnr, hrnd⟩ :
      a ≠ c ∧ a ∉ rest ∧ b ∉ rest ∧ b ≠ a ∧ b ≠ c ∧ c ∉ rest ∧ rest.Nodup := by
    have hrot_nodup : List.Nodup (V.rotate r) := List.nodup_rotate.mpr hsimple.1
    rw [hrot] at hrot_nodup
    simp only [List.nodup_cons, List.mem_cons] at hrot_nodup
    grind +qlia
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
    simp_all +decide
    grind +ring
  have hABCne : HexArea.cross (b - a) (c - b) ≠ 0 :=
    polyCycNondeg_rotate_head V a b c rest r (by omega) hnd hrot
  by_cases hint : ∃ s t, rest' = s ++ a :: c :: t
  · obtain ⟨s, t, rfl⟩ := hint
    by_cases hA'flat : HexArea.shoelace2 [a', b', c'] = 0
    · exact empty_branch_interior_lift_flat V z1 z2 a b c rest r hrot hac hanr hbseg
        horient hzrest a' b' c' s t r' hrot' hb'rest ha'V hc'V ha'b hc'b hA'flat hdiag'
        horient'
    · have hcross : HexArea.cross (b' - a') (c' - b') ≠ 0 := by
        have hc : HexArea.cross (b' - a') (c' - b') = HexArea.shoelace2 [a', b', c'] := by
          simp [HexArea.shoelace2_triple, HexArea.cross]; ring
        rw [hc]; exact hA'flat
      exact empty_branch_interior_lift V z1 z2 a b c rest r hrot hac hanr hbconv hbseg
        horient hABCne hzrest a' b' c' p'M q'M s t r' hrot' hb'rest ha'V hb'V hc'V
        ha'b hc'b hcross hp'M hq'M hempty' hdiag' horient'
  · exact empty_branch_boundary_lift_weak V hlen hsimple z1 z2 hadj r a b c rest hrot
      hbconv hbseg horient hbf a' b' c' p'M q'M rest' r' hrot' hb'a hb'c hp'M hq'M
      hempty' hdiag' horient' hint

end
