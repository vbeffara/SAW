import Mathlib
import RequestProject.SAWUmlaufPolyLift
import RequestProject.SAWUmlaufConeStrict

/-!
# `SAWUmlaufBaseBlocked` — the blocked-base chord of the Meisters recursion

In the *empty* branch of the Meisters ear search the convex apex `b` of a
rotation `V.rotate r = a :: b :: c :: rest` has an empty corner triangle: no
vertex of `rest` lies in the **open** triangle `a, b, c`.  The branch then splits
on the base diagonal `a–c`:

* base *clear* — no vertex of `rest` on the closed segment `[a, c]` — is the
  situation handled by `empty_branch_good_lift` / `empty_branch_flat_clip_lift`;
* base *blocked* — some vertex `w ∈ rest` lies on `[a, c]` — is handled here.

In the blocked case the clip `a :: c :: rest` is not even a simple polygon (the
new edge `a–c` runs through the vertex `w`), so one has to cut `V` along the
chord `b–w` instead.  This file supplies the two geometric inputs of that cut:

* `base_vertex_cross_facts` — the corner cross products at a point of the *open*
  base segment, which give both the two clauses `hwac`, `hwbc` the interior-split
  bricks now take and the strict cone membership
  `HexArea.inConeStrict a b c w` needed for `InteriorChord`;
* `base_chord_is_diagonal` — the blocked-base analogue of
  `interior_chord_is_diagonal`: the chord `b–w` meets no non-incident edge of the
  polygon.  The proof is the same as in the interior case; only the arithmetic
  of the corner tests along `[b, w]` changes, and the maximality hypothesis
  `hwmax` is replaced by the emptiness of the open corner triangle, which in the
  blocked case is available outright.
* `base_split_select` — the packaged cut data, exactly the shape
  `interior_split_select` produces for the interior branch.

NOT a dead branch: imported by `RequestProject.SAWUmlaufPolyMeisters` and
consumed by `empty_branch_base_blocked_lift`.
-/

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

/-! ## 1. The corner arithmetic at a point of the open base -/

/-- **Corner cross products at a point of the open base segment.**  If
`w - a = s • (c - a)` with `0 < s < 1`, then, writing `O = cross (b-a) (c-b)` for
the corner orientation,

    cross (b - a) (w - a) = s * O,
    cross (c - b) (w - b) = (1 - s) * O,
    cross (a - c) (w - c) = 0.

In particular both corner tests at `w` are non-zero as soon as the corner is
non-degenerate, and `w` is strictly inside the corner *cone* at `b`. -/
lemma base_vertex_cross_facts (a b c w : ℂ) (s : ℝ)
    (hw : w - a = (s : ℂ) * (c - a)) :
    HexArea.cross (b - a) (w - a) = s * HexArea.cross (b - a) (c - b) ∧
    HexArea.cross (c - b) (w - b) = (1 - s) * HexArea.cross (b - a) (c - b) ∧
    HexArea.cross (a - c) (w - c) = 0 := by
  have hw' : w = a + (s : ℂ) * (c - a) := by linear_combination hw
  subst hw'
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [HexArea.cross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im] <;> ring

/-- A vertex of the open base segment is strictly inside the corner cone at the
apex `b`, spanned by the two polygon edges `b–a` and `b–c`. -/
lemma base_vertex_inConeStrict (a b c w : ℂ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hw : w - a = (s : ℂ) * (c - a)) :
    HexArea.inConeStrict a b c w := by
  refine ⟨?_, 1 - s, s, by linarith, hs0, ?_⟩
  · -- `cross (a - b) (c - b) = - cross (b - a) (c - b) ≠ 0`
    intro hc
    refine hndtri ?_
    simp only [HexArea.cross, Complex.sub_re, Complex.sub_im] at hc ⊢
    linarith
  · have hw' : w = a + (s : ℂ) * (c - a) := by linear_combination hw
    rw [hw']
    push_cast [Complex.real_smul]
    ring

/-! ## 2. The chord `b–w` is a valid diagonal -/

/-- **The blocked-base chord is a diagonal.**  Blocked-base analogue of
`interior_chord_is_diagonal` (`RequestProject.SAWUmlaufPolyChord`): if the open
corner triangle `a, b, c` of the simple polygon `a :: b :: c :: rest` contains no
vertex of `rest` (`hcase`) and `w ∈ rest` lies on the *open* base segment
`(a, c)`, then the chord `b–w` is disjoint from every closed edge of the polygon
not incident to `b` or `w`.

The proof is the interior one with two changes.  The corner tests along the open
segment `(b, w)` are now computed exactly: for `z = (1 - t) b + t w` with
`t ∈ (0,1)` and `w - a = s (c - a)`, `s ∈ (0,1)`,

    cross (b-a) (z-a) = t s O,   cross (c-b) (z-b) = t (1-s) O,
    cross (a-c) (z-c) = (1-t) O, cross (a-c) (w-c) = 0,

so `z` is strictly inside the corner and strictly farther from the base line than
`w`; and the maximality hypothesis is replaced by `hcase`, which says outright
that the endpoint `y` of the offending edge is not strictly inside the corner
triangle. -/
lemma base_chord_is_diagonal (a b c w : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hndtri : HexArea.cross (b - a) (c - b) ≠ 0)
    (hwrest : w ∈ rest) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hw : w - a = (s : ℂ) * (c - a))
    (hcase : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) :
    ∀ e ∈ closedEdges (a :: b :: c :: rest),
      b ≠ e.1 → b ≠ e.2 → w ≠ e.1 → w ≠ e.2 →
      Disjoint (segment ℝ b w) (segment ℝ e.1 e.2) := by
  intro e he hb1 hb2 hw1 hw2
  by_contra h_contra
  obtain ⟨z, hz⟩ : ∃ z ∈ segment ℝ b w, z ∈ segment ℝ e.1 e.2 := by
    grind +splitImp
  obtain ⟨y, hy⟩ : ∃ y ∈ ({e.1, e.2} : Set ℂ),
      HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b)
        ≥ HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) := by
    have h_affine : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        HexArea.cross (a - c) ((1 - t) • e.1 + t • e.2 - c) * HexArea.cross (b - a) (c - b)
          = (1 - t) * (HexArea.cross (a - c) (e.1 - c) * HexArea.cross (b - a) (c - b))
            + t * (HexArea.cross (a - c) (e.2 - c) * HexArea.cross (b - a) (c - b)) := by
      unfold HexArea.cross; norm_num [Complex.ext_iff]; intros; ring
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ z = (1 - t) • e.1 + t • e.2 := by
      rcases hz.2 with ⟨u, v, hu, hv, huv, rfl⟩
      exact ⟨v, ⟨by linarith, by linarith⟩, by simp +decide [huv.symm]⟩
    simp_all +decide [segment_eq_image]
    cases le_total (HexArea.cross (a - c) (e.1 - c) * HexArea.cross (b - a) (c - b))
        (HexArea.cross (a - c) (e.2 - c) * HexArea.cross (b - a) (c - b)) <;>
      first | left; nlinarith | right; nlinarith
  have hz_pos : HexArea.cross (b - a) (z - a) * HexArea.cross (b - a) (c - b) > 0 ∧
      HexArea.cross (c - b) (z - b) * HexArea.cross (b - a) (c - b) > 0 ∧
      HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b)
        > HexArea.cross (a - c) (w - c) * HexArea.cross (b - a) (c - b) ∧
      HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b) > 0 := by
    obtain ⟨t, ht⟩ : ∃ t ∈ Set.Ioo (0 : ℝ) 1, z = (1 - t) • b + t • w := by
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, z = (1 - t) • b + t • w := by
        rw [segment_eq_image] at hz; aesop
      refine ⟨t, ⟨lt_of_le_of_ne ht.1.1 ?_, lt_of_le_of_ne ht.1.2 ?_⟩, ht.2⟩ <;>
        rintro rfl <;> simp_all +decide [segment_eq_image]
      · obtain ⟨x, hx, hx'⟩ := hz.2
        have := simple_vertex_not_on_far_edge (a :: b :: c :: rest) (by grind +splitImp)
          hsimple b (by simp +decide) e he hb1 hb2
        exact this ⟨1 - x, x, by aesop⟩
      · have := simple_vertex_not_on_far_edge (a :: b :: c :: rest) (by grind)
          hsimple w (by grind) e he hw1 hw2
        simp_all +decide [segment_eq_image]
    obtain ⟨htI, hzt⟩ := ht
    obtain ⟨ht0, ht1⟩ := htI
    have hzc : z = b + (t : ℂ) * (w - b) := by
      rw [hzt]; push_cast [Complex.real_smul]; ring
    have hwc : w = a + (s : ℂ) * (c - a) := by linear_combination hw
    have E1 : HexArea.cross (b - a) (z - a)
        = t * s * HexArea.cross (b - a) (c - b) := by
      rw [hzc, hwc]
      simp [HexArea.cross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im]
      ring
    have E2 : HexArea.cross (c - b) (z - b)
        = t * (1 - s) * HexArea.cross (b - a) (c - b) := by
      rw [hzc, hwc]
      simp [HexArea.cross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im]
      ring
    have E3 : HexArea.cross (a - c) (z - c)
        = (1 - t) * HexArea.cross (b - a) (c - b) := by
      rw [hzc, hwc]
      simp [HexArea.cross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im]
      ring
    have E4 : HexArea.cross (a - c) (w - c) = 0 := by
      rw [hwc]
      simp [HexArea.cross, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im]
      ring
    have hOsq : 0 < HexArea.cross (b - a) (c - b) * HexArea.cross (b - a) (c - b) :=
      mul_self_pos.mpr hndtri
    have h1s : (0:ℝ) < 1 - s := by linarith
    have h1t : (0:ℝ) < 1 - t := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [E1]; nlinarith [mul_pos (mul_pos ht0 hs0) hOsq]
    · rw [E2]; nlinarith [mul_pos (mul_pos ht0 h1s) hOsq]
    · rw [E3, E4]; nlinarith [mul_pos h1t hOsq]
    · rw [E3]; nlinarith [mul_pos h1t hOsq]
  have hy_rest : y ∈ rest := by
    have hy_rest : y ∈ a :: b :: c :: rest := by
      have := List.of_mem_zip he; simp_all +decide
      grind +ring
    by_cases hya : y = a <;> by_cases hyc : y = c <;> simp_all +decide
    · unfold HexArea.cross at *; aesop
    · linarith
    · simp_all +decide [HexArea.cross]
      linarith
    · grind
  have hy_not_in_triangle : ¬ HexArea.inTriangleStrict a b c y := hcase y hy_rest
  have hb_not_in_segment : b ∉ segment ℝ e.1 e.2 := by
    apply simple_vertex_not_on_far_edge (a :: b :: c :: rest) (by grind) hsimple b
      (by simp +decide) e he hb1 hb2
  have ha_not_in_segment : a ∉ segment ℝ z y := by
    intro ha_in_segment
    have h_cross_zero : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        HexArea.cross (a - c) ((1 - t) • z + t • y - c) * HexArea.cross (b - a) (c - b)
          = (1 - t) * HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b)
            + t * HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) := by
      intros t ht
      simp [HexArea.cross]
      ring
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ a = (1 - t) • z + t • y := by
      rw [segment_eq_image] at ha_in_segment
      rcases ha_in_segment with ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    norm_num [ht.2] at *
    specialize h_cross_zero t ht.1 ht.2; norm_num at h_cross_zero; nlinarith
  have hc_not_in_segment : c ∉ segment ℝ z y := by
    intro hc_in_segment
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ c = (1 - t) • z + t • y := by
      rw [segment_eq_image] at hc_in_segment
      obtain ⟨t, ht, rfl⟩ := hc_in_segment
      exact ⟨t, ht, rfl⟩
    have h_cross_zero : HexArea.cross (a - c) (c - c) * HexArea.cross (b - a) (c - b)
        = (1 - t) * HexArea.cross (a - c) (z - c) * HexArea.cross (b - a) (c - b)
          + t * HexArea.cross (a - c) (y - c) * HexArea.cross (b - a) (c - b) := by
      rw [ht.right]
      unfold HexArea.cross; norm_num; ring
    have hzero : HexArea.cross (a - c) (c - c) * HexArea.cross (b - a) (c - b) = 0 := by
      simp [HexArea.cross]
    rw [hzero] at h_cross_zero
    nlinarith [ht.1.1, ht.1.2, hz_pos.2.2.2, hy.2]
  have := HexArea.corner_exit_point_ge a b c z y hndtri hz_pos.1 hz_pos.2.1
    hz_pos.2.2.2.le (by linarith) hy_not_in_triangle
  rcases this with ⟨p, hp₁, hp₂⟩ | ⟨p, hp₁, hp₂⟩
  · have := chord_disjoint_ear_ab a b c rest z y hsimple e he hb1 hb2 hz.2
      (by rcases hy.1 with rfl | rfl <;>
        [exact left_mem_segment _ _ _; exact right_mem_segment _ _ _])
      hb_not_in_segment ha_not_in_segment
      (by exact fun h => by simp_all +decide [HexArea.cross])
    exact this.le_bot ⟨hp₁, hp₂⟩
  · have := chord_disjoint_ear_bc a b c rest z y hsimple e he hb1 hb2 hz.2
      (by rcases hy.1 with rfl | rfl <;>
        [exact left_mem_segment _ _ _; exact right_mem_segment _ _ _])
      hb_not_in_segment hc_not_in_segment
      (by exact fun h => by simp_all +decide [HexArea.cross])
    exact this.le_bot ⟨hp₁, hp₂⟩

end
