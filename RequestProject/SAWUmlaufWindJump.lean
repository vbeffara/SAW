import Mathlib
import RequestProject.SAWUmlaufRayIndex
import RequestProject.SAWUmlaufPtWindMove

/-!
# `SAWUmlaufWindJump` — the winding number jumps by `2π` across an edge

This file proves the *local* counterpart of the global ray-crossing formula of
`RequestProject.SAWUmlaufRayIndex`: crossing one edge of a closed polygon changes
the winding number by exactly `2π`.

Precisely (`ptWind_jump_edge`): let `m` be an interior point of the edge `A–B` of
the cycle `A :: B :: rest` and suppose `m` lies on no other edge of that cycle.
Then there is a radius `δ > 0` such that for **any** two points `y`, `z` within
`δ` of `m`, lying strictly on opposite sides of the line `A–B` (the side being
read off from the sign of `cross (B - A) (· - A)`) and off the vertices,

  `ptWind y (A :: B :: rest) - ptWind z (A :: B :: rest) = 2π`.

## The proof

Split the closed sweep sum at the distinguished edge,

  `ptWind x (A :: B :: rest) = arg ((B - x)/(A - x)) + ptTurn x (B :: rest ++ [A])`.

The second summand is **continuous** at `m` (`continuousAt_ptTurn`, since `m` is
off every edge of the open path `B → … → A`), so its contribution to the
difference is smaller than `π/2` once `y`, `z` are close enough to `m`.  The
first summand is the jumping one: near `m` the ratio `(B - x)/(A - x)` has
negative real part (at `x = m` it is the negative real number `-(1-t)/t`), while
the sign of its imaginary part is the sign of `cross (B - A) (x - A)`, i.e. the
side of the line the point is on.  Hence its argument lies in `(π/2, π]` on one
side and in `[-π, -π/2)` on the other, so the difference of the two arguments
lies in `(π, 2π)`.  Altogether the winding difference lies in `(π/2, 5π/2)`; and
it is a multiple of `2π` by `ptWind_int`, so it equals `2π`.

## Downstream use (NOT a dead branch)

The file is imported by `RequestProject.SAWUmlaufChordLiftAux`, hence lies on the
live route to `polygon_umlaufsatz`.  Like `SAWUmlaufRayIndex` it is *preparation*
— recorded as such in `PROOF_STATUS.md` — for the four remaining Jordan-level
gaps of the chain.  The jump lemma is the tool that distinguishes the two sides
of a polygon boundary by an invariant: it is what turns statements of the form
"this point is on the far side of the cut, hence the winding vanishes there"
(`chord_piece_orient`, `chord_lift_other_not_on_diagonal`,
`clipped_ear_escape_walk`) into finite computations, and it is the local input of
the collar argument for the polygonal Jordan curve theorem.
-/

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 1000000

/-! ## 1. Elementary bricks -/

/-- The imaginary part of the sweep ratio is the position cross product, scaled
by the (positive) squared norm of the first position vector. -/
lemma div_sub_im_mul_normSq (a b y : ℂ) :
    ((b - y) / (a - y)).im * Complex.normSq (a - y) = cross (a - y) (b - y) := by
  by_cases h : a - y = 0
  · simp [h, cross, Complex.normSq]
  · have hns : Complex.normSq (a - y) ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr h)
    rw [Complex.div_im, cross, sub_mul, div_mul_cancel₀ _ hns, div_mul_cancel₀ _ hns]
    ring

/-- The sign of the imaginary part of the sweep ratio `(b-y)/(a-y)` is the sign of
`cross (b - a) (y - a)`. -/
lemma div_sub_im_pos_iff (a b y : ℂ) (h : a - y ≠ 0) :
    (0 < ((b - y) / (a - y)).im ↔ 0 < cross (b - a) (y - a)) := by
  have hns : 0 < Complex.normSq (a - y) := Complex.normSq_pos.mpr h
  have hcr : cross (a - y) (b - y) = cross (b - a) (y - a) := cross_pos_vec a b y
  constructor
  · intro hi
    rw [← hcr, ← div_sub_im_mul_normSq a b y]
    exact mul_pos hi hns
  · intro hc
    by_contra hi
    push_neg at hi
    have := div_sub_im_mul_normSq a b y
    rw [hcr] at this
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hi (le_of_lt hns)]

/-- Argument bounds in the second quadrant-and-a-half: negative real part and
positive imaginary part force `arg ∈ (π/2, π]`. -/
lemma arg_gt_pi_div_two (z : ℂ) (hre : z.re < 0) (him : 0 < z.im) :
    Real.pi / 2 < z.arg ∧ z.arg ≤ Real.pi := by
  refine ⟨?_, Complex.arg_le_pi z⟩
  have habs : ¬ |z.arg| ≤ Real.pi / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff]
    linarith
  push_neg at habs
  have hnn : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him.le
  rw [abs_of_nonneg hnn] at habs
  exact habs

/-- Argument bounds in the third quadrant-and-a-half: negative real part and
negative imaginary part force `arg ∈ [-π, -π/2)`. -/
lemma arg_lt_neg_pi_div_two (z : ℂ) (hre : z.re < 0) (him : z.im < 0) :
    -Real.pi < z.arg ∧ z.arg < -(Real.pi / 2) := by
  refine ⟨Complex.neg_pi_lt_arg z, ?_⟩
  have habs : ¬ |z.arg| ≤ Real.pi / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff]
    linarith
  push_neg at habs
  have hneg : z.arg < 0 := Complex.arg_neg_iff.mpr him
  rw [abs_of_neg hneg] at habs
  linarith

/-- Splitting the closed sweep sum at the first edge. -/
lemma ptWind_cons_cons_split (x A B : ℂ) (rest : List ℂ) :
    ptWind x (A :: B :: rest)
      = Complex.arg ((B - x) / (A - x)) + ptTurn x (B :: (rest ++ [A])) := by
  unfold ptWind
  have hform : (A :: B :: rest) ++ (A :: B :: rest).take 1 = A :: B :: (rest ++ [A]) := by
    simp [List.take]
  rw [hform, ptTurn_cons_cons]

/-- At an interior point of the edge, the sweep ratio is a negative real. -/
lemma ratio_neg_real_of_openSegment (A B m : ℂ) (hAB : A ≠ B)
    (hm : m ∈ openSegment ℝ A B) :
    ((B - m) / (A - m)).re < 0 ∧ ((B - m) / (A - m)).im = 0 ∧ A - m ≠ 0 := by
  rw [openSegment_eq_image' ℝ A B] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  obtain ⟨ht0, ht1⟩ := ht
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
  have hA : A - (A + t • (B - A)) = (-t : ℝ) • (B - A) := by
    simp [Complex.real_smul]
  have hB : B - (A + t • (B - A)) = ((1 - t : ℝ)) • (B - A) := by
    simp [Complex.real_smul]; ring
  have hAne : A - (A + t • (B - A)) ≠ 0 := by
    rw [hA]
    simp [Complex.real_smul]
    exact ⟨by linarith, hBA⟩
  have htC : (t : ℂ) ≠ 0 := by
    simpa using (ne_of_gt ht0)
  have hkey : (B - (A + t • (B - A))) / (A - (A + t • (B - A)))
      = ((-((1 - t) / t) : ℝ) : ℂ) := by
    rw [hA, hB, Complex.real_smul, Complex.real_smul,
      mul_div_mul_right _ _ hBA]
    push_cast
    field_simp
  have hpos : (0:ℝ) < (1 - t) / t := div_pos (by linarith) ht0
  refine ⟨?_, ?_, hAne⟩
  · rw [hkey, Complex.ofReal_re]
    linarith
  · rw [hkey, Complex.ofReal_im]

/-! ## 2. The jump theorem -/

/-- **The winding number jumps by `2π` across an edge.**  Let `m` be an interior
point of the edge `A–B` of the closed polygon `A :: B :: rest`, lying on no other
edge of the cycle.  Then for all points `y`, `z` sufficiently close to `m` and
strictly on opposite sides of the line `A–B` (with `y` on the side where
`cross (B - A) (· - A) > 0`), and off the vertices,

  `ptWind y (A :: B :: rest) - ptWind z (A :: B :: rest) = 2π`. -/
theorem ptWind_jump_edge (A B : ℂ) (rest : List ℂ) (m : ℂ) (hAB : A ≠ B)
    (hm : m ∈ openSegment ℝ A B)
    (hpath : ∀ p ∈ (B :: (rest ++ [A])).zip ((B :: (rest ++ [A])).drop 1),
        m ∉ segment ℝ p.1 p.2) :
    ∃ δ > 0, ∀ y z : ℂ, dist y m < δ → dist z m < δ →
      (∀ v ∈ (A :: B :: rest), v ≠ y) → (∀ v ∈ (A :: B :: rest), v ≠ z) →
      0 < cross (B - A) (y - A) → cross (B - A) (z - A) < 0 →
      ptWind y (A :: B :: rest) - ptWind z (A :: B :: rest) = 2 * Real.pi := by
  classical
  obtain ⟨hre0, him0, hAm⟩ := ratio_neg_real_of_openSegment A B m hAB hm
  -- (1) continuity of the tail sweep at `m`
  have hcont : ContinuousAt (fun w : ℂ => ptTurn w (B :: (rest ++ [A]))) m :=
    continuousAt_ptTurn (B :: (rest ++ [A])) m hpath
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨δ₁, hδ₁, hball₁⟩ :=
    Metric.continuousAt_iff.mp hcont (Real.pi / 4) (by linarith)
  -- (2) continuity of the sweep ratio at `m`, giving a negative real part nearby
  have hratio_cont : ContinuousAt (fun w : ℂ => ((B - w) / (A - w)).re) m := by
    have h1 : ContinuousAt (fun w : ℂ => (B - w) / (A - w)) m := by
      apply ContinuousAt.div
      · exact (continuous_const.sub continuous_id).continuousAt
      · exact (continuous_const.sub continuous_id).continuousAt
      · exact hAm
    exact Complex.continuous_re.continuousAt.comp h1
  obtain ⟨δ₂, hδ₂, hball₂⟩ :=
    Metric.continuousAt_iff.mp hratio_cont (-((B - m) / (A - m)).re) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro y z hy hz hvy hvz hcy hcz
  have hy₁ : dist y m < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy₂ : dist y m < δ₂ := lt_of_lt_of_le hy (min_le_right _ _)
  have hz₁ : dist z m < δ₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : dist z m < δ₂ := lt_of_lt_of_le hz (min_le_right _ _)
  -- the two points are off the vertices `A`, `B`
  have hAy : A - y ≠ 0 := sub_ne_zero.mpr (hvy A (by simp))
  have hAz : A - z ≠ 0 := sub_ne_zero.mpr (hvz A (by simp))
  -- (a) the real parts of the two sweep ratios are negative
  have hrey : ((B - y) / (A - y)).re < 0 := by
    have := hball₂ hy₂
    rw [Real.dist_eq] at this
    have h2 := abs_lt.mp this
    linarith [h2.2]
  have hrez : ((B - z) / (A - z)).re < 0 := by
    have := hball₂ hz₂
    rw [Real.dist_eq] at this
    have h2 := abs_lt.mp this
    linarith [h2.2]
  -- (b) the signs of the imaginary parts are the sides of the line
  have himy : 0 < ((B - y) / (A - y)).im := (div_sub_im_pos_iff A B y hAy).mpr hcy
  have himz : ((B - z) / (A - z)).im < 0 := by
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hpos
    · -- imaginary part zero forces the cross product to vanish
      have h0 := div_sub_im_mul_normSq A B z
      rw [← heq] at h0
      rw [cross_pos_vec A B z] at h0
      simp at h0
      linarith
    · have := (div_sub_im_pos_iff A B z hAz).mp hpos
      linarith
  -- (c) the two arguments are in `(π/2, π]` and `[-π, -π/2)`
  obtain ⟨hay1, hay2⟩ := arg_gt_pi_div_two _ hrey himy
  obtain ⟨haz1, haz2⟩ := arg_lt_neg_pi_div_two _ hrez himz
  -- (d) the tail sweeps differ by less than `π/2`
  have htaily : |ptTurn y (B :: (rest ++ [A])) - ptTurn m (B :: (rest ++ [A]))| < Real.pi / 4 := by
    have := hball₁ hy₁
    rwa [Real.dist_eq] at this
  have htailz : |ptTurn z (B :: (rest ++ [A])) - ptTurn m (B :: (rest ++ [A]))| < Real.pi / 4 := by
    have := hball₁ hz₁
    rwa [Real.dist_eq] at this
  have htail := abs_lt.mp htaily
  have htail' := abs_lt.mp htailz
  -- (e) the difference lies in `(π/2, 5π/2)` and is a multiple of `2π`
  rw [ptWind_cons_cons_split y A B rest, ptWind_cons_cons_split z A B rest]
  obtain ⟨n, hn⟩ := ptWind_int y (A :: B :: rest) hvy
  obtain ⟨k, hk⟩ := ptWind_int z (A :: B :: rest) hvz
  rw [ptWind_cons_cons_split y A B rest] at hn
  rw [ptWind_cons_cons_split z A B rest] at hk
  have hdiff : (Complex.arg ((B - y) / (A - y)) + ptTurn y (B :: (rest ++ [A])))
      - (Complex.arg ((B - z) / (A - z)) + ptTurn z (B :: (rest ++ [A])))
      = 2 * Real.pi * (n - k) := by
    rw [hn, hk]; push_cast; ring
  rw [hdiff]
  have hlow : Real.pi / 2 < 2 * Real.pi * ((n : ℝ) - k) := by
    rw [← hdiff]; linarith [htail.1, htail.2, htail'.1, htail'.2]
  have hhigh : 2 * Real.pi * ((n : ℝ) - k) < 5 * Real.pi / 2 := by
    rw [← hdiff]; linarith [htail.1, htail.2, htail'.1, htail'.2]
  have hn1 : ((n : ℝ) - k) = 1 := by
    have h1 : (0 : ℝ) < (n : ℝ) - k := by nlinarith
    have h2 : ((n : ℝ) - k) < 2 := by nlinarith
    have hz1 : (0 : ℤ) < n - k := by exact_mod_cast (by push_cast; linarith : (0:ℝ) < ((n - k : ℤ) : ℝ))
    have hz2 : (n - k : ℤ) < 2 := by exact_mod_cast (by push_cast; linarith : ((n - k : ℤ) : ℝ) < 2)
    have : n - k = 1 := by omega
    have := congrArg (fun i : ℤ => (i : ℝ)) this
    push_cast at this
    linarith
  rw [hn1]
  ring

end HexArea

end
