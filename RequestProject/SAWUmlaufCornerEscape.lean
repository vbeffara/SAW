import Mathlib
import RequestProject.SAWUmlaufCornerEscapeAux

/-!
# Escape from a strictly extreme corner of a polygon

This file contains the escape theorem itself; see
`RequestProject.SAWUmlaufCornerEscapeAux` for the elementary ingredients
(`HexArea.cdot`, `HexArea.cornerCone` and their basic properties) and for the
description of the construction.

Let `P` be a closed polygon and `u` a vertex of `P` which is *strictly extreme*:
some direction `d` has `0 < cdot d (y - u)` for every other vertex `y`.  Let
`n₁, n₂` be the two neighbours of `u`, so that the two cycle edges at `u` lie in
the closed convex cone `cornerCone u n₁ n₂`.  If `x₀` is seen from `u` in a
direction outside that cone and the segment `[u, x₀]` meets the polygon only at
`u`, then `ptWind x₀ P = 0`.

The proof is explicit: move from `x₀` along `[u, x₀]` to a point `z` so close to
`u` that `cdot d (z - u) < h` (with `h > 0` the minimum of `cdot d (y - u)` over
the other vertices), then run the straight ray from `z` in the direction
`-((n₁ - u) + (n₂ - u))`.  Along that ray `cdot d (· - u)` strictly decreases, so
the ray misses every cycle edge with both endpoints `≠ u` (all of whose points
have `cdot d (· - u) ≥ h`), and it misses the two edges at `u` as well, since a
meeting point would exhibit `x₀ - u` as a nonnegative combination of `n₁ - u`
and `n₂ - u`.  Far out on the ray the whole polygon lies in an open half plane,
so the winding vanishes there (`HexArea.ptWind_eq_zero_of_halfplane`), and
`HexArea.ptWind_eq_of_segment_avoids` transports this back to `x₀`.

Imported by `RequestProject.SAWUmlaufChordCorner`, hence on the live route to
the main theorem.
-/

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 1000000

/-- **The corner escape theorem.**  See the file header for the construction.
`u` is a strictly extreme vertex of the closed polygon `P` (witnessed by the
direction `d`), the two cycle edges of `P` at `u` lie in the corner cone spanned
by `n₁ - u` and `n₂ - u`, the point `x₀` is seen from `u` in a direction outside
that cone, and the segment `[u, x₀]` touches the polygon only at `u`.  Then the
polygon does not wind around `x₀`. -/
theorem ptWind_zero_of_extreme_corner
    (P : List ℂ) (u n₁ n₂ x₀ d : ℂ)
    (hx₀ : x₀ ≠ u) (hn₁ : n₁ ∈ P) (hn₂ : n₂ ∈ P) (hn₁u : n₁ ≠ u) (hn₂u : n₂ ≠ u)
    (hpos : ∀ y ∈ P, y ≠ u → 0 < cdot d (y - u))
    (hedge : ∀ e ∈ cycleEdges P, (e.1 ≠ u ∧ e.2 ≠ u) ∨
        segment ℝ e.1 e.2 ⊆ cornerCone u n₁ n₂)
    (hcone : x₀ ∉ cornerCone u n₁ n₂)
    (hsegu : ∀ e ∈ cycleEdges P, ∀ w ∈ segment ℝ u x₀,
        w ∈ segment ℝ e.1 e.2 → w = u) :
    ptWind x₀ P = 0 := by
  obtain ⟨h, hh, hmin⟩ := exists_pos_lower_bound P u d hpos
  set D := cdot d (x₀ - u) with hD
  set g := (n₁ - u) + (n₂ - u) with hg
  have hG : 0 < cdot d g := by
    rw [hg, cdot_add]
    have h1 := hpos n₁ hn₁ hn₁u
    have h2 := hpos n₂ hn₂ hn₂u
    linarith
  set G := cdot d g with hGdef
  -- Step 1: a point `z` on the segment `(u, x₀]` with `cdot d (z - u) < h`.
  obtain ⟨s₀, hs₀pos, hs₀le1, hs₀⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ s * D < h := by
    rcases le_or_gt D 0 with hD0 | hD0
    · refine ⟨1, one_pos, le_rfl, ?_⟩
      nlinarith
    · have hpos2 : 0 < h / (2 * D) := by positivity
      refine ⟨min 1 (h / (2 * D)), lt_min one_pos hpos2, min_le_left _ _, ?_⟩
      have h1 : min 1 (h / (2 * D)) ≤ h / (2 * D) := min_le_right _ _
      have h2 : (h / (2 * D)) * D = h / 2 := by field_simp
      nlinarith
  set z := u + s₀ • (x₀ - u) with hzdef
  -- Step 2: the far end `y` of the escaping ray.
  obtain ⟨T, hTpos, hT⟩ : ∃ T : ℝ, 0 < T ∧ s₀ * D - T * G < 0 := by
    refine ⟨(|s₀ * D| + 1) / G, by positivity, ?_⟩
    have hTG : ((|s₀ * D| + 1) / G) * G = |s₀ * D| + 1 := by field_simp
    have hle : s₀ * D ≤ |s₀ * D| := le_abs_self _
    linarith
  set y := z - T • g with hydef
  -- Every point of the ray has the form `z - t • g` with `0 ≤ t ≤ T`.
  have hray : ∀ w ∈ segment ℝ z y, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ w = z - t • g := by
    rintro w ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b * T, by positivity, by nlinarith, ?_⟩
    have hc : (a : ℂ) + b = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hab
    rw [hydef]
    push_cast [Complex.real_smul]
    linear_combination (norm := ring) z * hc
  -- Along the ray the linear functional strictly decreases.
  have hcdot_ray : ∀ t : ℝ, 0 ≤ t → cdot d ((z - t • g) - u) = s₀ * D - t * G := by
    intro t ht
    have hstep : (z - t • g) - u = s₀ • (x₀ - u) - t • g := by rw [hzdef]; ring
    rw [hstep, cdot_sub, cdot_smul, cdot_smul]
  -- The ray stays out of the corner cone: otherwise `x₀` would be in it.
  have hnotcone : ∀ t : ℝ, 0 ≤ t → (z - t • g) ∉ cornerCone u n₁ n₂ := by
    intro t ht hmem
    obtain ⟨α, β, hα, hβ, hw⟩ := hmem
    apply hcone
    refine ⟨(α + t) / s₀, (β + t) / s₀, by positivity, by positivity, ?_⟩
    have hs : (s₀ : ℂ) ≠ 0 := by simpa using (ne_of_gt hs₀pos)
    have hw' : s₀ • (x₀ - u) - t • g = α • (n₁ - u) + β • (n₂ - u) := by
      rw [← hw, hzdef]; ring
    rw [hg] at hw'
    push_cast [Complex.real_smul] at hw' ⊢
    field_simp
    linear_combination (norm := ring) hw'
  -- Hence the ray avoids every cycle edge of `P`.
  have havoid : ∀ e ∈ cycleEdges P, Disjoint (segment ℝ z y) (segment ℝ e.1 e.2) := by
    intro e he
    rw [Set.disjoint_left]
    intro w hw hwe
    obtain ⟨t, ht0, htT, rfl⟩ := hray w hw
    rcases hedge e he with ⟨he1, he2⟩ | hsub
    · obtain ⟨hm1, hm2⟩ := mem_of_mem_cycleEdges P e he
      have hge : h ≤ cdot d ((z - t • g) - u) :=
        cdot_ge_of_mem_segment u d e.1 e.2 h (hmin e.1 hm1 he1) (hmin e.2 hm2 he2) _ hwe
      rw [hcdot_ray t ht0] at hge
      nlinarith
    · exact hnotcone t ht0 (hsub hwe)
  have h1 : ptWind z P = ptWind y P := ptWind_eq_of_segment_avoids P z y havoid
  -- Far out on the ray the whole polygon is in an open half plane.
  have h2 : ptWind y P = 0 := by
    refine ptWind_eq_zero_of_halfplane y ((starRingEnd ℂ) d) P ?_
    intro v hv
    have hyu : cdot d (y - u) = s₀ * D - T * G := by
      rw [hydef]; exact hcdot_ray T (le_of_lt hTpos)
    have hsplit : ((v - y) * (starRingEnd ℂ) d).re = cdot d (v - u) - cdot d (y - u) := by
      have hvy : v - y = (v - u) - (y - u) := by ring
      rw [hvy]
      exact cdot_sub d (v - u) (y - u)
    rw [hsplit, hyu]
    by_cases hvu : v = u
    · subst hvu; simp [cdot]; linarith
    · have := hmin v hv hvu
      linarith
  -- Finally the initial segment `[x₀, z]` avoids every cycle edge as well.
  have havoid2 : ∀ e ∈ cycleEdges P, Disjoint (segment ℝ x₀ z) (segment ℝ e.1 e.2) := by
    intro e he
    rw [Set.disjoint_left]
    rintro w ⟨a, b, ha, hb, hab, rfl⟩ hwe
    have hc : (a : ℂ) + b = 1 := by exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hab
    set σ := a + b * s₀ with hσ
    have hwσ : a • x₀ + b • z = u + σ • (x₀ - u) := by
      rw [hzdef, hσ]
      push_cast [Complex.real_smul]
      linear_combination (norm := ring) u * hc
    have hσpos : 0 < σ := by
      rcases lt_or_eq_of_le hb with hb' | hb'
      · nlinarith
      · nlinarith [hb'.symm]
    have hσle : σ ≤ 1 := by nlinarith
    have hmemseg : a • x₀ + b • z ∈ segment ℝ u x₀ := by
      rw [hwσ]
      refine ⟨1 - σ, σ, by linarith, le_of_lt hσpos, by ring, ?_⟩
      push_cast [Complex.real_smul]
      ring
    have heq := hsegu e he _ hmemseg hwe
    rw [hwσ] at heq
    have hcontra : σ • (x₀ - u) = 0 := by
      have hzz : u + σ • (x₀ - u) - u = u - u := by rw [heq]
      simpa using hzz
    rcases smul_eq_zero.mp hcontra with h' | h'
    · exact absurd h' (ne_of_gt hσpos)
    · exact hx₀ (sub_eq_zero.mp h')
  have h3 : ptWind x₀ P = ptWind z P := ptWind_eq_of_segment_avoids P x₀ z havoid2
  rw [h3, h1, h2]

end HexArea

end
