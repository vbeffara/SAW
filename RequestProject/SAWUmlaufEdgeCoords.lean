import Mathlib
import RequestProject.SAWUmlaufHalfPlaneDetour

/-!
# Affine coordinates adapted to the newly adjoined edge

This file is preparation for the *corridor* construction that closes the last
geometric residue of the Umlaufsatz detour (`SAWUmlaufCorridorSelect`), and it
is imported on the live chain
`SAWUmlaufDetourConstruction → SAWUmlaufArcDetour → SAWUmlaufArcInduction →
SAWUmlaufArcEscape → SAWUmlaufPolygon`.

Given the base point `a` and the direction `u = b - a` of the new edge, every
complex number `z` is written uniquely as `z = a + (α + βi) u`.  The two real
coordinates `α = edgeParam a u z` and `β = edgeNormal a u z` are ℝ-affine in
`z`, so all the sets used by the corridor argument are convex and open, and the
closed segment `[a, a+u]` becomes the coordinate box `β = 0`, `0 ≤ α ≤ 1`.

The *corridor* is the open coordinate rectangle `-η < α < s₁`, `|β| < η`.  Its
left overhang `α < 0` is what makes `corridor \ segment` path connected: one can
always walk around the free endpoint `a`.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-- Coordinate of `z` along the oriented edge direction `u` based at `a`. -/
def edgeParam (a u z : ℂ) : ℝ := ((z - a) * star u).re / Complex.normSq u

/-- Coordinate of `z` transverse to the oriented edge direction `u`. -/
def edgeNormal (a u z : ℂ) : ℝ := ((z - a) * star u).im / Complex.normSq u

/-- The point with prescribed edge coordinates. -/
def edgePt (a u : ℂ) (s t : ℝ) : ℂ := a + ((s : ℂ) + (t : ℂ) * Complex.I) * u

lemma edgeNormal_eq_detourSide (a u z : ℂ) :
    edgeNormal a u z = detourSide a u z / Complex.normSq u := rfl

@[simp] lemma edgeParam_edgePt (a u : ℂ) (hu : u ≠ 0) (s t : ℝ) :
    edgeParam a u (edgePt a u s t) = s := by
  have hn : Complex.normSq u ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hu
  simp only [edgeParam, edgePt, add_sub_cancel_left]
  have : ((((s : ℂ) + (t : ℂ) * Complex.I) * u) * star u).re
      = s * Complex.normSq u := by
    simp [Complex.ext_iff, Complex.normSq_apply, Complex.star_def,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [this]
  field_simp

@[simp] lemma edgeNormal_edgePt (a u : ℂ) (hu : u ≠ 0) (s t : ℝ) :
    edgeNormal a u (edgePt a u s t) = t := by
  have hn : Complex.normSq u ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hu
  simp only [edgeNormal, edgePt, add_sub_cancel_left]
  have : ((((s : ℂ) + (t : ℂ) * Complex.I) * u) * star u).im
      = t * Complex.normSq u := by
    simp [Complex.ext_iff, Complex.normSq_apply, Complex.star_def,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [this]
  field_simp

/-- The two coordinates determine the point. -/
lemma edgePt_coords (a u z : ℂ) (hu : u ≠ 0) :
    edgePt a u (edgeParam a u z) (edgeNormal a u z) = z := by
  have hn : (Complex.normSq u : ℂ) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hu
  have hstar : (z - a) * star u * u = (z - a) * (Complex.normSq u : ℂ) := by
    have h : (star u : ℂ) * u = (Complex.normSq u : ℂ) := by
      rw [mul_comm]; simpa using Complex.mul_conj u
    calc (z - a) * star u * u = (z - a) * (star u * u) := by ring
      _ = _ := by rw [h]
  have key : ((edgeParam a u z : ℂ) + (edgeNormal a u z : ℂ) * Complex.I) * u
      = z - a := by
    simp only [edgeParam, edgeNormal]
    push_cast
    rw [div_mul_eq_mul_div, div_add_div_same, Complex.re_add_im,
      div_mul_eq_mul_div, hstar]
    field_simp
  rw [edgePt, key]
  ring

lemma continuous_edgeParam (a u : ℂ) : Continuous (edgeParam a u) := by
  unfold edgeParam
  fun_prop

lemma continuous_edgeNormal (a u : ℂ) : Continuous (edgeNormal a u) := by
  unfold edgeNormal
  fun_prop

/-- `edgeParam` is ℝ-affine. -/
lemma edgeParam_smul_add (a u p q : ℂ) (r s : ℝ) (hrs : r + s = 1) :
    edgeParam a u (r • p + s • q) = r * edgeParam a u p + s * edgeParam a u q := by
  have hp : (r • p + s • q) - a = r • (p - a) + s • (q - a) := by
    have h : ((r : ℂ) + (s : ℂ)) = 1 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hrs
    simp only [Complex.real_smul]
    linear_combination (a : ℂ) * h
  simp only [edgeParam, hp]
  simp [Complex.real_smul, add_mul, Complex.add_re, Complex.mul_re, Complex.mul_im]
  ring

/-- `edgeNormal` is ℝ-affine. -/
lemma edgeNormal_smul_add (a u p q : ℂ) (r s : ℝ) (hrs : r + s = 1) :
    edgeNormal a u (r • p + s • q) = r * edgeNormal a u p + s * edgeNormal a u q := by
  have hp : (r • p + s • q) - a = r • (p - a) + s • (q - a) := by
    have h : ((r : ℂ) + (s : ℂ)) = 1 := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hrs
    simp only [Complex.real_smul]
    linear_combination (a : ℂ) * h
  simp only [edgeNormal, hp]
  simp [Complex.real_smul, add_mul, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

lemma edgeParam_affinePath (a u p q : ℂ) (t : unitInterval) :
    edgeParam a u (affinePath p q t)
      = (1 - (t : ℝ)) * edgeParam a u p + (t : ℝ) * edgeParam a u q := by
  rw [affinePath_apply]
  exact edgeParam_smul_add a u p q _ _ (by ring)

lemma edgeNormal_affinePath (a u p q : ℂ) (t : unitInterval) :
    edgeNormal a u (affinePath p q t)
      = (1 - (t : ℝ)) * edgeNormal a u p + (t : ℝ) * edgeNormal a u q := by
  rw [affinePath_apply]
  exact edgeNormal_smul_add a u p q _ _ (by ring)

/-- Coordinate description of the closed edge. -/
lemma mem_segment_iff_edgeCoords (a u z : ℂ) (hu : u ≠ 0) :
    z ∈ segment ℝ a (a + u) ↔
      edgeNormal a u z = 0 ∧ 0 ≤ edgeParam a u z ∧ edgeParam a u z ≤ 1 := by
  constructor
  · intro hz
    rw [segment_eq_image'] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    dsimp only
    have hsu : a + s • (a + u - a) = edgePt a u s 0 := by
      simp [edgePt, Complex.real_smul]
    rw [hsu, edgeParam_edgePt a u hu, edgeNormal_edgePt a u hu]
    exact ⟨rfl, hs.1, hs.2⟩
  · rintro ⟨hβ, h0, h1⟩
    rw [segment_eq_image']
    refine ⟨edgeParam a u z, ⟨h0, h1⟩, ?_⟩
    have h := edgePt_coords a u z hu
    rw [hβ] at h
    simp only [edgePt, Complex.ofReal_zero, zero_mul, add_zero] at h
    dsimp only
    rw [show a + u - a = u by ring, Complex.real_smul]
    exact h

/-- Coordinate description of the closed edge, endpoint form. -/
lemma mem_segment_iff_edgeCoords' (a b z : ℂ) (hab : a ≠ b) :
    z ∈ segment ℝ a b ↔
      edgeNormal a (b - a) z = 0 ∧ 0 ≤ edgeParam a (b - a) z ∧
        edgeParam a (b - a) z ≤ 1 := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h := mem_segment_iff_edgeCoords a (b - a) z hu
  rwa [show a + (b - a) = b by ring] at h

/-- Strict lower bounds are preserved by convex combinations. -/
lemma real_convex_lt_comb {r s x y c : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r + s = 1) (hx : c < x) (hy : c < y) : c < r * x + s * y := by
  rcases lt_or_eq_of_le hr with h | h
  · have h1 : r * c < r * x := mul_lt_mul_of_pos_left hx h
    have h2 : s * c ≤ s * y := mul_le_mul_of_nonneg_left (le_of_lt hy) hs
    have h3 : r * c + s * c = c := by rw [← add_mul, hrs, one_mul]
    linarith
  · have hr0 : r = 0 := h.symm
    have hs1 : s = 1 := by linarith
    simp [hr0, hs1]; linarith

/-- Strict upper bounds are preserved by convex combinations. -/
lemma real_convex_comb_lt {r s x y c : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r + s = 1) (hx : x < c) (hy : y < c) : r * x + s * y < c := by
  have := real_convex_lt_comb (r := r) (s := s) (x := -x) (y := -y) (c := -c)
    hr hs hrs (by linarith) (by linarith)
  nlinarith

/-- The open coordinate rectangle used as a detour corridor around the new
edge.  Its `α < 0` part lies strictly beyond the free endpoint `a`. -/
def corridorSet (a u : ℂ) (s₁ η : ℝ) : Set ℂ :=
  {z | -η < edgeParam a u z ∧ edgeParam a u z < s₁ ∧ |edgeNormal a u z| < η}

lemma mem_corridorSet_iff (a u : ℂ) (s₁ η : ℝ) (z : ℂ) :
    z ∈ corridorSet a u s₁ η ↔
      -η < edgeParam a u z ∧ edgeParam a u z < s₁ ∧ |edgeNormal a u z| < η :=
  Iff.rfl

lemma convex_corridorSet (a u : ℂ) (s₁ η : ℝ) :
    Convex ℝ (corridorSet a u s₁ η) := by
  intro p hp q hq r s hr hs hrs
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeParam_smul_add a u p q r s hrs]
    exact real_convex_lt_comb hr hs hrs hp1 hq1
  · rw [edgeParam_smul_add a u p q r s hrs]
    exact real_convex_comb_lt hr hs hrs hp2 hq2
  · rw [edgeNormal_smul_add a u p q r s hrs]
    have h1 : |r * edgeNormal a u p + s * edgeNormal a u q|
        ≤ r * |edgeNormal a u p| + s * |edgeNormal a u q| := by
      calc |r * edgeNormal a u p + s * edgeNormal a u q|
          ≤ |r * edgeNormal a u p| + |s * edgeNormal a u q| := abs_add_le _ _
        _ = r * |edgeNormal a u p| + s * |edgeNormal a u q| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hs]
    have h2 : r * |edgeNormal a u p| + s * |edgeNormal a u q| < η :=
      real_convex_comb_lt hr hs hrs hp3 hq3
    linarith

lemma isOpen_corridorSet (a u : ℂ) (s₁ η : ℝ) :
    IsOpen (corridorSet a u s₁ η) := by
  have h1 : IsOpen {z : ℂ | -η < edgeParam a u z} :=
    isOpen_lt continuous_const (continuous_edgeParam a u)
  have h2 : IsOpen {z : ℂ | edgeParam a u z < s₁} :=
    isOpen_lt (continuous_edgeParam a u) continuous_const
  have h3 : IsOpen {z : ℂ | |edgeNormal a u z| < η} :=
    isOpen_lt ((continuous_edgeNormal a u).abs) continuous_const
  have : corridorSet a u s₁ η =
      {z : ℂ | -η < edgeParam a u z} ∩
        ({z : ℂ | edgeParam a u z < s₁} ∩ {z : ℂ | |edgeNormal a u z| < η}) := by
    ext z; simp [corridorSet]
  rw [this]
  exact h1.inter (h2.inter h3)

/-- Points of the closed edge with parameter at most `s₀` lie in the corridor. -/
lemma edgePt_mem_corridorSet (a u : ℂ) (hu : u ≠ 0) {s₀ s₁ η : ℝ} (hη : 0 < η)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₀) (hs₁ : s₀ < s₁) :
    edgePt a u s 0 ∈ corridorSet a u s₁ η := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [edgeParam_edgePt a u hu, edgeNormal_edgePt a u hu] <;> linarith

end HexArea
