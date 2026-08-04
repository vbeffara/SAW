import Mathlib
import RequestProject.SAWUmlaufCorridorBlock
import RequestProject.SAWUmlaufEdgeTailConvex
import RequestProject.SAWUmlaufCrossingBounds

/-!
# Selecting the single corridor block

This file closes the last geometric residue of the Umlaufsatz finite-detour
construction.  It is imported by `SAWUmlaufMixedSelection`, hence lies on the
live route
`SAWUmlaufDetourConstruction → SAWUmlaufArcDetour → SAWUmlaufArcInduction →
SAWUmlaufArcEscape → SAWUmlaufPolygon`.

Earlier rounds tried to cover the compact crossing set by *many* small
same-side blocks, which forced an awkward parity analysis: a single transverse
crossing has its two boundary values on opposite sides of the edge.  The
corridor construction removes that problem entirely.  Because `corridor \ edge`
is path connected (proved in `SAWUmlaufCorridorPath`), **one** block suffices:

* `s₀` is the largest edge parameter attained by a crossing;
* the initial piece `edgeCore = [a, a + s₀ (b-a)]` misses the old tail, since
  the tail meets `[a,b]` in a convex set containing `b`
  (`SAWUmlaufEdgeTailConvex`) while the deepest crossing point is tail free;
* compactness gives a corridor of positive width around `edgeCore` which is
  still tail free;
* continuity places one parameter just before the first crossing and one just
  after the last crossing, both with values in the corridor and off the edge.
-/

open Real Complex Topology Metric

noncomputable section

namespace HexArea

/-! ### The initial piece of the new edge reached by the crossings -/

/-- The initial piece of the new edge, up to parameter `s₀`. -/
def edgeCore (a u : ℂ) (s₀ : ℝ) : Set ℂ :=
  (fun s : ℝ => edgePt a u s 0) '' Set.Icc 0 s₀

lemma continuous_edgePt_param (a u : ℂ) :
    Continuous (fun s : ℝ => edgePt a u s 0) := by
  unfold edgePt
  fun_prop

lemma isCompact_edgeCore (a u : ℂ) (s₀ : ℝ) : IsCompact (edgeCore a u s₀) :=
  isCompact_Icc.image (continuous_edgePt_param a u)

lemma edgeCore_subset_segment (a u : ℂ) (hu : u ≠ 0) {s₀ : ℝ} (h1 : s₀ ≤ 1) :
    edgeCore a u s₀ ⊆ segment ℝ a (a + u) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_segment_iff_edgeCoords a u _ hu, edgeParam_edgePt a u hu,
    edgeNormal_edgePt a u hu]
  exact ⟨rfl, hs.1, le_trans hs.2 h1⟩

/-- Points of the edge line with parameters between `s` and `1` lie on the
segment joining the two corresponding edge points. -/
lemma edgePt_mem_segment_between (a u : ℂ) {s s' : ℝ} (h : s ≤ s') (h' : s' ≤ 1) :
    edgePt a u s' 0 ∈ segment ℝ (edgePt a u s 0) (edgePt a u 1 0) := by
  rw [segment_eq_image']
  rcases eq_or_lt_of_le h' with hs'1 | hs'1
  · subst hs'1
    refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    dsimp only
    simp only [edgePt, Complex.real_smul]
    push_cast
    ring
  · have hs1 : s < 1 := lt_of_le_of_lt h hs'1
    refine ⟨(s' - s) / (1 - s), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · have hne : (1 : ℝ) - s ≠ 0 := by linarith
      have hC : (1 : ℂ) - (s : ℂ) ≠ 0 := by
        have h0 := Complex.ofReal_ne_zero.mpr hne
        push_cast at h0
        exact h0
      have hθ : ((s' : ℂ) - (s : ℂ)) / ((1 : ℂ) - (s : ℂ)) * ((1 : ℂ) - (s : ℂ))
          = (s' : ℂ) - (s : ℂ) := div_mul_cancel₀ _ hC
      dsimp only
      simp only [edgePt, Complex.real_smul]
      push_cast
      linear_combination u * hθ

/-! ### Corridor clearance -/

/-- Every corridor point is close to the initial piece of the edge. -/
lemma exists_edgeCore_close (a u : ℂ) (hu : u ≠ 0) {s₀ η : ℝ}
    (hs₀ : 0 ≤ s₀) (hη : 0 < η) {z : ℂ}
    (hz : z ∈ corridorSet a u (s₀ + η) η) :
    ∃ w ∈ edgeCore a u s₀, dist z w < 2 * η * ‖u‖ := by
  obtain ⟨h1, h2, h3⟩ := hz
  set α := edgeParam a u z with hα
  set β := edgeNormal a u z with hβ
  set s := max 0 (min α s₀) with hs
  have hs0 : 0 ≤ s := le_max_left _ _
  have hss₀ : s ≤ s₀ := max_le hs₀ (min_le_right _ _)
  have hdiff : |α - s| ≤ η := by
    rcases le_or_gt α 0 with hle | hgt
    · have : s = 0 := by
        simp only [hs]
        have : min α s₀ ≤ 0 := le_trans (min_le_left _ _) hle
        exact max_eq_left this
      rw [this, sub_zero, abs_of_nonpos hle]
      linarith
    · rcases le_or_gt α s₀ with hle2 | hgt2
      · have : s = α := by
          simp only [hs, min_eq_left hle2]
          exact max_eq_right (le_of_lt hgt)
        rw [this]; simp; linarith
      · have : s = s₀ := by
          simp only [hs, min_eq_right (le_of_lt hgt2)]
          exact max_eq_right hs₀
        rw [this, abs_of_pos (by linarith)]
        linarith
  refine ⟨edgePt a u s 0, ⟨s, ⟨hs0, hss₀⟩, rfl⟩, ?_⟩
  have hzeq : z = edgePt a u α β := (edgePt_coords a u z hu).symm
  have hd : dist z (edgePt a u s 0)
      = ‖(((α - s : ℝ) : ℂ) + ((β : ℝ) : ℂ) * Complex.I)‖ * ‖u‖ := by
    rw [dist_eq_norm]
    nth_rewrite 1 [hzeq]
    simp only [edgePt]
    rw [show (a + ((α : ℂ) + (β : ℂ) * Complex.I) * u)
        - (a + ((s : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) * u)
      = ((((α - s : ℝ)) : ℂ) + ((β : ℝ) : ℂ) * Complex.I) * u by push_cast; ring]
    exact norm_mul _ _
  have hnormle : ‖(((α - s : ℝ) : ℂ) + ((β : ℝ) : ℂ) * Complex.I)‖
      ≤ |α - s| + |β| := by
    calc ‖(((α - s : ℝ) : ℂ) + ((β : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖(((α - s : ℝ) : ℂ))‖ + ‖((β : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |α - s| + |β| := by
            simp only [Complex.norm_mul, Complex.norm_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs]
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hlt : ‖(((α - s : ℝ) : ℂ) + ((β : ℝ) : ℂ) * Complex.I)‖ < 2 * η := by
    have : |α - s| + |β| < 2 * η := by linarith
    linarith
  rw [hd]
  calc ‖(((α - s : ℝ) : ℂ) + ((β : ℝ) : ℂ) * Complex.I)‖ * ‖u‖
      < (2 * η) * ‖u‖ := by exact mul_lt_mul_of_pos_right hlt hupos
    _ = 2 * η * ‖u‖ := by ring

/-- A corridor of small enough width around a tail-free initial edge piece is
itself tail free. -/
lemma exists_corridor_clearance (a u : ℂ) (hu : u ≠ 0) {s₀ : ℝ} (hs₀ : 0 ≤ s₀)
    (T : Set ℂ) (hT : IsClosed T) (hfree : ∀ w ∈ edgeCore a u s₀, w ∉ T) :
    ∃ η : ℝ, 0 < η ∧ ∀ z ∈ corridorSet a u (s₀ + η) η, z ∉ T := by
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_edgeCore a u s₀).exists_thickening_subset_open hT.isOpen_compl
      (fun w hw => hfree w hw)
  refine ⟨δ / (2 * (‖u‖ + 1)), by positivity, ?_⟩
  intro z hz
  obtain ⟨w, hw, hdist⟩ :=
    exists_edgeCore_close a u hu hs₀ (by positivity) hz
  have hbound : 2 * (δ / (2 * (‖u‖ + 1))) * ‖u‖ ≤ δ := by
    have hpos : (0 : ℝ) < ‖u‖ + 1 := by positivity
    have heq : 2 * (δ / (2 * (‖u‖ + 1))) * ‖u‖ = δ * ‖u‖ / (‖u‖ + 1) := by
      field_simp
    rw [heq, div_le_iff₀ hpos]
    nlinarith [norm_nonneg u, hδ.le]
  exact hsub (Metric.mem_thickening_iff.mpr ⟨w, hw, by linarith⟩)

/-! ### The deepest crossing parameter -/

/-- The crossings reach a maximal edge parameter, attained at a crossing. -/
lemma exists_max_crossing_param {x y : ℂ} (γ : Path x y) (a b : ℂ)
    (hab : a ≠ b)
    (hne : (pathHitTimes γ (segment ℝ a b)).Nonempty) :
    ∃ s₀ : ℝ, 0 ≤ s₀ ∧ s₀ ≤ 1 ∧
      (∀ t ∈ pathHitTimes γ (segment ℝ a b),
        edgeParam a (b - a) (γ t) ≤ s₀) ∧
      (∃ tm ∈ pathHitTimes γ (segment ℝ a b),
        γ tm = edgePt a (b - a) s₀ 0) := by
  classical
  have hcomp := isCompact_pathHitTimes_segment γ a b
  have hcont : ContinuousOn (fun t : unitInterval => edgeParam a (b - a) (γ t))
      (pathHitTimes γ (segment ℝ a b)) :=
    ((continuous_edgeParam a (b - a)).comp γ.continuous).continuousOn
  obtain ⟨tm, htm, hmax⟩ := hcomp.exists_isMaxOn hne hcont
  have hmem : γ tm ∈ segment ℝ a b := htm
  rw [mem_segment_iff_edgeCoords' a b _ hab] at hmem
  refine ⟨edgeParam a (b - a) (γ tm), hmem.2.1, hmem.2.2, fun t ht => hmax ht, ?_⟩
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have heq : edgePt a (b - a) (edgeParam a (b - a) (γ tm)) 0 = γ tm := by
    have h := edgePt_coords a (b - a) (γ tm) hu
    rwa [hmem.1] at h
  exact ⟨tm, htm, heq.symm⟩

/-! ### Parameter selection just outside the crossing window -/

/-- A point of an open set reached at a positive parameter is reached at some
strictly smaller parameter as well. -/
lemma exists_lt_mem_preimage {x y : ℂ} (γ : Path x y) (U : Set ℂ) (hU : IsOpen U)
    (t : unitInterval) (ht : γ t ∈ U) (h0 : (0 : ℝ) < (t : ℝ)) :
    ∃ s : unitInterval, (s : ℝ) < (t : ℝ) ∧ γ s ∈ U := by
  have hopen : IsOpen (γ ⁻¹' U) := hU.preimage γ.continuous
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen t ht
  set c : ℝ := min (ε / 2) ((t : ℝ) / 2) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hcle : c ≤ (t : ℝ) / 2 := min_le_right _ _
  have hmem : (t : ℝ) - c ∈ unitInterval := by
    constructor
    · linarith [t.prop.1, t.prop.2]
    · linarith [t.prop.2, hcpos]
  refine ⟨⟨(t : ℝ) - c, hmem⟩, by show (t : ℝ) - c < (t : ℝ); linarith, ?_⟩
  apply hball
  rw [Metric.mem_ball, Subtype.dist_eq]
  have : dist ((t : ℝ) - c) (t : ℝ) = c := by
    rw [Real.dist_eq]; rw [show (t : ℝ) - c - (t : ℝ) = -c by ring, abs_neg,
      abs_of_pos hcpos]
  rw [this]
  calc c ≤ ε / 2 := min_le_left _ _
    _ < ε := by linarith

/-- A point of an open set reached at a parameter below `1` is reached at some
strictly larger parameter as well. -/
lemma exists_gt_mem_preimage {x y : ℂ} (γ : Path x y) (U : Set ℂ) (hU : IsOpen U)
    (t : unitInterval) (ht : γ t ∈ U) (h1 : (t : ℝ) < 1) :
    ∃ s : unitInterval, (t : ℝ) < (s : ℝ) ∧ γ s ∈ U := by
  have hopen : IsOpen (γ ⁻¹' U) := hU.preimage γ.continuous
  rw [Metric.isOpen_iff] at hopen
  obtain ⟨ε, hε, hball⟩ := hopen t ht
  set c : ℝ := min (ε / 2) ((1 - (t : ℝ)) / 2) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hcle : c ≤ (1 - (t : ℝ)) / 2 := min_le_right _ _
  have hmem : (t : ℝ) + c ∈ unitInterval := by
    constructor
    · linarith [t.prop.1, hcpos.le]
    · linarith
  refine ⟨⟨(t : ℝ) + c, hmem⟩, by show (t : ℝ) < (t : ℝ) + c; linarith, ?_⟩
  apply hball
  rw [Metric.mem_ball, Subtype.dist_eq]
  have : dist ((t : ℝ) + c) (t : ℝ) = c := by
    rw [Real.dist_eq]; rw [show (t : ℝ) + c - (t : ℝ) = c by ring, abs_of_pos hcpos]
  rw [this]
  calc c ≤ ε / 2 := min_le_left _ _
    _ < ε := by linarith

/-! ### The initial edge piece is tail free -/

/-- If the deepest crossing point avoids the old tail, so does the whole
initial piece of the new edge.  This uses convexity of the tail intersection. -/
lemma edgeCore_avoids_tail (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L)) (hab : a ≠ b) {s₀ : ℝ}
    (hs₀0 : 0 ≤ s₀) (hs₀1 : s₀ ≤ 1)
    (hdeep : edgePt a (b - a) s₀ 0 ∉ chainCarrier (b :: L)) :
    ∀ w ∈ edgeCore a (b - a) s₀, w ∉ chainCarrier (b :: L) := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  rintro _ ⟨s, hs, rfl⟩ hmem
  rcases L with _ | ⟨c, L'⟩
  · simp [chainCarrier_singleton] at hmem
  · have hb : b ∈ chainCarrier (b :: c :: L') := terminal_mem_chainCarrier b c L'
    have hbseg : b ∈ segment ℝ a b := right_mem_segment ℝ a b
    have hwseg : edgePt a (b - a) s 0 ∈ segment ℝ a b := by
      rw [mem_segment_iff_edgeCoords' a b _ hab, edgeParam_edgePt a (b - a) hu,
        edgeNormal_edgePt a (b - a) hu]
      exact ⟨rfl, hs.1, le_trans hs.2 hs₀1⟩
    have hconv := segment_inter_tail_convex a b (c :: L') hsimple
    have hone : edgePt a (b - a) 1 0 = b := by
      simp [edgePt]
    have hbetween : edgePt a (b - a) s₀ 0 ∈
        segment ℝ (edgePt a (b - a) s 0) (edgePt a (b - a) 1 0) :=
      edgePt_mem_segment_between a (b - a) hs.2 hs₀1
    rw [hone] at hbetween
    have := hconv.segment_subset ⟨hwseg, hmem⟩ ⟨hbseg, hb⟩ hbetween
    exact hdeep this.2

/-! ### The corridor block -/

/-- **The single corridor block covering all crossings.**  This is the final
geometric input of the Umlaufsatz finite-detour construction. -/
lemma exists_corridorAttachment_covering
    (a b : ℂ) (L : List ℂ)
    (hsimple : PlaneArcSimple (a :: b :: L))
    {x y : ℂ} (γ : Path x y)
    (hγtail : ∀ q, γ q ∈ (chainCarrier (b :: L))ᶜ)
    (hx : x ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hy : y ∈ (chainCarrier (a :: b :: L))ᶜ)
    (hhit : (pathHitTimes γ (segment ℝ a b)).Nonempty) :
    ∃ A : CorridorAttachment γ a b (chainCarrier (b :: L)),
      ∀ t ∈ pathHitTimes γ (segment ℝ a b), A.left < t ∧ t < A.right := by
  have hab : a ≠ b := hsimple.head_ne_of_cons_cons
  have hu : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hxseg : x ∉ segment ℝ a b := by
    intro h; exact hx (by rw [chainCarrier_cons_cons]; exact Or.inl h)
  have hyseg : y ∉ segment ℝ a b := by
    intro h; exact hy (by rw [chainCarrier_cons_cons]; exact Or.inl h)
  obtain ⟨l₀, r₀, hl₀pos, -, hr₀lt, hinner⟩ :=
    exists_pathHitTimes_segment_inner_bounds γ a b hxseg hyseg
  obtain ⟨s₀, hs₀0, hs₀1, hs₀max, tm, htm, hγtm⟩ :=
    exists_max_crossing_param γ a b hab hhit
  have hdeep : edgePt a (b - a) s₀ 0 ∉ chainCarrier (b :: L) := by
    rw [← hγtm]; exact hγtail tm
  have hfree := edgeCore_avoids_tail a b L hsimple hab hs₀0 hs₀1 hdeep
  obtain ⟨η, hη, hclear⟩ :=
    exists_corridor_clearance a (b - a) hu hs₀0 (chainCarrier (b :: L))
      (isClosed_chainCarrier _) hfree
  set C := corridorSet a (b - a) (s₀ + η) η with hC
  have hCopen : IsOpen C := isOpen_corridorSet _ _ _ _
  set H := pathHitTimes γ (segment ℝ a b) with hH
  have hHcomp : IsCompact H := isCompact_pathHitTimes_segment γ a b
  have htmin_mem : sInf H ∈ H := hHcomp.sInf_mem hhit
  have htmax_mem : sSup H ∈ H := hHcomp.sSup_mem hhit
  have hmemC : ∀ t ∈ H, γ t ∈ C := by
    intro t ht
    have h1 : γ t ∈ segment ℝ a b := ht
    rw [mem_segment_iff_edgeCoords' a b _ hab] at h1
    refine ⟨by linarith [h1.2.1], ?_, ?_⟩
    · have := hs₀max t ht; linarith
    · rw [h1.1]; simpa using hη
  -- the crossing window is strictly inside the parameter interval
  have hminpos : (0 : ℝ) < ((sInf H : unitInterval) : ℝ) := by
    have h1 := (hinner (sInf H) htmin_mem).1
    have h2 : (0 : ℝ) < (l₀ : ℝ) := hl₀pos
    have : (l₀ : ℝ) < ((sInf H : unitInterval) : ℝ) := h1
    linarith
  have hmaxlt : ((sSup H : unitInterval) : ℝ) < 1 := by
    have h1 := (hinner (sSup H) htmax_mem).2
    have h2 : (r₀ : ℝ) < 1 := hr₀lt
    have : ((sSup H : unitInterval) : ℝ) < (r₀ : ℝ) := h1
    linarith
  obtain ⟨left, hleftlt, hleftC⟩ :=
    exists_lt_mem_preimage γ C hCopen (sInf H) (hmemC _ htmin_mem) hminpos
  obtain ⟨right, hrightgt, hrightC⟩ :=
    exists_gt_mem_preimage γ C hCopen (sSup H) (hmemC _ htmax_mem) hmaxlt
  -- boundary values are off the new edge
  have hleftoff : γ left ∉ segment ℝ a b := by
    intro hmem
    have : left ∈ H := hmem
    have hle : sInf H ≤ left := csInf_le hHcomp.bddBelow this
    have : ((sInf H : unitInterval) : ℝ) ≤ (left : ℝ) := hle
    linarith
  have hrightoff : γ right ∉ segment ℝ a b := by
    intro hmem
    have : right ∈ H := hmem
    have hle : right ≤ sSup H := le_csSup hHcomp.bddAbove this
    have : (right : ℝ) ≤ ((sSup H : unitInterval) : ℝ) := hle
    linarith
  have hminmax : ((sInf H : unitInterval) : ℝ) ≤ ((sSup H : unitInterval) : ℝ) := by
    have : sInf H ≤ sSup H := csInf_le_csSup hHcomp.bddBelow hHcomp.bddAbove hhit
    exact this
  have hlr : left ≤ right := by
    have : (left : ℝ) ≤ (right : ℝ) := by linarith
    exact this
  refine ⟨{ left := left
            right := right
            left_le_right := hlr
            reach := s₀ + η
            width := η
            reach_pos := by linarith
            width_pos := hη
            left_mem := hleftC
            right_mem := hrightC
            left_off := hleftoff
            right_off := hrightoff
            clear := hclear }, ?_⟩
  intro t ht
  constructor
  · show (left : ℝ) < (t : ℝ)
    have hle : sInf H ≤ t := csInf_le hHcomp.bddBelow ht
    have : ((sInf H : unitInterval) : ℝ) ≤ (t : ℝ) := hle
    linarith
  · show (t : ℝ) < (right : ℝ)
    have hle : t ≤ sSup H := le_csSup hHcomp.bddAbove ht
    have : (t : ℝ) ≤ ((sSup H : unitInterval) : ℝ) := hle
    linarith

end HexArea
