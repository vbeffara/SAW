import Mathlib
import RequestProject.SAWUmlaufJordanStep
import RequestProject.SAWUmlaufWindJump
import RequestProject.SAWUmlaufCornerEscape

/-!
# `SAWUmlaufExtremeOrient` — the orientation of a polygon at an extreme corner

The last geometric input of the corrected Meisters chain is
`chord_piece_orient` (`RequestProject.SAWUmlaufChordLiftAux`): both pieces of a
valid interior chord carry the orientation of the whole polygon.  This file
supplies the fact from which that follows, namely

  **`extreme_corner_orient`** — for a simple polygon `P` whose first vertex `u`
  is *strictly extreme* (all other vertices lie in an open half plane through
  `u`) and whose corner there is non-flat,

    `0 < shoelace2 P  ↔  0 < cross (u - pu) (nu - u)`,

  where `pu`, `nu` are the two neighbours of `u`.

The proof is elementary and uses only material already available:

* the *escape* theorem `HexArea.ptWind_zero_of_extreme_corner`
  (`RequestProject.SAWUmlaufCornerEscape`) shows that the point
  `w_out = u + t·(nu - u) - δ·(pu - u)`, which sits just outside the corner cone
  next to the edge `u–nu`, is not wound around by `P`;
* the *jump* theorem `HexArea.ptWind_jump_edge`
  (`RequestProject.SAWUmlaufWindJump`) shows that the mirror point
  `w_in = u + t·(nu - u) + δ·(pu - u)`, on the other side of that edge, has
  winding `±2π`, with the sign read off from `cross (pu - u) (nu - u)`;
* the point-in-polygon dichotomy (available for `P` through `DichBelow`) then
  identifies that sign with the sign of `shoelace2 P`.

Everything is stated relative to `DichBelow N`, so the file stays *below* the
induction of `RequestProject.SAWUmlaufJordanInduction` and introduces no cycle.

NOT a dead branch: it is imported by `RequestProject.SAWUmlaufChordLiftAux`.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 2000000

namespace HexArea

/-! ## 1. Indexing the closed edges -/

/-- The closed edges of `V` are exactly the pairs `(V[i], V[(i+1) % |V|])`. -/
lemma mem_closedEdges_iff_getElem (V : List ℂ) (e : ℂ × ℂ) :
    e ∈ closedEdges V ↔
      ∃ i, ∃ _ : i < V.length, e = (V[i], V[(i + 1) % V.length]'(by
        exact Nat.mod_lt _ (by omega))) := by
  rw [closedEdges, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.length_zip, List.length_rotate, min_self] at hi
    exact ⟨i, hi, by rw [List.getElem_zip, List.getElem_rotate]⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < (V.zip (V.rotate 1)).length := by
      rw [List.length_zip, List.length_rotate, min_self]; exact hi
    exact ⟨i, hi', by rw [List.getElem_zip, List.getElem_rotate]⟩

/-- Both endpoints of a closed edge are vertices. -/
lemma closedEdges_mem (V : List ℂ) (e : ℂ × ℂ) (he : e ∈ closedEdges V) :
    e.1 ∈ V ∧ e.2 ∈ V := by
  obtain ⟨i, hi, rfl⟩ := (mem_closedEdges_iff_getElem V e).mp he
  exact ⟨List.getElem_mem _, List.getElem_mem _⟩

/-- Every vertex is the source of a closed edge. -/
lemma exists_closedEdge_fst (V : List ℂ) (v : ℂ) (hv : v ∈ V) :
    ∃ e ∈ closedEdges V, e.1 = v := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  refine ⟨(V[i], V[(i + 1) % V.length]'(Nat.mod_lt _ (by omega))), ?_, rfl⟩
  exact (mem_closedEdges_iff_getElem V _).mpr ⟨i, hi, rfl⟩

/-- **The closed edges incident to the first vertex.**  In a `Nodup` cycle, the
only edges having `V[0]` as an endpoint are `(V[0], V[1])` and
`(V[|V|-1], V[0])`. -/
lemma closedEdges_incident_head (V : List ℂ) (h2 : 2 ≤ V.length) (hnd : V.Nodup)
    (e : ℂ × ℂ) (he : e ∈ closedEdges V) :
    (e.1 ≠ V[0]'(by omega) ∧ e.2 ≠ V[0]'(by omega)) ∨
      e = (V[0]'(by omega), V[1]'(by omega)) ∨
      e = (V[V.length - 1]'(by omega), V[0]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := (mem_closedEdges_iff_getElem V e).mp he
  by_cases h1 : i = 0
  · subst h1
    right; left
    simp [Nat.mod_eq_of_lt (show 1 < V.length by omega)]
  by_cases h2' : i = V.length - 1
  · subst h2'
    right; right
    have hmod : (V.length - 1 + 1) % V.length = 0 := by
      have hh : V.length - 1 + 1 = V.length := by omega
      rw [hh, Nat.mod_self]
    simp [hmod]
  · left
    have hmod : (i + 1) % V.length = i + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, ?_⟩
    · intro hh; exact h1 (hnd.getElem_inj_iff.mp hh)
    · simp only [hmod]
      intro hh
      have := hnd.getElem_inj_iff.mp hh
      omega

/-- The closed edges of `u :: nu :: rest`, split off the first one. -/
lemma closedEdges_cons_cons (u nu : ℂ) (rest : List ℂ) :
    closedEdges (u :: nu :: rest) = (u, nu) :: (nu :: rest).zip (rest ++ [u]) := by
  have hr1 : (u :: nu :: rest).rotate 1 = (nu :: rest) ++ [u] := by
    rw [List.rotate_cons_succ]; simp
  rw [closedEdges, hr1]; simp

/-- Appending an extra element on the left list does not change a `zip` whose
right list is already short enough. -/
lemma zip_append_singleton_left {α β : Type*} (L : List α) (x : α) (M : List β)
    (hM : M.length ≤ L.length) : (L ++ [x]).zip M = L.zip M := by
  induction L generalizing M with
  | nil =>
      have : M = [] := List.eq_nil_of_length_eq_zero (by simpa using hM)
      simp [this]
  | cons a L ih =>
      cases M with
      | nil => simp
      | cons b M => simp [List.zip_cons_cons, ih M (by simpa using hM)]

/-! ## 2. Elementary bilinear algebra -/

lemma cross_comb_right (a b : ℝ) (p q z : ℂ) :
    cross z (a • p + b • q) = a * cross z p + b * cross z q := by
  simp [cross, Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

lemma cross_comb_left (a b : ℝ) (p q z : ℂ) :
    cross (a • p + b • q) z = a * cross p z + b * cross q z := by
  simp [cross, Complex.real_smul, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
  ring

lemma cdot_comb (a b : ℝ) (p q d : ℂ) :
    cdot d (a • p + b • q) = a * cdot d p + b * cdot d q := by
  rw [cdot_add, cdot_smul, cdot_smul]

/-- A convex combination, recentred at `u`. -/
lemma affine_sub (a b : ℝ) (hab : a + b = 1) (x y u : ℂ) :
    a • x + b • y - u = a • (x - u) + b • (y - u) := by
  have hsum : a • u + b • u = u := by rw [← add_smul, hab, one_smul]
  have h2 : a • (x - u) + b • (y - u) = a • x + b • y - (a • u + b • u) := by
    rw [smul_sub, smul_sub]; abel
  rw [h2, hsum]

/-! ## 3. The orientation at a strictly extreme corner -/

/-- **The orientation of a simple polygon is read off at any strictly extreme
vertex.**  If the first vertex `u` of the simple polygon `P` is strictly extreme
(all other vertices lie in the open half plane `cdot d (· - u) > 0`) and the
corner there is non-flat, then `P` is positively oriented exactly when the corner
turn `pu → u → nu` is positive. -/
theorem extreme_corner_orient (N : ℕ) (hN : DichBelow N)
    (u nu pu d : ℂ) (rest : List ℂ)
    (hPN : (u :: nu :: rest).length < N) (h3 : 3 ≤ (u :: nu :: rest).length)
    (hsimple : PolygonSimple (u :: nu :: rest))
    (hpu : (u :: nu :: rest).getLast? = some pu)
    (hpos : ∀ y ∈ (u :: nu :: rest), y ≠ u → 0 < cdot d (y - u))
    (hX : cross (pu - u) (nu - u) ≠ 0) :
    (0 < shoelace2 (u :: nu :: rest) ↔ 0 < cross (u - pu) (nu - u)) := by
  classical
  set P : List ℂ := u :: nu :: rest with hPdef
  have hnd : P.Nodup := hsimple.1
  have hlenP : P.length = rest.length + 2 := by simp [hPdef]
  have hrest : 1 ≤ rest.length := by simp [hlenP] at h3 ⊢; omega
  have hP0 : P[0]'(by omega) = u := by simp [hPdef]
  have hP1 : P[1]'(by omega) = nu := by simp [hPdef]
  have hPlast : P[P.length - 1]'(by omega) = pu := by
    have := List.getLast?_eq_getElem? (l := P)
    rw [hpu] at this
    have h' : P[P.length - 1]? = some pu := this.symm
    exact (List.getElem?_eq_some_iff.mp h').2 ▸ rfl
  -- basic memberships and non-degeneracies
  have hnuP : nu ∈ P := by simp [hPdef]
  have hpuP : pu ∈ P := hPlast ▸ List.getElem_mem _
  have hnuu : nu ≠ u := by
    intro hh
    have h01 : P[1]'(by omega) = P[0]'(by omega) := by rw [hP0, hP1, hh]
    exact absurd (hnd.getElem_inj_iff.mp h01) (by omega)
  have hpuu : pu ≠ u := by
    intro hh
    have h01 : P[P.length - 1]'(by omega) = P[0]'(by omega) := by rw [hP0, hPlast, hh]
    have := hnd.getElem_inj_iff.mp h01
    omega
  set p : ℂ := pu - u with hpdef
  set n : ℂ := nu - u with hndef
  set X : ℝ := cross p n with hXdef
  have hXne : X ≠ 0 := hX
  have hn0 : n ≠ 0 := sub_ne_zero.mpr hnuu
  have hp0 : p ≠ 0 := sub_ne_zero.mpr hpuu
  have hDn : 0 < cdot d n := hpos nu hnuP hnuu
  have hDp : 0 < cdot d p := hpos pu hpuP hpuu
  obtain ⟨h, hh, hmin⟩ := exists_pos_lower_bound P u d hpos
  -- points of an edge missing `u` are far from `u`
  have hedgelow : ∀ e ∈ closedEdges P, e.1 ≠ u → e.2 ≠ u →
      ∀ w ∈ segment ℝ e.1 e.2, h ≤ cdot d (w - u) := by
    intro e he h1 h2 w hw
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    obtain ⟨hm1, hm2⟩ := closedEdges_mem P e he
    have e1 := hmin e.1 hm1 h1
    have e2 := hmin e.2 hm2 h2
    rw [affine_sub a b hab, cdot_comb]
    nlinarith
  have hUX : cross (u - pu) n = -X := by
    rw [hXdef, hpdef, hndef]; simp [cross]; ring
  have hnp : cross n p = -X := by rw [hXdef]; simp [cross]; ring
  -- the base point `m` on the edge `u–nu`, close to `u`
  set t : ℝ := min (1/2) (h / (2 * cdot d n)) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have htDn : t * cdot d n ≤ h / 2 := by
    have hle : t ≤ h / (2 * cdot d n) := min_le_right _ _
    have hstep : t * cdot d n ≤ (h / (2 * cdot d n)) * cdot d n := by nlinarith
    have hq : (h / (2 * cdot d n)) * cdot d n = h / 2 := by field_simp
    linarith [hq ▸ hstep]
  set m : ℂ := u + t • n with hmdef
  have hmu : m - u = t • n := by rw [hmdef]; abel
  -- `m` lies on no closed edge except `u–nu`
  have hmoff : ∀ e ∈ closedEdges P, e.1 ≠ u → m ∉ segment ℝ e.1 e.2 := by
    intro e he h1 hmem
    rcases closedEdges_incident_head P (by omega) hnd e he with ⟨hh1, hh2⟩ | heq | heq
    · rw [hP0] at hh1 hh2
      have hb := hedgelow e he hh1 hh2 m hmem
      rw [hmu, cdot_smul] at hb
      linarith
    · rw [heq] at h1; simp only [hP0] at h1; exact h1 rfl
    · rw [heq] at hmem
      simp only [hPlast, hP0] at hmem
      obtain ⟨a, b, ha, hb, hab, heq2⟩ := hmem
      have hmu2 : m - u = a • p := by
        rw [← heq2, affine_sub a b hab pu u u]; simp [hpdef]
      have hz1 : cross (m - u) n = 0 := by
        rw [hmu, cross_smul_left, cross_eq_zero_self, mul_zero]
      have hz2 : cross (m - u) n = a * X := by rw [hmu2, cross_smul_left, hXdef]
      have ha0 : a = 0 := by
        have haX : a * X = 0 := by rw [← hz2, hz1]
        rcases mul_eq_zero.mp haX with h' | h'
        · exact h'
        · exact absurd h' hXne
      have hz : m - u = 0 := by rw [hmu2, ha0, zero_smul]
      rw [hmu] at hz
      rcases smul_eq_zero.mp hz with h' | h'
      · linarith
      · exact hn0 h'
  -- the tail edge list
  set T : List (ℂ × ℂ) := (nu :: rest).zip (rest ++ [u]) with hTdef
  have hCE : closedEdges P = (u, nu) :: T := closedEdges_cons_cons u nu rest
  have hunotin : u ∉ nu :: rest := by
    have hnd' := hnd
    rw [hPdef, List.nodup_cons] at hnd'
    exact hnd'.1
  have hT1 : ∀ e ∈ T, e.1 ≠ u := by
    intro e he hcon
    have h1 := (List.of_mem_zip he).1
    rw [hcon] at h1
    exact hunotin h1
  have hTsub : ∀ e ∈ T, e ∈ closedEdges P := by
    intro e he; rw [hCE]; exact List.mem_cons_of_mem _ he
  have hpathT : ∀ e ∈ T, m ∉ segment ℝ e.1 e.2 :=
    fun e he => hmoff e (hTsub e he) (hT1 e he)
  have hjlist : (nu :: (rest ++ [u])).zip ((nu :: (rest ++ [u])).drop 1) = T := by
    rw [List.drop_one, List.tail_cons]
    have hcons : nu :: (rest ++ [u]) = (nu :: rest) ++ [u] := by simp
    rw [hcons, zip_append_singleton_left (nu :: rest) u (rest ++ [u]) (by simp)]
  have hpath : ∀ pr ∈ (nu :: (rest ++ [u])).zip ((nu :: (rest ++ [u])).drop 1),
      m ∉ segment ℝ pr.1 pr.2 := by rw [hjlist]; exact hpathT
  have hmopen : m ∈ openSegment ℝ u nu := by
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [hmdef, hndef]; module
  obtain ⟨δ₀, hδ₀, hjump⟩ := ptWind_jump_edge u nu rest m (Ne.symm hnuu) hmopen hpath
  obtain ⟨ε, hε, hclear⟩ := exists_clearance T m hpathT
  -- the two mirror points
  have hpnorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hmin0 : 0 < min δ₀ ε := lt_min hδ₀ hε
  set δ : ℝ := min ((min δ₀ ε) / (2 * ‖p‖)) (h / (4 * cdot d p)) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδnorm : δ * ‖p‖ < min δ₀ ε := by
    have h1 : δ ≤ (min δ₀ ε) / (2 * ‖p‖) := min_le_left _ _
    have h2 : δ * ‖p‖ ≤ ((min δ₀ ε) / (2 * ‖p‖)) * ‖p‖ := by nlinarith
    have hq2 : ((min δ₀ ε) / (2 * ‖p‖)) * ‖p‖ = (min δ₀ ε) / 2 := by field_simp
    rw [hq2] at h2; linarith
  have hδD : δ * cdot d p ≤ h / 4 := by
    have h1 : δ ≤ h / (4 * cdot d p) := min_le_right _ _
    have h2 : δ * cdot d p ≤ (h / (4 * cdot d p)) * cdot d p := by nlinarith
    have hq : (h / (4 * cdot d p)) * cdot d p = h / 4 := by field_simp
    rw [hq] at h2; exact h2
  set win : ℂ := u + t • n + δ • p with hwindef
  set wout : ℂ := u + t • n - δ • p with hwoutdef
  have hwinu : win - u = t • n + δ • p := by rw [hwindef]; abel
  have hwoutu : wout - u = t • n + (-δ) • p := by rw [hwoutdef, neg_smul]; abel
  have hwinm : win - m = δ • p := by rw [hwindef, hmdef]; abel
  have hwoutm : wout - m = (-δ) • p := by rw [hwoutdef, hmdef, neg_smul]; abel
  have hdin : dist win m < min δ₀ ε := by
    rw [dist_eq_norm, hwinm, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]; exact hδnorm
  have hdout : dist wout m < min δ₀ ε := by
    rw [dist_eq_norm, hwoutm, norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_iff_pos.mpr hδpos),
      neg_neg]
    exact hδnorm
  have hcin : cross n (win - u) = -δ * X := by
    rw [hwinu, cross_comb_right, cross_eq_zero_self, hnp]; ring
  have hcout : cross n (wout - u) = δ * X := by
    rw [hwoutu, cross_comb_right, cross_eq_zero_self, hnp]; ring
  have hcin' : cross (win - u) n = δ * X := by
    rw [hwinu, cross_comb_left, cross_eq_zero_self, ← hXdef]; ring
  have hcout' : cross (wout - u) n = -δ * X := by
    rw [hwoutu, cross_comb_left, cross_eq_zero_self, ← hXdef]; ring
  -- the `p`-coordinate of the mirror points (used for the escape segment)
  have hcpwout : cross p (wout - u) = t * X := by
    rw [hwoutu, cross_comb_right, cross_eq_zero_self, ← hXdef]; ring
  -- half-plane coordinates of the two mirror points
  have hcdwin : cdot d (win - u) = t * cdot d n + δ * cdot d p := by
    rw [hwinu, cdot_add, cdot_smul, cdot_smul]
  have hcdwout : cdot d (wout - u) = t * cdot d n + (-δ) * cdot d p := by
    rw [hwoutu, cdot_add, cdot_smul, cdot_smul]
  have hwinlt : cdot d (win - u) < h := by rw [hcdwin]; linarith
  have hwoutle : cdot d (wout - u) ≤ h / 2 := by
    have hdp : 0 < δ * cdot d p := mul_pos hδpos hDp
    rw [hcdwout]; linarith
  have hwoutlt : cdot d (wout - u) < h := by linarith
  -- neither mirror point is the corner itself
  have hwinne : win ≠ u := by
    intro hcon
    have h0 : (-δ) * X = 0 := by rw [← hcin, hcon]; simp [cross]
    rcases mul_eq_zero.mp h0 with h' | h'
    · linarith [neg_eq_zero.mp h']
    · exact hXne h'
  have hwoutne : wout ≠ u := by
    intro hcon
    have h0 : δ * X = 0 := by rw [← hcout, hcon]; simp [cross]
    rcases mul_eq_zero.mp h0 with h' | h'
    · linarith
    · exact hXne h'
  -- no vertex of `P` is one of the mirror points
  have hvertaway : ∀ w : ℂ, cdot d (w - u) < h → w ≠ u → ∀ v ∈ P, v ≠ w := by
    intro w hw hwu v hv hvw
    rcases eq_or_ne v u with rfl | hvu
    · exact hwu hvw.symm
    · have hb := hmin v hv hvu
      rw [hvw] at hb; linarith
  have hvwin : ∀ v ∈ P, v ≠ win := hvertaway win hwinlt hwinne
  have hvwout : ∀ v ∈ P, v ≠ wout := hvertaway wout hwoutlt hwoutne
  -- both mirror points lie off every closed edge of `P`
  have hoffedge : ∀ w : ℂ, dist w m < ε → cross n (w - u) ≠ 0 →
      ∀ e ∈ closedEdges P, w ∉ segment ℝ e.1 e.2 := by
    intro w hwd hwc e he hmem
    rw [hCE] at he
    rcases List.mem_cons.mp he with heq | he'
    · rw [heq] at hmem
      simp only at hmem
      obtain ⟨a, b, ha, hb, hab, heq2⟩ := hmem
      have hwu2 : w - u = b • n := by
        rw [← heq2, affine_sub a b hab u nu u, hndef]; simp
      apply hwc
      rw [hwu2]
      have : cross n (b • n) = b * cross n n := by
        simpa using cross_comb_right (0 : ℝ) b n n n
      rw [this, cross_eq_zero_self, mul_zero]
    · exact hclear w hwd e he' hmem
  have hδin : dist win m < δ₀ := lt_of_lt_of_le hdin (min_le_left _ _)
  have hδout : dist wout m < δ₀ := lt_of_lt_of_le hdout (min_le_left _ _)
  have hεin : dist win m < ε := lt_of_lt_of_le hdin (min_le_right _ _)
  have hεout : dist wout m < ε := lt_of_lt_of_le hdout (min_le_right _ _)
  have hcinne : cross n (win - u) ≠ 0 := by
    rw [hcin]
    intro hc
    rcases mul_eq_zero.mp hc with h' | h'
    · linarith [neg_eq_zero.mp h']
    · exact hXne h'
  have hcoutne : cross n (wout - u) ≠ 0 := by
    rw [hcout]
    intro hc
    rcases mul_eq_zero.mp hc with h' | h'
    · linarith
    · exact hXne h'
  have hwinoff : ∀ e ∈ closedEdges P, win ∉ segment ℝ e.1 e.2 :=
    hoffedge win hεin hcinne
  have hwoutoff : ∀ e ∈ closedEdges P, wout ∉ segment ℝ e.1 e.2 :=
    hoffedge wout hεout hcoutne
  -- **the escape**: the polygon does not wind around the outer mirror point
  have hescape : ptWind wout P = 0 := by
    refine ptWind_zero_of_extreme_corner P u pu nu wout d hwoutne hpuP hnuP hpuu hnuu hpos
      ?_ ?_ ?_
    · -- every cycle edge either avoids `u` or lies in the corner cone
      intro e he
      rw [cycleEdges_eq_closedEdges] at he
      rcases closedEdges_incident_head P (by omega) hnd e he with hav | heq | heq
      · rw [hP0] at hav; exact Or.inl hav
      · right
        rw [heq]
        simp only [hP0, hP1]
        exact segment_subset_cornerCone u pu nu u nu (mem_cornerCone_self u pu nu)
          (mem_cornerCone_right u pu nu)
      · right
        rw [heq]
        simp only [hP0, hPlast]
        exact segment_subset_cornerCone u pu nu pu u (mem_cornerCone_left u pu nu)
          (mem_cornerCone_self u pu nu)
    · -- the outer mirror point is outside the corner cone
      rintro ⟨α, β, hα, hβ, hαβ⟩
      have hcr : cross n (wout - u) = α * cross n p + β * cross n n := by
        rw [hαβ, cross_comb_right]
      rw [hcout, hnp, cross_eq_zero_self] at hcr
      have hz : (α + δ) * X = 0 := by nlinarith [hcr]
      rcases mul_eq_zero.mp hz with h' | h'
      · linarith
      · exact hXne h'
    · -- the segment from `u` to the outer mirror point touches `P` only at `u`
      intro e he w hw hwe
      obtain ⟨s1, s2, hs1, hs2, hs12, hweq⟩ := hw
      have hwu2 : w - u = s2 • (wout - u) := by
        rw [← hweq, affine_sub s1 s2 hs12 u wout u]; simp
      have hcd : cdot d (w - u) = s2 * cdot d (wout - u) := by
        rw [hwu2, cdot_smul]
      have hcdlt : cdot d (w - u) < h := by
        rw [hcd]
        nlinarith
      rw [cycleEdges_eq_closedEdges] at he
      rcases closedEdges_incident_head P (by omega) hnd e he with hav | heq | heq
      · exfalso
        rw [hP0] at hav
        have := hedgelow e he hav.1 hav.2 w hwe
        linarith
      · -- `w` on the edge `u–nu`
        rw [heq] at hwe
        simp only [hP0, hP1] at hwe
        obtain ⟨a, b, ha, hb, hab, heq2⟩ := hwe
        have hwu3 : w - u = b • n := by
          rw [← heq2, affine_sub a b hab u nu u, hndef]; simp
        have h1 : cross n (w - u) = 0 := by
          rw [hwu3]
          have : cross n (b • n) = b * cross n n := by
            simpa using cross_comb_right (0 : ℝ) b n n n
          rw [this, cross_eq_zero_self, mul_zero]
        have h2 : cross n (w - u) = s2 * (δ * X) := by
          rw [hwu2]
          have : cross n (s2 • (wout - u)) = s2 * cross n (wout - u) := by
            simpa using cross_comb_right (0 : ℝ) s2 (wout - u) (wout - u) n
          rw [this, hcout]
        have hs20 : s2 = 0 := by
          rw [h1] at h2
          rcases mul_eq_zero.mp h2.symm with h' | h'
          · exact h'
          · exfalso
            rcases mul_eq_zero.mp h' with h'' | h''
            · linarith
            · exact hXne h''
        have : w = u := by
          have : w - u = 0 := by rw [hwu2, hs20, zero_smul]
          linear_combination (norm := ring_nf) this
        exact this
      · -- `w` on the edge `pu–u`
        rw [heq] at hwe
        simp only [hP0, hPlast] at hwe
        obtain ⟨a, b, ha, hb, hab, heq2⟩ := hwe
        have hwu3 : w - u = a • p := by
          rw [← heq2, affine_sub a b hab pu u u, hpdef]; simp
        have h1 : cross p (w - u) = 0 := by
          rw [hwu3]
          have : cross p (a • p) = a * cross p p := by
            simpa using cross_comb_right (0 : ℝ) a p p p
          rw [this, cross_eq_zero_self, mul_zero]
        have h2 : cross p (w - u) = s2 * (t * X) := by
          rw [hwu2]
          have : cross p (s2 • (wout - u)) = s2 * cross p (wout - u) := by
            simpa using cross_comb_right (0 : ℝ) s2 (wout - u) (wout - u) p
          rw [this, hcpwout]
        have hs20 : s2 = 0 := by
          rw [h1] at h2
          rcases mul_eq_zero.mp h2.symm with h' | h'
          · exact h'
          · exfalso
            rcases mul_eq_zero.mp h' with h'' | h''
            · linarith
            · exact hXne h''
        have : w - u = 0 := by rw [hwu2, hs20, zero_smul]
        linear_combination (norm := ring_nf) this
  -- **the dichotomy** at the inner mirror point
  have hdich : PolyDichotomy P := hN P hPN h3 hsimple
  have hdichwin := hdich win (by
    intro e he
    rw [cycleEdges_eq_closedEdges] at he
    exact hwinoff e he)
  have hpi : 0 < Real.pi := Real.pi_pos
  rcases lt_or_gt_of_ne hXne with hXneg | hXpos
  · -- `X < 0`: the inner mirror point is wound around positively
    have hj := hjump win wout hδin hδout hvwin hvwout
      (by rw [hcin]; exact mul_pos_of_neg_of_neg (by linarith) hXneg)
      (by rw [hcout]; exact mul_neg_of_pos_of_neg hδpos hXneg)
    rw [hescape, sub_zero] at hj
    have hpos' : (0:ℝ) < shoelace2 P := by
      rcases hdichwin with h0 | h0
      · exfalso; rw [h0] at hj; linarith
      · rw [hj] at h0
        by_contra hcon
        rw [if_neg hcon] at h0
        linarith
    rw [hUX]
    constructor
    · intro _; linarith
    · intro _; exact hpos'
  · -- `X > 0`: the inner mirror point is wound around negatively
    have hj := hjump wout win hδout hδin hvwout hvwin
      (by rw [hcout]; exact mul_pos hδpos hXpos)
      (by rw [hcin]; exact mul_neg_of_neg_of_pos (by linarith) hXpos)
    rw [hescape, zero_sub] at hj
    have hwin2 : ptWind win P = -(2 * Real.pi) := by linarith
    have hneg : ¬ ((0:ℝ) < shoelace2 P) := by
      intro hcon
      rcases hdichwin with h0 | h0
      · rw [h0] at hwin2; linarith
      · rw [if_pos hcon] at h0; rw [h0] at hwin2; linarith
    rw [hUX]
    constructor
    · intro hcon; exact absurd hcon hneg
    · intro hcon; linarith

end HexArea

end
