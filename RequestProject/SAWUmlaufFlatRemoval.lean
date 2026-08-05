/-
# Flat-vertex removal for closed polygons

`RequestProject.SAWUmlaufFlatClipCounterexample` shows that an ear clip of a
simple polygon can leave a **flat** vertex behind: the pentagon
`0, i, 1+i, 2+2i, 2+i` is simple and cyclically non-degenerate, but clipping any
of its ears produces a quadrilateral with three collinear consecutive vertices.
Consequently the ear-clipping induction of the polygon Umlaufsatz cannot demand
`polyCycNondeg` of the clip; it must instead be able to **delete flat
vertices**.

This file provides that step.  A vertex `b` with cyclic neighbours `a`, `c` is
*flat* when it lies strictly between them, `b = a + s (c - a)` with `0 < s < 1`.
Deleting it

* preserves the total turning `polyCycWind` exactly
  (`flat_turning_identity`, `polyCycWind_remove_flat_second`) — the two turns at
  `a` and `c` merge and the turn at `b` is `0`;
* preserves the signed area `HexArea.shoelace2` exactly
  (`shoelace2_remove_flat_second`) — the removed triangle is degenerate;
* preserves planar simplicity (`PolygonSimple_remove_flat_second`, an instance of
  the already proved `PolygonSimple_remove_flat_mid`);
* cannot create a new flat corner: the corners at `a` and at `c` are only
  rescaled by a positive factor (`cross_pred_corner_remove_flat`,
  `cross_succ_corner_remove_flat` in `RequestProject.SAWUmlaufPolyChord`).

Moreover, in a *simple* polygon a degenerate cyclic corner is automatically of
this flat kind — the "spike" alternative `b - a = t (c - b)` with `t < 0` forces
two non-adjacent edges to meet (`flat_between_of_cross_zero`).

The package is `exists_nondeg_normalization`: every simple closed polygon with
non-zero signed area can be normalised to a simple, cyclically non-degenerate
polygon with the *same* turning and the *same* signed area, by repeatedly
deleting flat vertices.

This file is imported by `RequestProject.SAWUmlaufPolyLift` (hence lies on the
live route to the main theorem); it is the replacement, forced by the
counterexample, for the "clip corners stay non-flat" clauses of
`EmptyCornerData`.
-/
import Mathlib
import RequestProject.SAWUmlaufChordCorner

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The local turning identity of a flat vertex -/

/-- **The ear-clip local turning identity holds exactly at a flat vertex.**
If `b = a + s (c - a)` with `0 < s < 1` then the three turns at `a`, `b`, `c`
telescope to the two turns of the clipped cycle: the turn at `b` is `0`, and the
turns at `a` and `c` are unchanged because `b - a` and `c - b` are *positive*
real multiples of `c - a`. -/
lemma flat_turning_identity (a b c p q : ℂ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hb : b - a = (s : ℂ) * (c - a)) (hca : c - a ≠ 0) :
    Complex.arg ((b - a) / (a - p)) + Complex.arg ((c - b) / (b - a))
        + Complex.arg ((q - c) / (c - b))
      = Complex.arg ((c - a) / (a - p)) + Complex.arg ((q - c) / (c - a)) := by
  have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hs1' : ((1 - s : ℝ) : ℂ) ≠ 0 := by
    have : (1 - s) ≠ 0 := by linarith
    exact_mod_cast this
  have hcb : c - b = ((1 - s : ℝ) : ℂ) * (c - a) := by
    have h : c - b = (c - a) - (b - a) := by ring
    rw [h, hb]; push_cast; ring
  have e1 : (b - a) / (a - p) = (s : ℂ) * ((c - a) / (a - p)) := by
    rw [hb]; ring
  have e2 : (c - b) / (b - a) = (((1 - s) / s : ℝ) : ℂ) := by
    rw [hcb, hb]; push_cast
    field_simp
  have e3 : (q - c) / (c - b) = ((1 / (1 - s) : ℝ) : ℂ) * ((q - c) / (c - a)) := by
    rw [hcb]; push_cast
    field_simp
  have h1s : (0:ℝ) < 1 - s := by linarith
  rw [e1, e2, e3, Complex.arg_real_mul _ hs0,
    Complex.arg_real_mul _ (by positivity : (0:ℝ) < 1 / (1 - s)),
    Complex.arg_ofReal_of_nonneg (by positivity : (0:ℝ) ≤ (1 - s) / s)]
  ring

/-! ## Removing a flat second vertex -/

/-- **Turning is preserved when a flat second vertex is deleted.** -/
lemma polyCycWind_remove_flat_second (a b c p q : ℂ) (rest : List ℂ)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hpa : a - p ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0)
    (hcq : q - c ≠ 0) (hca : c - a ≠ 0)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hb : b - a = (s : ℂ) * (c - a)) :
    polyCycWind (a :: c :: rest) = polyCycWind (a :: b :: c :: rest) :=
  polyCycWind_clip_eq_of_identity a b c p q rest hp hq hpa hab hbc hcq hca
    (flat_turning_identity a b c p q s hs0 hs1 hb hca)

/-- **The signed area is preserved when a flat second vertex is deleted**: the
removed triangle `a, b, c` is degenerate. -/
lemma shoelace2_remove_flat_second (a b c : ℂ) (rest : List ℂ) (s : ℝ)
    (hb : b - a = (s : ℂ) * (c - a)) :
    HexArea.shoelace2 (a :: b :: c :: rest) = HexArea.shoelace2 (a :: c :: rest) := by
  rw [shoelace2_clip_second]
  have htri : HexArea.shoelace2 [a, b, c] = 0 := by
    have hb' : b = a + (s : ℂ) * (c - a) := by linear_combination hb
    subst hb'
    simp [HexArea.shoelace2_triple, HexArea.cross, Complex.ext_iff]
    ring
  rw [htri, add_zero]

/-- **Planar simplicity is preserved when a flat second vertex is deleted.**
Instance of `PolygonSimple_remove_flat_mid` with an empty prefix. -/
lemma PolygonSimple_remove_flat_second (a b c : ℂ) (rest : List ℂ)
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hflat : b ∈ segment ℝ a c) :
    PolygonSimple (a :: c :: rest) := by
  have h := PolygonSimple_remove_flat_mid [] rest a b c (by simpa using hsimple) hflat
  simpa using h

/-- A point of the form `a + s (c - a)` with `0 ≤ s ≤ 1` lies on the segment. -/
lemma mem_segment_of_param (a c : ℂ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (b : ℂ) (hb : b - a = (s : ℂ) * (c - a)) :
    b ∈ segment ℝ a c := by
  refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
  have hb' : b = a + (s : ℂ) * (c - a) := by linear_combination hb
  rw [hb']
  simp [Complex.real_smul]
  ring

/-! ## A degenerate corner of a *simple* polygon is flat, never a spike -/

/-- Two complex numbers with vanishing cross product are real multiples of each
other (the first being non-zero). -/
lemma exists_real_of_cross_zero (z w : ℂ) (hz : z ≠ 0) (h : HexArea.cross z w = 0) :
    ∃ t : ℝ, w = (t : ℂ) * z := by
  refine ⟨(w / z).re, ?_⟩
  have hns : Complex.normSq z ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hz
  have him : (w / z).im = 0 := by
    rw [Complex.div_im]
    field_simp
    simp [HexArea.cross] at h
    linarith
  have hre : (w / z) = (((w / z).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  calc w = (w / z) * z := by field_simp
  _ = (((w / z).re : ℝ) : ℂ) * z := by rw [← hre]

/-- **In a simple polygon a flat cyclic corner really is flat.**  If the corner
`a, b, c` at the second vertex of a simple closed polygon `a :: b :: c :: rest`
(with `rest ≠ []`) is degenerate, then `b` lies *strictly between* `a` and `c`:
`b - a = s (c - a)` with `0 < s < 1`.  The two "spike" alternatives would put a
vertex in the interior of a non-incident edge:

* if `c` were between `a` and `b`, the edge `a–b` would meet the edge `c–q`;
* if `a` were between `b` and `c`, the edge `b–c` would meet the edge `p–a`. -/
lemma flat_between_of_cross_zero (a b c : ℂ) (rest : List ℂ) (hrest : rest ≠ [])
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hzero : HexArea.cross (b - a) (c - b) = 0) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ b - a = (s : ℂ) * (c - a) := by
  set W : List ℂ := a :: b :: c :: rest with hWdef
  have hnd : W.Nodup := hsimple.1
  have hrl : 1 ≤ rest.length := List.length_pos_iff.mpr hrest
  have hlen : W.length = 3 + rest.length := by simp [hWdef]; omega
  have hlen4 : 4 ≤ W.length := by omega
  -- The five relevant entries of `W`.
  have h0 : W[0]'(by omega) = a := by simp [hWdef]
  have h1 : W[1]'(by omega) = b := by simp [hWdef]
  have h2 : W[2]'(by omega) = c := by simp [hWdef]
  set q : ℂ := W[3]'(by omega) with hqdef
  set p : ℂ := W[W.length - 1]'(by omega) with hpdef
  -- Distinctness, from `Nodup`.
  have hinj := fun (i j : ℕ) (hi : i < W.length) (hj : j < W.length) =>
    (List.Nodup.getElem_inj_iff (l := W) hnd (i := i) (j := j) (hi := hi) (hj := hj))
  have hab : a ≠ b := by
    intro h; have := (hinj 0 1 (by omega) (by omega)).mp (by rw [h0, h1]; exact h); omega
  have hac : a ≠ c := by
    intro h; have := (hinj 0 2 (by omega) (by omega)).mp (by rw [h0, h2]; exact h); omega
  have hbc : b ≠ c := by
    intro h; have := (hinj 1 2 (by omega) (by omega)).mp (by rw [h1, h2]; exact h); omega
  have haq : a ≠ q := by
    intro h; have := (hinj 0 3 (by omega) (by omega)).mp (by rw [h0]; exact h); omega
  have hbq : b ≠ q := by
    intro h; have := (hinj 1 3 (by omega) (by omega)).mp (by rw [h1]; exact h); omega
  have hbp : b ≠ p := by
    intro h; have := (hinj 1 (W.length - 1) (by omega) (by omega)).mp (by rw [h1]; exact h)
    omega
  have hcp : c ≠ p := by
    intro h; have := (hinj 2 (W.length - 1) (by omega) (by omega)).mp (by rw [h2]; exact h)
    omega
  -- The four relevant closed edges.
  have eab : (a, b) ∈ closedEdges W :=
    mem_closedEdges_pair W 0 1 (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]) a b h0 h1
  have ebc : (b, c) ∈ closedEdges W :=
    mem_closedEdges_pair W 1 2 (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]) b c h1 h2
  have ecq : (c, q) ∈ closedEdges W :=
    mem_closedEdges_pair W 2 3 (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]) c q h2 rfl
  have epa : (p, a) ∈ closedEdges W :=
    mem_closedEdges_pair W (W.length - 1) 0 (by omega) (by omega)
      (by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]) p a rfl h0
  -- The corner is degenerate, so `c - b` is a real multiple of `b - a`.
  have hba : b - a ≠ 0 := sub_ne_zero_of_ne (Ne.symm hab)
  obtain ⟨t, ht⟩ := exists_real_of_cross_zero (b - a) (c - b) hba hzero
  have hcb : c - b ≠ 0 := sub_ne_zero_of_ne (Ne.symm hbc)
  have ht0 : t ≠ 0 := by
    intro h; rw [h] at ht; simp at ht; exact hcb ht
  have hca : c - a = ((1 + t : ℝ) : ℂ) * (b - a) := by
    have h : c - a = (b - a) + (c - b) := by ring
    rw [h, ht]; push_cast; ring
  rcases lt_trichotomy t 0 with htneg | htzero | htpos
  · exfalso
    rcases lt_trichotomy (1 + t) 0 with h1t | h1t | h1t
    · -- `a` lies strictly between `b` and `c`: edge `b–c` meets edge `p–a`.
      have hmt : (0:ℝ) < -t := by linarith
      have hnz : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
      have hkey : ((1 / (-t) : ℝ) : ℂ) * ((t : ℂ) * (b - a)) = -(b - a) := by
        push_cast; field_simp
      have hab' : a - b = ((1 / (-t) : ℝ) : ℂ) * (c - b) := by
        rw [ht, hkey]; ring
      have hmem : a ∈ segment ℝ b c := by
        refine mem_segment_of_param b c (1 / (-t)) (by positivity) ?_ a hab'
        rw [div_le_one hmt]; linarith
      have hdis := hsimple.2 (b, c) ebc (p, a) epa hbp (Ne.symm hab) hcp (Ne.symm hac)
      exact (Set.disjoint_left.mp hdis) hmem (right_mem_segment ℝ p a)
    · -- `c = a`, impossible.
      have hz : c - a = 0 := by rw [hca, h1t]; simp
      exact hac (sub_eq_zero.mp hz).symm
    · -- `c` lies strictly between `a` and `b`: edge `a–b` meets edge `c–q`.
      have hcb' : c - a = ((1 + t : ℝ) : ℂ) * (b - a) := hca
      have hmem : c ∈ segment ℝ a b := by
        refine mem_segment_of_param a b (1 + t) (le_of_lt h1t) (by linarith) c hcb'
      have hdis := hsimple.2 (a, b) eab (c, q) ecq hac haq hbc hbq
      exact (Set.disjoint_left.mp hdis) hmem (left_mem_segment ℝ c q)
  · exact absurd htzero ht0
  · refine ⟨1 / (1 + t), by positivity, ?_, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · have hnz : ((1 + t : ℝ) : ℂ) ≠ 0 := by
        have h : (1 + t) ≠ 0 := by linarith
        exact_mod_cast h
      have hkey : ((1 / (1 + t) : ℝ) : ℂ) * (((1 + t : ℝ)) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, one_div,
          inv_mul_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < 1 + t))]
        norm_num
      rw [hca, ← mul_assoc, hkey, one_mul]


/-! ## The packaged one-step removal -/

/-- **One flat-vertex removal step.**  If the corner at the second vertex of the
simple closed polygon `a :: b :: c :: rest` (`rest ≠ []`) is degenerate, then
deleting `b` leaves a simple closed polygon with the *same* turning and the
*same* signed area. -/
lemma flat_removal_step (a b c : ℂ) (rest : List ℂ) (hrest : rest ≠ [])
    (hsimple : PolygonSimple (a :: b :: c :: rest))
    (hzero : HexArea.cross (b - a) (c - b) = 0) :
    PolygonSimple (a :: c :: rest) ∧
      polyCycWind (a :: c :: rest) = polyCycWind (a :: b :: c :: rest) ∧
      HexArea.shoelace2 (a :: c :: rest) = HexArea.shoelace2 (a :: b :: c :: rest) ∧
      b ∈ segment ℝ a c := by
  obtain ⟨s, hs0, hs1, hb⟩ := flat_between_of_cross_zero a b c rest hrest hsimple hzero
  -- Names for the two cyclic neighbours of the clip diagonal.
  obtain ⟨p, hp⟩ : ∃ p, rest.getLast? = some p := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons x t => exact ⟨(x :: t).getLast (by simp), by simp [List.getLast?_eq_getLast]⟩
  obtain ⟨q, hq⟩ : ∃ q, rest.head? = some q := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons x t => exact ⟨x, rfl⟩
  have hnd : (a :: b :: c :: rest).Nodup := hsimple.1
  have hpmem : p ∈ rest := List.mem_of_mem_getLast? hp
  have hqmem : q ∈ rest := List.mem_of_mem_head? hq
  simp only [List.nodup_cons, List.mem_cons] at hnd
  have hpa : a - p ≠ 0 := by
    refine sub_ne_zero_of_ne ?_
    intro h; exact hnd.1 (Or.inr (Or.inr (h ▸ hpmem)))
  have hab : b - a ≠ 0 := by
    refine sub_ne_zero_of_ne ?_
    intro h; exact hnd.1 (Or.inl h.symm)
  have hcq : q - c ≠ 0 := by
    refine sub_ne_zero_of_ne ?_
    intro h; exact hnd.2.2.1 (h ▸ hqmem)
  have hca : c - a ≠ 0 := by
    refine sub_ne_zero_of_ne ?_
    intro h; exact hnd.1 (Or.inr (Or.inl h.symm))
  have hbc : c - b ≠ 0 := by
    refine sub_ne_zero_of_ne ?_
    intro h; exact hnd.2.1 (Or.inl h.symm)
  have hflat : b ∈ segment ℝ a c :=
    mem_segment_of_param a c s (le_of_lt hs0) (le_of_lt hs1) b hb
  refine ⟨PolygonSimple_remove_flat_second a b c rest hsimple hflat, ?_, ?_, hflat⟩
  · exact polyCycWind_remove_flat_second a b c p q rest hp hq hpa hab hbc hcq hca s hs0 hs1 hb
  · exact (shoelace2_remove_flat_second a b c rest s hb).symm


/-! ## Finding a flat corner -/

/-- `polyNondeg` follows from the non-vanishing of all consecutive-triple cross
products. -/
lemma polyNondeg_of_getElem (L : List ℂ)
    (H : ∀ i : ℕ, i + 2 < L.length →
      HexArea.cross (L[i+1]! - L[i]!) (L[i+2]! - L[i+1]!) ≠ 0) :
    polyNondeg L := by
  induction L with
  | nil => trivial
  | cons x t ih =>
    match t with
    | [] => trivial
    | [y] => trivial
    | y :: z :: v =>
      rw [polyNondeg_cons_cons_cons]
      refine ⟨?_, ?_⟩
      · have h0 := H 0 (by simp)
        simpa using h0
      · refine ih (fun i h => ?_)
        have h1 := H (i + 1) (by simp at h ⊢; omega)
        simpa using h1

/-- Entries of the closed form `V ++ V.take 2` are the cyclic entries of `V`. -/
lemma getElem_append_take_two (V : List ℂ) (h2 : 2 ≤ V.length) (j : ℕ)
    (hj : j < V.length + 2) :
    (V ++ V.take 2)[j]! = V[j % V.length]! := by
  have hlen : (V ++ V.take 2).length = V.length + 2 := by simp; omega
  have hmodlt : j % V.length < V.length := Nat.mod_lt _ (by omega)
  rw [getElem!_pos (V ++ V.take 2) j (by omega), getElem!_pos V (j % V.length) hmodlt]
  by_cases hlt : j < V.length
  · rw [List.getElem_append_left hlt]
    congr 1
    exact (Nat.mod_eq_of_lt hlt).symm
  · push_neg at hlt
    rw [List.getElem_append_right hlt]
    have hmod : j % V.length = j - V.length := by
      rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getElem_take]
    congr 1
    exact hmod.symm

/-- Entries of a rotation are the cyclically shifted entries. -/
lemma getElem_rotate_bang (V : List ℂ) (i j : ℕ) (hj : j < V.length) :
    (V.rotate i)[j]! = V[(j + i) % V.length]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_rotate (by simpa using hj)]

/-- **A cyclically degenerate polygon has a flat corner at the front of some
rotation.** -/
lemma exists_flat_cyclic_corner (V : List ℂ) (h3 : 3 ≤ V.length) (h : ¬ polyCycNondeg V) :
    ∃ (r : ℕ) (a b c : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ HexArea.cross (b - a) (c - b) = 0 := by
  by_contra hcon
  push_neg at hcon
  apply h
  rw [polyCycNondeg_def]
  refine polyNondeg_of_getElem _ (fun i hi => ?_)
  have hlen : (V ++ V.take 2).length = V.length + 2 := by simp; omega
  rw [hlen] at hi
  have hi' : i < V.length := by omega
  -- the rotation of `V` starting at `i`
  obtain ⟨a, b, c, rest, hr⟩ : ∃ a b c rest, V.rotate i = a :: b :: c :: rest := by
    have hlen3 : 3 ≤ (V.rotate i).length := by simpa using h3
    rcases hh : V.rotate i with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [hh] at hlen3
    · simp [hh] at hlen3
    · simp [hh] at hlen3
    · exact ⟨a, b, c, rest, rfl⟩
  have ha : V[(0 + i) % V.length]! = a := by
    rw [← getElem_rotate_bang V i 0 (by omega), hr]; simp
  have hb : V[(1 + i) % V.length]! = b := by
    rw [← getElem_rotate_bang V i 1 (by omega), hr]; simp
  have hc : V[(2 + i) % V.length]! = c := by
    rw [← getElem_rotate_bang V i 2 (by omega), hr]; simp
  rw [getElem_append_take_two V (by omega) i (by omega),
    getElem_append_take_two V (by omega) (i + 1) (by omega),
    getElem_append_take_two V (by omega) (i + 2) (by omega),
    show i % V.length = (0 + i) % V.length by ring_nf,
    show (i + 1) % V.length = (1 + i) % V.length by ring_nf,
    show (i + 2) % V.length = (2 + i) % V.length by ring_nf,
    ha, hb, hc]
  exact hcon i a b c rest hr


/-! ## Normalisation: deleting all flat vertices -/

/-- The signed area of a triangle is the corner cross product. -/
lemma shoelace2_triple_eq_cross (a b c : ℂ) :
    HexArea.shoelace2 [a, b, c] = HexArea.cross (b - a) (c - b) := by
  simp [HexArea.shoelace2_triple, HexArea.cross]
  ring

/-- **Normalisation by flat-vertex deletion (strong-induction form).**  Every
simple closed polygon with at least three vertices and non-zero signed area can
be turned into a simple, *cyclically non-degenerate* closed polygon with the
same turning and the same signed area, by deleting flat vertices one at a
time. -/
lemma exists_nondeg_normalization_aux :
    ∀ (n : ℕ) (V : List ℂ), V.length = n → 3 ≤ V.length → PolygonSimple V →
      HexArea.shoelace2 V ≠ 0 →
      ∃ V' : List ℂ, 3 ≤ V'.length ∧ V'.length ≤ V.length ∧ PolygonSimple V' ∧
        polyCycNondeg V' ∧ polyCycWind V' = polyCycWind V ∧
        HexArea.shoelace2 V' = HexArea.shoelace2 V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V hn h3 hsimple harea
    by_cases hnd : polyCycNondeg V
    · exact ⟨V, h3, le_rfl, hsimple, hnd, rfl, rfl⟩
    -- Find a flat corner and rotate it to the front.
    obtain ⟨r, a, b, c, rest, hrot, hzero⟩ := exists_flat_cyclic_corner V h3 hnd
    have hWsimple : PolygonSimple (a :: b :: c :: rest) := by
      rw [← hrot]; exact (PolygonSimple_rotate V r).mpr hsimple
    have hWlen : (a :: b :: c :: rest).length = V.length := by
      rw [← hrot]; simp
    have hWarea : HexArea.shoelace2 (a :: b :: c :: rest) = HexArea.shoelace2 V := by
      rw [← hrot]; exact shoelace2_rotate V r
    have hWwind : polyCycWind (a :: b :: c :: rest) = polyCycWind V := by
      rw [← hrot]; exact polyCycWind_rotate V r h3
    -- `rest` cannot be empty: a degenerate triangle has zero area.
    have hrest : rest ≠ [] := by
      rintro rfl
      apply harea
      rw [← hWarea, shoelace2_triple_eq_cross, hzero]
    -- Delete the flat vertex.
    obtain ⟨hsimple₁, hwind₁, harea₁, -⟩ := flat_removal_step a b c rest hrest hWsimple hzero
    have hlen₁ : (a :: c :: rest).length = V.length - 1 := by
      simp at hWlen ⊢; omega
    have hrestlen : 1 ≤ rest.length := List.length_pos_iff.mpr hrest
    have h3₁ : 3 ≤ (a :: c :: rest).length := by simp; omega
    have hlt : (a :: c :: rest).length < n := by
      rw [← hn]; simp at hWlen ⊢; omega
    have harea₁' : HexArea.shoelace2 (a :: c :: rest) ≠ 0 := by
      rw [harea₁, hWarea]; exact harea
    obtain ⟨V', hV'3, hV'le, hV'simple, hV'nd, hV'wind, hV'area⟩ :=
      IH (a :: c :: rest).length hlt (a :: c :: rest) rfl h3₁ hsimple₁ harea₁'
    refine ⟨V', hV'3, ?_, hV'simple, hV'nd, ?_, ?_⟩
    · omega
    · rw [hV'wind, hwind₁, hWwind]
    · rw [hV'area, harea₁, hWarea]

/-- **Normalisation by flat-vertex deletion.**  See
`exists_nondeg_normalization_aux`. -/
lemma exists_nondeg_normalization (V : List ℂ) (h3 : 3 ≤ V.length)
    (hsimple : PolygonSimple V) (harea : HexArea.shoelace2 V ≠ 0) :
    ∃ V' : List ℂ, 3 ≤ V'.length ∧ V'.length ≤ V.length ∧ PolygonSimple V' ∧
      polyCycNondeg V' ∧ polyCycWind V' = polyCycWind V ∧
      HexArea.shoelace2 V' = HexArea.shoelace2 V :=
  exists_nondeg_normalization_aux V.length V rfl h3 hsimple harea


/-! ## A simple polygon with at least four vertices is not collinear -/

/-- Three collinear points, in order of their line parameters, put the middle
one strictly inside the segment spanned by the outer two. -/
lemma mem_segment_of_params (p₀ v : ℂ) (t₁ t₂ t₃ : ℝ) (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃) :
    (p₀ + (t₂ : ℂ) * v) ∈ segment ℝ (p₀ + (t₁ : ℂ) * v) (p₀ + (t₃ : ℂ) * v) := by
  refine mem_segment_of_param _ _ ((t₂ - t₁) / (t₃ - t₁)) ?_ ?_ _ ?_
  · apply div_nonneg <;> linarith
  · rw [div_le_one (by linarith)]; linarith
  · have hne : (t₃ - t₁ : ℝ) ≠ 0 := by intro h; linarith [h]
    have hkey : ((t₂ - t₁) / (t₃ - t₁) : ℝ) * (t₃ - t₁) = t₂ - t₁ := by field_simp
    have : (p₀ + (t₃ : ℂ) * v) - (p₀ + (t₁ : ℂ) * v) = ((t₃ - t₁ : ℝ) : ℂ) * v := by
      push_cast; ring
    rw [this, ← mul_assoc, ← Complex.ofReal_mul, hkey]
    push_cast; ring

/-- **A simple closed polygon with at least four vertices is not contained in a
line.**  At the extreme vertex `u` of the line the two incident edges both
descend, so the *larger* of the two neighbours lies strictly inside the edge
joining `u` to the smaller one; the second edge at that neighbour then meets a
non-incident edge, contradicting simplicity. -/
lemma not_collinear_of_simple (V : List ℂ) (h4 : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (p₀ v : ℂ) (hv : v ≠ 0)
    (hline : ∀ x ∈ V, ∃ t : ℝ, x = p₀ + (t : ℂ) * v) : False := by
  classical
  -- the line parameter as an explicit function
  set f : ℂ → ℝ := fun z => ((z - p₀) * (starRingEnd ℂ) v).re / Complex.normSq v with hfdef
  have hns : Complex.normSq v ≠ 0 := by simpa [Complex.normSq_eq_zero] using hv
  have hfparam : ∀ x ∈ V, x = p₀ + ((f x : ℝ) : ℂ) * v := by
    intro x hx
    obtain ⟨t, ht⟩ := hline x hx
    have hfx : f x = t := by
      rw [hfdef]
      simp only [ht]
      have h1 : (p₀ + (t : ℂ) * v - p₀) = (t : ℂ) * v := by ring
      rw [h1, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
      field_simp
    rw [hfx, ← ht]
  have hfinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y := by
    intro x hx y hy hxy
    rw [hfparam x hx, hfparam y hy, hxy]
  -- the extreme vertex
  have hVne : V ≠ [] := by intro h; rw [h] at h4; simp at h4
  have hne : (V.toFinset).Nonempty := by
    cases V with
    | nil => exact absurd rfl hVne
    | cons x t => exact ⟨x, by simp⟩
  obtain ⟨u, huF, hmax⟩ := Finset.exists_max_image V.toFinset f hne
  have huV : u ∈ V := List.mem_toFinset.mp huF
  have hmax' : ∀ y ∈ V, f y ≤ f u := fun y hy => hmax y (List.mem_toFinset.mpr hy)
  -- rotate `u` into the middle
  obtain ⟨r, n₁, n₂, rest, hrot⟩ := exists_rotate_mid V u huV (by omega)
  set W : List ℂ := n₁ :: u :: n₂ :: rest with hWdef
  have hWsimple : PolygonSimple W := by
    rw [← hrot]; exact (PolygonSimple_rotate V r).mpr hsimple
  have hWlen : W.length = V.length := by rw [← hrot]; simp
  have hWmem : ∀ x, x ∈ W ↔ x ∈ V := by
    intro x; rw [← hrot]; exact List.mem_rotate
  have hnd : W.Nodup := hWsimple.1
  have hlen4 : 4 ≤ W.length := by omega
  have hrestlen : rest.length = W.length - 3 := by
    simp only [hWdef, List.length_cons]; omega
  have h0 : W[0]'(by omega) = n₁ := by simp [hWdef]
  have h1 : W[1]'(by omega) = u := by simp [hWdef]
  have h2 : W[2]'(by omega) = n₂ := by simp [hWdef]
  set x₃ : ℂ := W[3]'(by omega) with hx₃
  set p : ℂ := W[W.length - 1]'(by omega) with hp
  have hinj := fun (i j : ℕ) (hi : i < W.length) (hj : j < W.length) =>
    (List.Nodup.getElem_inj_iff (l := W) hnd (i := i) (j := j) (hi := hi) (hj := hj))
  have hne01 : n₁ ≠ u := by
    intro h; have := (hinj 0 1 (by omega) (by omega)).mp (by rw [h0, h1]; exact h); omega
  have hne02 : n₁ ≠ n₂ := by
    intro h; have := (hinj 0 2 (by omega) (by omega)).mp (by rw [h0, h2]; exact h); omega
  have hne12 : u ≠ n₂ := by
    intro h; have := (hinj 1 2 (by omega) (by omega)).mp (by rw [h1, h2]; exact h); omega
  have hne03 : n₁ ≠ x₃ := by
    intro h; have := (hinj 0 3 (by omega) (by omega)).mp (by rw [h0]; exact h); omega
  have hne13 : u ≠ x₃ := by
    intro h; have := (hinj 1 3 (by omega) (by omega)).mp (by rw [h1]; exact h); omega
  have hne23 : n₂ ≠ x₃ := by
    intro h; have := (hinj 2 3 (by omega) (by omega)).mp (by rw [h2]; exact h); omega
  have hnep0 : n₁ ≠ p := by
    intro h; have := (hinj 0 (W.length - 1) (by omega) (by omega)).mp (by rw [h0]; exact h)
    omega
  have hnep1 : u ≠ p := by
    intro h; have := (hinj 1 (W.length - 1) (by omega) (by omega)).mp (by rw [h1]; exact h)
    omega
  have hnep2 : n₂ ≠ p := by
    intro h; have := (hinj 2 (W.length - 1) (by omega) (by omega)).mp (by rw [h2]; exact h)
    omega
  -- memberships in `V`
  have hmemW : ∀ (i : ℕ) (hi : i < W.length), W[i]'hi ∈ V := by
    intro i hi
    exact (hWmem _).mp (List.getElem_mem hi)
  have hn₁V : n₁ ∈ V := by rw [← h0]; exact hmemW 0 (by omega)
  have hn₂V : n₂ ∈ V := by rw [← h2]; exact hmemW 2 (by omega)
  have hx₃V : x₃ ∈ V := hmemW 3 (by omega)
  have hpV : p ∈ V := hmemW (W.length - 1) (by omega)
  -- the four relevant edges
  have e01 : (n₁, u) ∈ closedEdges W :=
    mem_closedEdges_pair W 0 1 (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]) n₁ u h0 h1
  have e12 : (u, n₂) ∈ closedEdges W :=
    mem_closedEdges_pair W 1 2 (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]) u n₂ h1 h2
  have e23 : (n₂, x₃) ∈ closedEdges W :=
    mem_closedEdges_pair W 2 3 (by omega) (by omega)
      (by rw [Nat.mod_eq_of_lt (by omega)]) n₂ x₃ h2 rfl
  have ep0 : (p, n₁) ∈ closedEdges W :=
    mem_closedEdges_pair W (W.length - 1) 0 (by omega) (by omega)
      (by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]) p n₁ rfl h0
  -- strict parameter inequalities at the extreme vertex
  have hlt₁ : f n₁ < f u := lt_of_le_of_ne (hmax' n₁ hn₁V) (fun h => hne01 (hfinj _ hn₁V _ huV h))
  have hlt₂ : f n₂ < f u := lt_of_le_of_ne (hmax' n₂ hn₂V) (fun h => hne12 (hfinj _ huV _ hn₂V h.symm))
  rcases lt_trichotomy (f n₁) (f n₂) with hcase | hcase | hcase
  · -- `n₂` lies inside the edge `n₁–u`; its other edge `n₂–x₃` meets it.
    have hmem : n₂ ∈ segment ℝ n₁ u := by
      rw [hfparam n₁ hn₁V, hfparam u huV, hfparam n₂ hn₂V]
      exact mem_segment_of_params p₀ v (f n₁) (f n₂) (f u) hcase hlt₂
    have hdis := hWsimple.2 (n₁, u) e01 (n₂, x₃) e23 hne02 hne03 hne12 hne13
    exact (Set.disjoint_left.mp hdis) hmem (left_mem_segment ℝ n₂ x₃)
  · exact hne02 (hfinj _ hn₁V _ hn₂V hcase)
  · -- `n₁` lies inside the edge `u–n₂`; its other edge `p–n₁` meets it.
    have hmem : n₁ ∈ segment ℝ u n₂ := by
      rw [hfparam n₁ hn₁V, hfparam u huV, hfparam n₂ hn₂V, segment_symm]
      exact mem_segment_of_params p₀ v (f n₂) (f n₁) (f u) hcase hlt₁
    have hdis := hWsimple.2 (u, n₂) e12 (p, n₁) ep0 hnep1 (Ne.symm hne01)
      hnep2 (Ne.symm hne02)
    exact (Set.disjoint_left.mp hdis) hmem (right_mem_segment ℝ p n₁)


/-! ## Normalisation with the convex-hull invariant

The variant below drops the non-vanishing hypothesis on the area and instead
reports the one way the deletion process can get stuck — at a *degenerate
triangle* — while carrying the invariant that every vertex of the original
polygon lies in the convex hull of the surviving ones.  Together with
`not_collinear_of_simple` this rules the stuck case out for polygons with at
least four vertices. -/

lemma exists_normalization_hull_aux :
    ∀ (n : ℕ) (V : List ℂ), V.length = n → 3 ≤ V.length → PolygonSimple V →
      ∃ V' : List ℂ, 3 ≤ V'.length ∧ V'.length ≤ V.length ∧ PolygonSimple V' ∧
        (∀ x ∈ V, x ∈ convexHull ℝ {y : ℂ | y ∈ V'}) ∧
        polyCycWind V' = polyCycWind V ∧
        HexArea.shoelace2 V' = HexArea.shoelace2 V ∧
        (polyCycNondeg V' ∨ (V'.length = 3 ∧ HexArea.shoelace2 V' = 0)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V hn h3 hsimple
    by_cases hnd : polyCycNondeg V
    · exact ⟨V, h3, le_rfl, hsimple, fun x hx => subset_convexHull ℝ _ hx, rfl, rfl, Or.inl hnd⟩
    obtain ⟨r, a, b, c, rest, hrot, hzero⟩ := exists_flat_cyclic_corner V h3 hnd
    have hWsimple : PolygonSimple (a :: b :: c :: rest) := by
      rw [← hrot]; exact (PolygonSimple_rotate V r).mpr hsimple
    have hWlen : (a :: b :: c :: rest).length = V.length := by rw [← hrot]; simp
    have hWarea : HexArea.shoelace2 (a :: b :: c :: rest) = HexArea.shoelace2 V := by
      rw [← hrot]; exact shoelace2_rotate V r
    have hWwind : polyCycWind (a :: b :: c :: rest) = polyCycWind V := by
      rw [← hrot]; exact polyCycWind_rotate V r h3
    have hWmem : ∀ x, x ∈ (a :: b :: c :: rest) ↔ x ∈ V := by
      intro x; rw [← hrot]; exact List.mem_rotate
    by_cases hrest : rest = []
    · -- stuck: a degenerate triangle
      subst hrest
      refine ⟨[a, b, c], by simp, by omega, hWsimple, ?_, hWwind, hWarea, Or.inr ⟨by simp, ?_⟩⟩
      · intro x hx
        exact subset_convexHull ℝ _ ((hWmem x).mpr hx)
      · rw [shoelace2_triple_eq_cross]; exact hzero
    obtain ⟨hsimple₁, hwind₁, harea₁, hflat⟩ :=
      flat_removal_step a b c rest hrest hWsimple hzero
    have hrestlen : 1 ≤ rest.length := List.length_pos_iff.mpr hrest
    have h3₁ : 3 ≤ (a :: c :: rest).length := by simp; omega
    have hlt : (a :: c :: rest).length < n := by
      rw [← hn]; simp only [List.length_cons] at hWlen ⊢; omega
    obtain ⟨V', hV'3, hV'le, hV'simple, hV'hull, hV'wind, hV'area, hV'case⟩ :=
      IH (a :: c :: rest).length hlt (a :: c :: rest) rfl h3₁ hsimple₁
    refine ⟨V', hV'3, ?_, hV'simple, ?_, ?_, ?_, hV'case⟩
    · simp only [List.length_cons] at hV'le hWlen ⊢; omega
    · -- the hull invariant: the deleted apex sits on the segment `[a, c]`
      intro x hx
      have hxW : x ∈ (a :: b :: c :: rest) := (hWmem x).mpr hx
      have haH : a ∈ convexHull ℝ {y : ℂ | y ∈ V'} := hV'hull a (by simp)
      have hcH : c ∈ convexHull ℝ {y : ℂ | y ∈ V'} := hV'hull c (by simp)
      rcases List.mem_cons.mp hxW with rfl | hx1
      · exact haH
      rcases List.mem_cons.mp hx1 with rfl | hx2
      · exact (convex_convexHull ℝ {y : ℂ | y ∈ V'}).segment_subset haH hcH hflat
      · exact hV'hull x (by
          rcases List.mem_cons.mp hx2 with rfl | hx3
          · simp
          · simp [hx3])
    · rw [hV'wind, hwind₁, hWwind]
    · rw [hV'area, harea₁, hWarea]

lemma exists_normalization_hull (V : List ℂ) (h3 : 3 ≤ V.length) (hsimple : PolygonSimple V) :
    ∃ V' : List ℂ, 3 ≤ V'.length ∧ V'.length ≤ V.length ∧ PolygonSimple V' ∧
      (∀ x ∈ V, x ∈ convexHull ℝ {y : ℂ | y ∈ V'}) ∧
      polyCycWind V' = polyCycWind V ∧
      HexArea.shoelace2 V' = HexArea.shoelace2 V ∧
      (polyCycNondeg V' ∨ (V'.length = 3 ∧ HexArea.shoelace2 V' = 0)) :=
  exists_normalization_hull_aux V.length V rfl h3 hsimple

/-- The line through `p₀` with direction `v` is convex. -/
lemma convex_line (p₀ v : ℂ) : Convex ℝ {w : ℂ | ∃ t : ℝ, w = p₀ + (t : ℂ) * v} := by
  rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩ α β hα hβ hαβ
  refine ⟨α * s + β * t, ?_⟩
  simp only [Complex.real_smul]
  have : ((α : ℂ)) + (β : ℂ) = 1 := by exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) hαβ
  push_cast
  linear_combination p₀ * this

/-- **A degenerate normalisation is impossible for four or more vertices.**  If a
simple polygon with at least four vertices normalised to a degenerate triangle,
all of its vertices would lie on a line, contradicting
`not_collinear_of_simple`. -/
lemma no_degenerate_normalization (V : List ℂ) (h4 : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (V' : List ℂ) (hV'simple : PolygonSimple V')
    (hV'3 : V'.length = 3) (hV'area : HexArea.shoelace2 V' = 0)
    (hhull : ∀ x ∈ V, x ∈ convexHull ℝ {y : ℂ | y ∈ V'}) : False := by
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z, V' = [x, y, z] := by
    match V', hV'3 with
    | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
  have hnd : ([x, y, z] : List ℂ).Nodup := hV'simple.1
  simp only [List.nodup_cons, List.mem_cons] at hnd
  have hxy : x ≠ y := by tauto
  have hv : y - x ≠ 0 := sub_ne_zero_of_ne (Ne.symm hxy)
  have hcr : HexArea.cross (y - x) (z - x) = 0 := by
    rw [shoelace2_triple_eq_cross] at hV'area
    simp [HexArea.cross] at hV'area ⊢
    linarith
  obtain ⟨t, ht⟩ := exists_real_of_cross_zero (y - x) (z - x) hv hcr
  -- the line through `x` with direction `y - x`
  have hsub : {w : ℂ | w ∈ ([x, y, z] : List ℂ)} ⊆ {w : ℂ | ∃ s : ℝ, w = x + (s : ℂ) * (y - x)} := by
    intro w hw
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by push_cast; ring⟩
    · exact ⟨t, by linear_combination ht⟩
  have hhull' : ∀ w ∈ V, ∃ s : ℝ, w = x + (s : ℂ) * (y - x) := by
    intro w hw
    exact convexHull_min hsub (convex_line x (y - x)) (hhull w hw)
  exact not_collinear_of_simple V h4 hsimple x (y - x) hv hhull'

end
