/-
# Orientation of the pair loop: the corner at `v` is convex

This file finishes the geometric route to `pair_winding_relation`.  It sits
between `RequestProject.SAWPairLoopWinding` (which builds the loop, proves it is
a simple closed hex trail and applies the Umlaufsatz to it) and
`RequestProject.SAWPairCancellation` (which consumes `pair_winding_relation`).

## What is missing and why

`pair_loop_umlauf` gives `W(loop) + τ_corner = ±2π`; the local angle
bookkeeping gives `τ_corner = ±π/3`.  The assembly of Lemma 1 needs the *sign*
to be matched, i.e. `W(loop) + τ_corner = 6 · τ_corner`, equivalently
`W(loop) = 5 · τ_corner`.  Geometrically this says that the corner of the loop
at `v` is **convex** for the loop's own orientation.

The argument:

1. At a honeycomb vertex the three edge directions are `120°` apart, so the two
   loop edges at `v` span a `120°` sector on one side and a `240°` sector on the
   other, and the *third* edge at `v` always points into the `240°` (reflex)
   sector.  Hence the corner at `v` is convex **iff** the third neighbour
   `n_m := hexNeighbors3 v (pairArriveIdx …)` lies **outside** the loop.
2. The third edge at `v` is the last edge of the prefix, which runs back to
   `paperStart`.  Because the honeycomb is 3-regular and the loop already uses
   two edges at each of its vertices, the prefix cannot touch the loop except at
   `v` (a prefix visit to a loop vertex would need two more free edges there).
   So `n_m` and `paperStart` lie in the same component of the complement.
3. `paperStart` is outside the loop: every strip vertex embeds with real part
   `≥ 1` (`strip_embed_re_ge_one`) and `correctHexEmbed paperStart = 1`, so the
   horizontal ray from `paperStart` in the direction `-1` meets no point of the
   loop; `ptWind_eq_zero_of_ray_avoids` then gives winding `0`.

Steps 1–3 are recorded below as `pair_corner_turn_sign` (the single remaining
geometric sorry, packaging 1–3) together with the two facts that are already
proved here, `strip_embed_re_ge_one` and `correctHexEmbed_paperStart`.

Everything after `pair_loop_turning_eq` is the local angle bookkeeping at `v`
and the final assembly, moved here unchanged from
`RequestProject.SAWPairLoopWinding`.
-/

import Mathlib
import RequestProject.SAWPairLoopWinding
import RequestProject.SAWUmlaufPtWindRay
import RequestProject.SAWVEdgeCountAux

open Real Complex ComplexConjugate Filter Topology
open HexArea

noncomputable section

set_option maxHeartbeats 1600000

variable {T L : ℕ} {v : HexVertex} {k : Fin 3}

/-! ## Preparation: the strip lies in the half plane `re ≥ 1` -/

/-- The embedding of `paperStart` is `1`. -/
lemma correctHexEmbed_paperStart : correctHexEmbed paperStart = 1 := by
  simp [correctHexEmbed, paperStart, Complex.ext_iff]

/-- Every vertex of the strip embeds into the closed half plane `re ≥ 1`.
This is what makes the leftward ray from `paperStart` escape: it is the
separation input for `pair_corner_turn_sign`. -/
lemma strip_embed_re_ge_one (T L : ℕ) (u : HexVertex) (hu : PaperFinStrip T L u) :
    1 ≤ (correctHexEmbed u).re := by
  obtain ⟨x, y, b⟩ := u
  obtain ⟨hinf, -⟩ := hu
  cases b
  · simp only [PaperInfStrip, if_false] at hinf
    have h : x + y ≤ -1 := hinf.2
    have : ((x : ℝ) + y) ≤ -1 := by exact_mod_cast h
    simp only [correctHexEmbed]
    norm_num
    linarith
  · simp only [PaperInfStrip, if_true] at hinf
    have h : x + y ≤ 0 := hinf.2
    have : ((x : ℝ) + y) ≤ 0 := by exact_mod_cast h
    simp only [correctHexEmbed]
    norm_num
    linarith

/-- `paperStart` is the **only** hex vertex embedding to `1`.  Together with
`strip_embed_re_ge_one` this says that the leftward ray from `correctHexEmbed
paperStart` meets no vertex of the strip, which is the separation input for
`pair_corner_turn_sign`. -/
lemma correctHexEmbed_eq_one_iff (u : HexVertex) :
    correctHexEmbed u = 1 ↔ u = paperStart := by
  obtain ⟨x, y, b⟩ := u
  constructor
  · intro h
    cases b
    · exfalso
      have hre : (-3 * ((x : ℝ) + y)) / 2 = 1 := by
        simpa [correctHexEmbed, Complex.ext_iff] using congrArg Complex.re h
      have : ((3 * (x + y) : ℤ) : ℝ) = -2 := by push_cast; linarith
      have : (3 * (x + y) : ℤ) = -2 := by exact_mod_cast this
      omega
    · have hre : (-3 * ((x : ℝ) + y)) / 2 + 1 = 1 := by
        simpa [correctHexEmbed, Complex.ext_iff] using congrArg Complex.re h
      have him : ((x : ℝ) - y) * Real.sqrt 3 / 2 = 0 := by
        simpa [correctHexEmbed, Complex.ext_iff] using congrArg Complex.im h
      have h3 : Real.sqrt 3 ≠ 0 := by positivity
      have hxy : ((x : ℝ) + y) = 0 := by linarith
      have hxy' : ((x : ℝ) - y) = 0 := by
        rcases mul_eq_zero.1 (by linarith : ((x : ℝ) - y) * Real.sqrt 3 = 0) with h | h
        · exact h
        · exact absurd h h3
      have hx : (x : ℝ) = 0 := by linarith
      have hy : (y : ℝ) = 0 := by linarith
      have hx' : x = 0 := by exact_mod_cast hx
      have hy' : y = 0 := by exact_mod_cast hy
      simp [paperStart, hx', hy']
  · intro h
    rw [h]
    exact correctHexEmbed_paperStart

/-! ## A leftward-ray separation criterion

A closed polygon contained in the closed half plane `re ≥ x.re`, avoiding `x`
itself and having no edge with *both* endpoints on the line `re = x.re`, has
winding number `0` around `x`: the ray from `x` in the direction `-1` escapes
without meeting the polygon. -/

lemma ptWind_eq_zero_of_left_ray (x : ℂ) (V : List ℂ)
    (hV : ∀ w ∈ V, x.re ≤ w.re)
    (hne : ∀ w ∈ V, w ≠ x)
    (hnoedge : ∀ p ∈ (V ++ V.take 1).zip ((V ++ V.take 1).drop 1),
        p.1.re = x.re → x.re < p.2.re) :
    ptWind x V = 0 := by
  refine ptWind_eq_zero_of_ray_avoids x 1 one_ne_zero V hne ?_
  intro p hp z hz
  rintro ⟨hzim, hzre⟩
  have hmemV : ∀ w ∈ V ++ V.take 1, x.re ≤ w.re := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hV w h
    · exact hV w (List.mem_of_mem_take h)
  have hmemV' : ∀ w ∈ V ++ V.take 1, w ≠ x := by
    intro w hw
    rcases List.mem_append.1 hw with h | h
    · exact hne w h
    · exact hne w (List.mem_of_mem_take h)
  have h1 : p.1 ∈ V ++ V.take 1 := (List.of_mem_zip hp).1
  have h2 : p.2 ∈ V ++ V.take 1 := List.mem_of_mem_drop (List.of_mem_zip hp).2
  have ha : x.re ≤ p.1.re := hmemV _ h1
  have hb : x.re ≤ p.2.re := hmemV _ h2
  simp only [div_one] at hz
  obtain ⟨s, t, hs, ht, hst, hz'⟩ := hz
  have hzre' : z.re = s * (p.1.re - x.re) + t * (p.2.re - x.re) := by
    rw [← hz']; simp [Complex.add_re, Complex.sub_re]
  have hs0 : s * (p.1.re - x.re) = 0 ∧ t * (p.2.re - x.re) = 0 := by
    constructor <;> nlinarith [mul_nonneg hs (by linarith : (0:ℝ) ≤ p.1.re - x.re),
      mul_nonneg ht (by linarith : (0:ℝ) ≤ p.2.re - x.re)]
  have hzim' : z.im = s * (p.1.im - x.im) + t * (p.2.im - x.im) := by
    rw [← hz']; simp [Complex.add_im, Complex.sub_im]
  rcases eq_or_lt_of_le hs with hs' | hs'
  · -- `s = 0`, so `z = p.2 - x`, forcing `p.2 = x`
    have ht1 : t = 1 := by linarith
    apply hmemV' _ h2
    have hre : p.2.re = x.re := by
      have := hs0.2; rw [ht1] at this; linarith
    have him : p.2.im = x.im := by
      rw [← hs', ht1] at hzim'; simp at hzim'; linarith
    exact Complex.ext hre him
  · rcases eq_or_lt_of_le ht with ht' | ht'
    · -- `t = 0`, so `z = p.1 - x`, forcing `p.1 = x`
      have hs1 : s = 1 := by linarith
      apply hmemV' _ h1
      have hre : p.1.re = x.re := by
        have := hs0.1; rw [hs1] at this; linarith
      have him : p.1.im = x.im := by
        rw [← ht', hs1] at hzim'; simp at hzim'; linarith
      exact Complex.ext hre him
    · -- both `s, t > 0`: both endpoints lie on the line `re = x.re`
      have hre1 : p.1.re = x.re := by
        have := hs0.1
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (ne_of_gt hs')
        · linarith
      have hre2 : p.2.re = x.re := by
        have := hs0.2
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h (ne_of_gt ht')
        · linarith
      exact absurd hre2 (ne_of_gt (hnoedge p hp hre1))

/-! ### Specialisation to a closed hexagonal cycle in the strip -/

/-- A hex vertex embedding onto the line `re = 1` is on the TRUE sublattice. -/
lemma correctHexEmbed_re_eq_one_true (u : HexVertex)
    (h : (correctHexEmbed u).re = 1) : u.2.2 = true := by
  obtain ⟨x, y, b⟩ := u
  cases b
  · exfalso
    have hre : (-3 * ((x : ℝ) + y)) / 2 = 1 := by
      simpa [correctHexEmbed] using h
    have h1 : ((3 * (x + y) : ℤ) : ℝ) = -2 := by push_cast; linarith
    have h2 : (3 * (x + y) : ℤ) = -2 := by exact_mod_cast h1
    omega
  · rfl

/-- The honeycomb lattice is bipartite: adjacent vertices lie on different
sublattices. -/
lemma hexGraph_adj_bool_ne {u w : HexVertex} (h : hexGraph.Adj u w) :
    u.2.2 ≠ w.2.2 := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> simp [h1, h2]

lemma isChain_zip_drop {α : Type*} (R : α → α → Prop) :
    ∀ (l : List α), List.IsChain R l → ∀ p ∈ l.zip (l.drop 1), R p.1 p.2 := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b s =>
      intro h p hp
      simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons,
        List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact (List.isChain_cons.1 h).1 b rfl
      · exact ih (List.isChain_cons.1 h).2 p (by simpa using hp)

/-- **Separation for a closed hexagonal cycle inside the strip.**  A cyclically
adjacent list of strip vertices not containing `paperStart` has winding number
`0` around `paperStart`. -/
lemma ptWind_paperStart_of_hexCycle (T L : ℕ) (Vs : List HexVertex)
    (hstrip : ∀ u ∈ Vs, PaperFinStrip T L u)
    (hns : paperStart ∉ Vs)
    (hchain : List.IsChain hexGraph.Adj (Vs ++ Vs.take 1)) :
    ptWind (correctHexEmbed paperStart) (Vs.map correctHexEmbed) = 0 := by
  rw [correctHexEmbed_paperStart]
  set W := Vs ++ Vs.take 1 with hW
  have hWmem : ∀ u ∈ W, u ∈ Vs := by
    intro u hu
    rcases List.mem_append.1 hu with h | h
    · exact h
    · exact List.mem_of_mem_take h
  have hmap : (Vs.map correctHexEmbed) ++ (Vs.map correctHexEmbed).take 1
      = W.map correctHexEmbed := by
    rw [hW, List.map_append, List.map_take]
  refine ptWind_eq_zero_of_left_ray 1 (Vs.map correctHexEmbed) ?_ ?_ ?_
  · rintro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
    simpa using strip_embed_re_ge_one T L u (hstrip u hu)
  · rintro w hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
    intro hcon
    exact hns ((correctHexEmbed_eq_one_iff u).1 hcon ▸ hu)
  · intro p hp hp1
    rw [hmap] at hp
    have hzip : (W.map correctHexEmbed).zip ((W.map correctHexEmbed).drop 1)
        = (W.zip (W.drop 1)).map (fun q => (correctHexEmbed q.1, correctHexEmbed q.2)) := by
      rw [← List.map_drop, List.zip_map]
      rfl
    rw [hzip] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hadj : hexGraph.Adj q.1 q.2 := isChain_zip_drop _ W hchain q hq
    have hq1 : q.1 ∈ Vs := hWmem _ (List.of_mem_zip hq).1
    have hq2 : q.2 ∈ Vs := hWmem _ (List.mem_of_mem_drop (List.of_mem_zip hq).2)
    have hb1 : q.1.2.2 = true := by
      apply correctHexEmbed_re_eq_one_true
      simpa using hp1
    have hb2 : q.2.2.2 = false := by
      have := hexGraph_adj_bool_ne hadj
      rw [hb1] at this
      cases hqb : q.2.2.2
      · rfl
      · exact absurd hqb (by simpa using this)
    have hge : (1 : ℝ) ≤ (correctHexEmbed q.2).re :=
      strip_embed_re_ge_one T L q.2 (hstrip _ hq2)
    have hne : (correctHexEmbed q.2).re ≠ 1 := by
      intro hcon
      rw [correctHexEmbed_re_eq_one_true q.2 hcon] at hb2
      exact absurd hb2 (by simp)
    simpa using lt_of_le_of_ne hge (Ne.symm hne)

/-! ## Step 3: the corner is convex for the loop's orientation -/

/-- The loop, as a closed polygon in `ℂ`. -/
def pairLoopPoly (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) : List ℂ :=
  (v :: (pairInner hv_ne γ).support).map correctHexEmbed

/-! **`paperStart` is outside the loop.**  Every strip vertex embeds with real
part `≥ 1` (`strip_embed_re_ge_one`), `paperStart` embeds to `1`
(`correctHexEmbed_paperStart`) and is the only hex vertex that does
(`correctHexEmbed_eq_one_iff`); no hex edge lies inside the line `re = 1`.  So
`ptWind_eq_zero_of_left_ray` applies, via `ptWind_paperStart_of_hexCycle`. -/

/-- The vertices of the loop are strip vertices. -/
lemma pairLoop_verts_strip (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∀ u ∈ (v :: (pairInner hv_ne γ).support), PaperFinStrip T L u := by
  have hsupp : γ.1.walk.support
      = (pairPrefix hv_ne γ).support ++ (pairInner hv_ne γ).support := by
    conv_lhs => rw [pairDecomp hv_ne γ]
    rw [SimpleGraph.Walk.support_append]
    rfl
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact hv
  · exact γ.1.in_strip u (by rw [hsupp]; exact List.mem_append_right _ hu)

/-- `paperStart` is not a vertex of the loop: it would need two of its three
edges for the loop, leaving none for the (non-empty) prefix. -/
lemma paperStart_not_mem_pairLoop (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    paperStart ∉ (v :: (pairInner hv_ne γ).support) := by
  intro hmem
  have hOrig : s(hexNeighbors3 paperStart 0, paperStart) ∉ γ.1.walk.edges := by
    intro hme
    have hmemsup : hexOrigin ∈ γ.1.walk.support :=
      γ.1.walk.fst_mem_support_of_mem_edges hme
    exact hexOrigin_not_in_strip T (γ.1.in_strip _ hmemsup).1
  have hle2 : vEdgeCount paperStart γ.1.walk ≤ 2 :=
    vEdgeCount_le_two_excluding paperStart 0 γ.1.walk γ.1.is_trail hOrig
  have h1 : 0 < vEdgeCount paperStart (pairPrefix hv_ne γ) := by
    have hpar := vEdgeCount_parity paperStart v (pairPrefix hv_ne γ) paperStart
    rw [if_pos rfl, if_neg (Ne.symm hv_ne)] at hpar
    omega
  have h2 : 0 < vEdgeCount paperStart
      (SimpleGraph.Walk.cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ)) (pairInner hv_ne γ)) :=
    vEdgeCount_pos_of_mem_support_ne_start _ paperStart hmem (Ne.symm hv_ne)
  have hsum : vEdgeCount paperStart γ.1.walk
      = vEdgeCount paperStart (pairPrefix hv_ne γ)
        + vEdgeCount paperStart
            (SimpleGraph.Walk.cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ))
              (pairInner hv_ne γ)) := by
    conv_lhs => rw [pairDecomp hv_ne γ]
    exact vEdgeCount_append paperStart _ _
  have hpar := vEdgeCount_parity paperStart (hexNeighbors3 v k) γ.1.walk paperStart
  rw [if_pos rfl] at hpar
  have hnk : hexNeighbors3 v k = paperStart := by
    by_contra hne
    rw [if_neg (Ne.symm hne)] at hpar
    omega
  have hadjv : hexGraph.Adj paperStart v := by
    have hh := γ.1.adj; rwa [hnk] at hh
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, v = hexNeighbors3 paperStart j := by
    rcases hexNeighbors3_complete paperStart v hadjv with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [hj] at hv
    exact hexOrigin_not_in_strip T hv.1
  have hfresh : s(hexNeighbors3 paperStart j, paperStart) ∉ γ.1.walk.edges := by
    have heq : s(hexNeighbors3 paperStart j, paperStart) = s(hexNeighbors3 v k, v) := by
      rw [hnk, ← hj, Sym2.eq_swap]
    rw [heq]
    exact γ.1.fresh
  have hle1 :=
    vEdgeCount_le_one_of_two_excluded (Ne.symm hj0) γ.1.walk γ.1.is_trail hOrig hfresh
  omega

/-- A `HexTrailList` of length at least two, whose first step is adjacent, is a
chain of adjacencies. -/
lemma hexTrailList_isChain :
    ∀ (l : List HexVertex) (a b : HexVertex), HexTrailList (a :: b :: l) →
      hexGraph.Adj a b → List.IsChain hexGraph.Adj (a :: b :: l) := by
  intro l
  induction l with
  | nil => intro a b _ hab; exact List.isChain_pair.2 hab
  | cons c t ih =>
    intro a b h hab
    obtain ⟨-, hbc, -, hrest⟩ := h
    exact List.isChain_cons_cons.2 ⟨hab, ih b c hrest hbc⟩

/-- The loop's vertex list is cyclically adjacent. -/
lemma pairLoop_isChain (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    List.IsChain hexGraph.Adj
      ((v :: (pairInner hv_ne γ).support) ++ (v :: (pairInner hv_ne γ).support).take 1) := by
  have hcat : (v :: (pairInner hv_ne γ).support) ++
      (v :: (pairInner hv_ne γ).support).take 1 = pairLoopList hv_ne γ := by
    simp [pairLoopList]
  rw [hcat, pairLoopList, pairInner_support_head hv_ne γ]
  refine hexTrailList_isChain _ _ _ ?_ (hexNeighbors3_adj v (pairExitIdx hv_ne γ))
  have h := pair_suffix_hex_trail hv_ne γ
  simpa using h

lemma pairLoop_ptWind_paperStart (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ptWind (correctHexEmbed paperStart) (pairLoopPoly hv_ne γ) = 0 :=
  ptWind_paperStart_of_hexCycle T L _ (pairLoop_verts_strip hv hv_ne γ)
    (paperStart_not_mem_pairLoop hv hv_ne γ) (pairLoop_isChain hv_ne γ)

/-- **The third neighbour of `v` is outside the loop.**  The prefix runs from
`paperStart` to `v` and, by 3-regularity, cannot meet the loop before `v` (a
prefix visit to a loop vertex would need two more free edges there); so `n_m`
and `paperStart` lie in the same component of the complement, and the winding
number is constant on components. -/
lemma pairLoop_ptWind_arrive_of_start (hv : PaperFinStrip T L v)
    (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k)
    (hstart : ptWind (correctHexEmbed paperStart) (pairLoopPoly hv_ne γ) = 0) :
    ptWind (correctHexEmbed (hexNeighbors3 v (pairArriveIdx hv_ne γ)))
      (pairLoopPoly hv_ne γ) = 0 := by
  sorry

lemma pairLoop_ptWind_arrive (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ptWind (correctHexEmbed (hexNeighbors3 v (pairArriveIdx hv_ne γ)))
      (pairLoopPoly hv_ne γ) = 0 :=
  pairLoop_ptWind_arrive_of_start hv hv_ne γ (pairLoop_ptWind_paperStart hv hv_ne γ)

/-- **Convexity of the corner from the third neighbour being outside.**  At a
honeycomb vertex the third direction lies in the reflex sector spanned by the
other two, so the corner of the loop at `v` is convex exactly when the third
neighbour is outside the loop. -/
lemma pair_corner_turn_sign_of_outside (hv : PaperFinStrip T L v)
    (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k)
    (hout : ptWind (correctHexEmbed (hexNeighbors3 v (pairArriveIdx hv_ne γ)))
      (pairLoopPoly hv_ne γ) = 0) :
    0 < (hexWalkWinding (pairLoopList hv_ne γ) + pairCornerTurn hv_ne γ)
          * pairCornerTurn hv_ne γ := by
  sorry

/-- **The remaining geometric input.**  The total turning of the loop and the
turn of the loop at `v` have the same sign: the corner of the loop at `v` is
convex for the loop's own orientation. -/
lemma pair_corner_turn_sign (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    0 < (hexWalkWinding (pairLoopList hv_ne γ) + pairCornerTurn hv_ne γ)
          * pairCornerTurn hv_ne γ :=
  pair_corner_turn_sign_of_outside hv hv_ne γ (pairLoop_ptWind_arrive hv hv_ne γ)

/-! ## The local angle bookkeeping at `v` -/

/-- The three indices `m`, `e`, `k` at `v` are pairwise distinct, hence
    `{e, k} = fin3_other m` in one of the two orders. -/
lemma pair_index_cases (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    (pairExitIdx hv_ne γ = (fin3_other (pairArriveIdx hv_ne γ)).1 ∧
      k = (fin3_other (pairArriveIdx hv_ne γ)).2) ∨
    (pairExitIdx hv_ne γ = (fin3_other (pairArriveIdx hv_ne γ)).2 ∧
      k = (fin3_other (pairArriveIdx hv_ne γ)).1) := by
  have h1 : pairArriveIdx hv_ne γ ≠ k := pairArriveIdx_ne_k hv_ne γ
  have h2 : pairArriveIdx hv_ne γ ≠ pairExitIdx hv_ne γ := pairArriveIdx_ne_exit hv_ne γ
  have h3 : pairExitIdx hv_ne γ ≠ k := pairExitIdx_ne hv_ne γ
  revert h1 h2 h3
  generalize pairArriveIdx hv_ne γ = m
  generalize pairExitIdx hv_ne γ = e
  fin_cases m <;> fin_cases e <;> fin_cases k <;> simp_all [fin3_other]

/-- Pure index bookkeeping for case A: if `e` and `k` are the first and second
    complements of `m`, then `e` is the *second* complement of `k`. -/
lemma fin3_other_shift_A {m e kk : Fin 3} (h1 : e = (fin3_other m).1)
    (h2 : kk = (fin3_other m).2) : e = (fin3_other kk).2 := by
  subst h1; subst h2; fin_cases m <;> simp [fin3_other]

/-- Pure index bookkeeping for case B. -/
lemma fin3_other_shift_B {m e kk : Fin 3} (h1 : e = (fin3_other m).2)
    (h2 : kk = (fin3_other m).1) : e = (fin3_other kk).1 := by
  subst h1; subst h2; fin_cases m <;> simp [fin3_other]

/-- Case A of `pair_index_cases`: `e = m+1`, `k = m+2`.  Then the entry turn is
    `-π/3`, the reversed entry turn is `+π/3` and the corner turn is `+π/3`. -/
lemma pair_turns_case_A (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k)
    (h1 : pairExitIdx hv_ne γ = (fin3_other (pairArriveIdx hv_ne γ)).1)
    (h2 : k = (fin3_other (pairArriveIdx hv_ne γ)).2) :
    pairEntryTurn hv_ne γ = -(Real.pi / 3) ∧
    pairEntryTurnRev hv_ne γ = Real.pi / 3 ∧
    pairCornerTurn hv_ne γ = Real.pi / 3 := by
  have hA := fin3_other_shift_A h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [pairEntryTurn, h1, turning_angle_k]; ring
  · have h := turning_angle_l v (pairArriveIdx hv_ne γ)
    rw [← h2] at h
    exact h
  · have h := turning_angle_l v k
    rw [← hA] at h
    exact h

/-- Case B of `pair_index_cases`: `e = m+2`, `k = m+1`. -/
lemma pair_turns_case_B (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k)
    (h1 : pairExitIdx hv_ne γ = (fin3_other (pairArriveIdx hv_ne γ)).2)
    (h2 : k = (fin3_other (pairArriveIdx hv_ne γ)).1) :
    pairEntryTurn hv_ne γ = Real.pi / 3 ∧
    pairEntryTurnRev hv_ne γ = -(Real.pi / 3) ∧
    pairCornerTurn hv_ne γ = -(Real.pi / 3) := by
  have hB := fin3_other_shift_B h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rw [pairEntryTurn, h1, turning_angle_l]
  · have h := turning_angle_k v (pairArriveIdx hv_ne γ)
    rw [← h2] at h
    rw [pairEntryTurnRev, h]; ring
  · have h := turning_angle_k v k
    rw [← hB] at h
    rw [pairCornerTurn, h]; ring


/-! ## `pair_loop_turning_eq` from the Umlaufsatz and the sign -/

/-- The corner turn at `v` is `±π/3`. -/
lemma pairCornerTurn_cases (hv_ne : v ≠ paperStart) (γ : FreshIncomingPair T L v k) :
    pairCornerTurn hv_ne γ = Real.pi / 3 ∨ pairCornerTurn hv_ne γ = -(Real.pi / 3) := by
  rcases pair_index_cases hv_ne γ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (pair_turns_case_A hv_ne γ h1 h2).2.2
  · exact Or.inr (pair_turns_case_B hv_ne γ h1 h2).2.2

/-- `W(loop) = 5 · τ_corner`: the Umlaufsatz value `±2π` is selected by the sign
of the corner turn. -/
lemma pair_loop_turning_eq (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexWalkWinding (pairLoopList hv_ne γ) = 5 * pairCornerTurn hv_ne γ := by
  have hpi := Real.pi_pos
  have hsign := pair_corner_turn_sign hv hv_ne γ
  rcases pair_loop_umlauf hv_ne γ with h | h <;>
    rcases pairCornerTurn_cases hv_ne γ with hc | hc <;>
    rw [hc] at h hsign ⊢ <;> nlinarith [h, hsign]

/-! ## Assembly -/

/-- The two members of a pair share their prefix, hence their first edge. -/
lemma pair_fullSupport_take_two (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    γ.1.fullSupport.take 2 = (pairInvol hv hv_ne γ).1.fullSupport.take 2 := by
  have h2 : 2 ≤ (pairPrefix hv_ne γ).support.length := by
    rw [pairPrefix_support_split hv_ne γ]; simp
  rw [original_fullSupport_eq hv_ne γ, paired_fullSupport_eq hv hv_ne γ]
  simp only [List.append_assoc]
  rw [List.take_append_of_le_length h2, List.take_append_of_le_length h2]

/-- The winding relation for loop-reversed pairs, for the raw (first-edge)
    normalisation of the winding. -/
theorem pair_winding_relation_geom_raw (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∃ (W_common : ℝ) (jj : Fin 3),
      ((k = (fin3_other jj).1 ∧ pairExitIdx hv_ne γ = (fin3_other jj).2 ∧
        γ.1.rawWinding = W_common - 4 * Real.pi / 3 ∧
        (pairInvol hv hv_ne γ).1.rawWinding = W_common + 4 * Real.pi / 3) ∨
       (k = (fin3_other jj).2 ∧ pairExitIdx hv_ne γ = (fin3_other jj).1 ∧
        γ.1.rawWinding = W_common + 4 * Real.pi / 3 ∧
        (pairInvol hv hv_ne γ).1.rawWinding = W_common - 4 * Real.pi / 3)) ∧
      (pairInvol hv hv_ne γ).1.len = γ.1.len := by
  refine ⟨hexWalkWinding (pairPrefix hv_ne γ).support, pairArriveIdx hv_ne γ, ?_, ?_⟩
  · have hsplit := pair_winding_split hv_ne γ
    have hsplitr := pair_winding_split_rev hv hv_ne γ
    have hrev := pairLoopListRev_winding hv_ne γ
    have hturn := pair_loop_turning_eq hv hv_ne γ
    rcases pair_index_cases hv_ne γ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨he, her, hc⟩ := pair_turns_case_A hv_ne γ h1 h2
      right
      refine ⟨h2, h1, ?_, ?_⟩
      · rw [hsplit, he, hturn, hc]; ring
      · rw [hsplitr, her, hrev, hturn, hc]; ring
    · obtain ⟨he, her, hc⟩ := pair_turns_case_B hv_ne γ h1 h2
      left
      refine ⟨h2, h1, ?_, ?_⟩
      · rw [hsplit, he, hturn, hc]; ring
      · rw [hsplitr, her, hrev, hturn, hc]; ring
  · exact pairInvol_length hv hv_ne γ

/-- The winding relation for loop-reversed pairs, in the exact form consumed by
    `pair_exp_cancellation`.  Both members of the pair share their first edge,
    so the relation is insensitive to the normalisation of the winding. -/
theorem pair_winding_relation_geom (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∃ (W_common : ℝ) (jj : Fin 3),
      ((k = (fin3_other jj).1 ∧ pairExitIdx hv_ne γ = (fin3_other jj).2 ∧
        γ.1.winding = W_common - 4 * Real.pi / 3 ∧
        (pairInvol hv hv_ne γ).1.winding = W_common + 4 * Real.pi / 3) ∨
       (k = (fin3_other jj).2 ∧ pairExitIdx hv_ne γ = (fin3_other jj).1 ∧
        γ.1.winding = W_common + 4 * Real.pi / 3 ∧
        (pairInvol hv hv_ne γ).1.winding = W_common - 4 * Real.pi / 3)) ∧
      (pairInvol hv hv_ne γ).1.len = γ.1.len := by
  obtain ⟨W, jj, hcases, hlen⟩ := pair_winding_relation_geom_raw hv hv_ne γ
  set c := hexHeadTurn hexOrigin γ.1.fullSupport with hc
  have h1 : γ.1.winding = c + γ.1.rawWinding := γ.1.winding_eq
  have h2 : (pairInvol hv hv_ne γ).1.winding
      = c + (pairInvol hv hv_ne γ).1.rawWinding := by
    rw [FreshTrail.winding_eq, hc,
      hexHeadTurn_congr hexOrigin (pair_fullSupport_take_two hv hv_ne γ)]
  refine ⟨W + c, jj, ?_, hlen⟩
  rcases hcases with ⟨ha, hb, hx, hy⟩ | ⟨ha, hb, hx, hy⟩
  · exact Or.inl ⟨ha, hb, by rw [h1, hx]; ring, by rw [h2, hy]; ring⟩
  · exact Or.inr ⟨ha, hb, by rw [h1, hx]; ring, by rw [h2, hy]; ring⟩

end
