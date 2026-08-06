import Mathlib
import RequestProject.SAWUmlaufFlatRemoval
import RequestProject.SAWUmlaufChordLiftAux
import RequestProject.SAWUmlaufTriangleClosed

/-!
# `SAWUmlaufFlatSeamLift` — lifting an ear across a flat seam vertex

This file supplies the **flat-seam residual** of `interior_lift_via_piece`
(`RequestProject.SAWUmlaufPolyMeisters`), the last structural gap of the
Meisters recursion for the planar Umlaufsatz.

## The situation

Cutting a simple, cyclically non-degenerate polygon `W` along an interior
diagonal `W[0]–W[k]` produces two pieces.  All corners of a piece except the two
*seam* corners (at the two cut endpoints) are corners of `W`, hence non-flat;
but a seam corner may well be flat, and then the piece is **not**
`polyCycNondeg`, so the Meisters induction hypothesis cannot be applied to it
directly.  The repair is classical: delete the flat vertex (the deletion is
again simple, and has the same turning and the same area, see
`RequestProject.SAWUmlaufFlatRemoval`), recurse on the deletion, and **lift the
returned ear back across the deletion**.  This file performs that lift.

Throughout, the cycle is written as `v :: L` with `v` the flat vertex, so that
`n = L.head` is the cyclic successor of `v` and `m = L.getLast` its cyclic
predecessor, and flatness reads `v - m = s (n - m)` with `0 < s < 1`.

## Contents

* `flatSeam_rotate_cons_succ`, `flatSeam_ear_index`, `flatSeam_insert_rotation` —
  the rotation surgery.  An ear rotation of `L` whose tip avoids the two
  neighbours `m`, `n` of `v` is *also* an ear rotation of `v :: L`, with `v`
  re-inserted into the tail at the seam.  (The tip avoids `m` and `n` exactly
  because the recursion forbids the seam edge `{m, n}` of `L`, which is the
  reason the Meisters invariant `EmptyCornerData2` forbids a whole *edge*.)
* `flatSeam_shoelace2_triple_flat`, `flatSeam_shoelace2_insert` — the signed area
  of the clipped cycle is unchanged by re-inserting the flat vertex, so the
  orientation clause of the ear survives the lift.
* `flatSeam_avoids_ear` — the flat vertex is neither strictly inside the returned
  ear triangle nor on its diagonal; this is the ear-clearance property
  (`ear_edge_interior_not_strict` / `ear_edge_interior_not_base` of
  `RequestProject.SAWUmlaufTriangleClosed`) applied to the seam edge, the flat
  vertex being an interior point of it.
* `flatSeam_quad_ear` (proved) — the base case `L.length = 3`: a quadrilateral
  with a flat vertex `v` has an ear at *each* of the two neighbours of `v`.
* `flatSeam_ear_lift` — the lift itself.
* `flatSeam_delete_simple`, `EmptyCornerData2_rotate`, `FlatSeamData`,
  `flatSeam_EmptyCornerData2_of_data` — the packaging consumed by
  `interior_lift_via_piece`.
* `interior_flat_seam_data_left/right`, `interior_flat_seam_data` — in the
  Meisters interior branch a degenerate chord piece is flat exactly at the cut
  endpoint `w`, and deleting `w` restores non-degeneracy.

The whole file is `sorry`-free.
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. Rotation surgery -/

/-- Rotating `v :: L` by `r + 1` moves the head `v` into the tail, at the seam. -/
lemma flatSeam_rotate_cons_succ (v : ℂ) (L : List ℂ) (r : ℕ) (hr : r ≤ L.length) :
    (v :: L).rotate (r + 1) = L.drop r ++ v :: L.take r := by
  rw [List.rotate_cons_succ, List.rotate_eq_drop_append_take (by simp; omega),
    List.drop_append_of_le_length hr, List.take_append_of_le_length hr]
  simp

/-- **The ear tip is far from the seam.**  If a rotation of `L` exhibits the
cyclically consecutive triple `a, b, c` and the tip `b` is neither the head `n`
nor the last vertex `m` of `L`, then the rotation index can be normalised to
`ρ` with `ρ + 3 ≤ L.length`, i.e. the whole triple sits inside `L.drop ρ`. -/
lemma flatSeam_ear_index (L : List ℂ) (m n : ℂ)
    (hn : L.head? = some n) (hm : L.getLast? = some m)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate r = a :: b :: c :: rest)
    (hbn : b ≠ n) (hbm : b ≠ m) :
    ∃ ρ : ℕ, ρ + 3 ≤ L.length ∧ L.rotate ρ = a :: b :: c :: rest := by
  have hN : 3 ≤ L.length := by
    have := congrArg List.length hrot; simp at this; omega
  set ρ := r % L.length with hρdef
  have hρlt : ρ < L.length := Nat.mod_lt _ (by omega)
  have hrotρ : L.rotate ρ = a :: b :: c :: rest := by
    rw [hρdef, List.rotate_mod]; exact hrot
  refine ⟨ρ, ?_, hrotρ⟩
  by_contra hcon
  push_neg at hcon
  have hsplit : L.drop ρ ++ L.take ρ = a :: b :: c :: rest := by
    rw [← List.rotate_eq_drop_append_take (le_of_lt hρlt)]; exact hrotρ
  have hdroplen : (L.drop ρ).length = L.length - ρ := by simp
  have hdropne : L.drop ρ ≠ [] := by
    intro h
    rw [h] at hdroplen; simp at hdroplen; omega
  have hLsplit : L.take ρ ++ L.drop ρ = L := List.take_append_drop _ _
  have hlastdrop : (L.drop ρ).getLast? = some m := by
    have h := List.getLast?_append_of_ne_nil (L.take ρ) hdropne
    rw [hLsplit] at h
    rw [← h]; exact hm
  rcases (by omega : L.length - ρ = 1 ∨ L.length - ρ = 2) with h1 | h2
  · -- `L.drop ρ = [m]`, so the tip `b` is the head `n` of `L`
    have hlen1 : (L.drop ρ).length = 1 := by omega
    obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen1
    have hym : y = m := by rw [hy] at hlastdrop; simpa using hlastdrop
    rw [hy, hym] at hsplit
    simp only [List.cons_append, List.nil_append] at hsplit
    have hta : L.take ρ = b :: c :: rest := by
      have h := hsplit; simp at h; tauto
    have htne : L.take ρ ≠ [] := by rw [hta]; simp
    have hheadtake : (L.take ρ).head? = some n := by
      have h := List.head?_append_of_ne_nil (l₂ := L.drop ρ) (L.take ρ) htne
      rw [hLsplit] at h
      rw [← h]; exact hn
    rw [hta] at hheadtake
    simp at hheadtake
    exact hbn hheadtake
  · -- `L.drop ρ = [a, m]`, so the tip `b` is the last vertex `m` of `L`
    have hlen2 : (L.drop ρ).length = 2 := by omega
    obtain ⟨y, z, hyz⟩ := List.length_eq_two.mp hlen2
    have hzm : z = m := by rw [hyz] at hlastdrop; simpa using hlastdrop
    rw [hyz, hzm] at hsplit
    simp only [List.cons_append, List.nil_append] at hsplit
    have hbm' : b = m := by
      have h := hsplit; simp at h; tauto
    exact hbm hbm'

/-- **Re-inserting the flat vertex.**  With `ρ + 3 ≤ L.length` and
`L.rotate ρ = a :: b :: c :: rest`, the same triple is cyclically consecutive in
`v :: L`, the tail being `rest` with `v` inserted at the seam. -/
lemma flatSeam_insert_rotation (v : ℂ) (L : List ℂ) (ρ : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hρ : ρ + 3 ≤ L.length) (hrot : L.rotate ρ = a :: b :: c :: rest) :
    L.drop ρ = a :: b :: c :: L.drop (ρ + 3) ∧
      rest = L.drop (ρ + 3) ++ L.take ρ ∧
      (v :: L).rotate (ρ + 1) = a :: b :: c :: (L.drop (ρ + 3) ++ v :: L.take ρ) := by
  have hρle : ρ ≤ L.length := by omega
  have hsplit : L.drop ρ ++ L.take ρ = a :: b :: c :: rest := by
    rw [← List.rotate_eq_drop_append_take hρle]; exact hrot
  have hdroplen : 3 ≤ (L.drop ρ).length := by simp; omega
  obtain ⟨x, y, z, tl, hxyz⟩ : ∃ x y z tl, L.drop ρ = x :: y :: z :: tl := by
    rcases hh : L.drop ρ with _ | ⟨x, _ | ⟨y, _ | ⟨z, tl⟩⟩⟩ <;>
      rw [hh] at hdroplen <;> simp at hdroplen
    exact ⟨x, y, z, tl, rfl⟩
  have htl : tl = L.drop (ρ + 3) := by
    have hd : L.drop (ρ + 3) = (L.drop ρ).drop 3 := by rw [List.drop_drop]
    rw [hd, hxyz]; simp
  subst htl
  rw [hxyz] at hsplit
  simp only [List.cons_append] at hsplit
  obtain ⟨hxa, hyb, hzc, hrest⟩ :
      x = a ∧ y = b ∧ z = c ∧ L.drop (ρ + 3) ++ L.take ρ = rest := by
    simp at hsplit; tauto
  subst hxa; subst hyb; subst hzc
  refine ⟨hxyz, hrest.symm, ?_⟩
  rw [flatSeam_rotate_cons_succ v L ρ hρle, hxyz]
  simp

/-! ## 2. The signed area is unchanged by re-inserting the flat vertex -/

/-- A flat triple has vanishing signed area. -/
lemma flatSeam_shoelace2_triple_flat (m v n : ℂ) (s : ℝ)
    (hflat : v - m = (s : ℂ) * (n - m)) :
    HexArea.shoelace2 [m, v, n] = 0 := by
  have hv : v = m + (s : ℂ) * (n - m) := by linear_combination hflat
  rw [hv, shoelace2_triple_eq_cross]
  simp [HexArea.cross, Complex.mul_re, Complex.mul_im]
  ring

/-- **Inserting the flat vertex at the seam does not change the signed area of
the clip.**  The clipped cycle is `a :: c :: (A ++ B)` and the flat vertex `v` is
inserted between `A` and `B`; its cyclic predecessor is `m` (the last entry of
`A`, or `c` when `A = []`) and its cyclic successor is `n` (the head of `B`, or
`a` when `B = []`). -/
lemma flatSeam_shoelace2_insert (a c v m n : ℂ) (A B : List ℂ) (s : ℝ)
    (hflat : v - m = (s : ℂ) * (n - m))
    (hA : A ≠ [] → A.getLast? = some m) (hAe : A = [] → c = m)
    (hB : B ≠ [] → B.head? = some n) (hBe : B = [] → a = n) :
    HexArea.shoelace2 (a :: c :: (A ++ v :: B)) =
      HexArea.shoelace2 (a :: c :: (A ++ B)) := by
  have htri : HexArea.shoelace2 [m, v, n] = 0 :=
    flatSeam_shoelace2_triple_flat m v n s hflat
  by_cases hAnil : A = []
  · subst hAnil
    have hcm : c = m := hAe rfl
    by_cases hBnil : B = []
    · -- the clip is the (degenerate) triangle `[a, c, v]`
      subst hBnil
      have han : a = n := hBe rfl
      rw [hcm, han]
      simp only [List.nil_append, List.append_nil]
      have h1 : HexArea.shoelace2 [n, m, v]
          = HexArea.shoelace2 (([n, m, v] : List ℂ).rotate 1) := by rw [shoelace2_rotate]
      have h2 : HexArea.shoelace2 [n, m]
          = HexArea.shoelace2 (([n, m] : List ℂ).rotate 1) := by rw [shoelace2_rotate]
      have e1 : ([n, m, v] : List ℂ).rotate 1 = [] ++ m :: v :: n :: [] := by
        rw [List.rotate_eq_drop_append_take (by simp)]; simp
      have e2 : ([n, m] : List ℂ).rotate 1 = [] ++ m :: n :: [] := by
        rw [List.rotate_eq_drop_append_take (by simp)]; simp
      rw [h1, h2, e1, e2, shoelace2_insert_mid [] [] m v n, htri, add_zero]
    · obtain ⟨b0, B0, hB0⟩ : ∃ b0 B0, B = b0 :: B0 := by
        cases B with
        | nil => exact absurd rfl hBnil
        | cons b0 B0 => exact ⟨b0, B0, rfl⟩
      have hb0 : b0 = n := by
        have h := hB hBnil; rw [hB0] at h; simpa using h
      rw [hB0, hb0, hcm]
      simp only [List.nil_append]
      have h := shoelace2_insert_mid [a] B0 m v n
      simp only [List.cons_append, List.nil_append] at h
      rw [h, htri, add_zero]
  · obtain ⟨A', hA'⟩ : ∃ A', A = A' ++ [m] := by
      rcases List.eq_nil_or_concat A with h1 | ⟨A', w, hw⟩
      · exact absurd h1 hAnil
      · have hlast := hA hAnil
        rw [show A = A' ++ [w] by simpa using hw] at hlast
        simp at hlast
        exact ⟨A', by rw [show A = A' ++ [w] by simpa using hw, hlast]⟩
    subst hA'
    -- rotate both clips by `2` to expose the seam
    have r1 : HexArea.shoelace2 (a :: c :: (A' ++ [m] ++ v :: B)) =
        HexArea.shoelace2 (A' ++ m :: v :: (B ++ [a, c])) := by
      have h : (a :: c :: (A' ++ [m] ++ v :: B)).rotate 2 = A' ++ m :: v :: (B ++ [a, c]) := by
        rw [List.rotate_eq_drop_append_take (by simp)]; simp
      rw [← shoelace2_rotate _ 2, h]
    have r2 : HexArea.shoelace2 (a :: c :: (A' ++ [m] ++ B)) =
        HexArea.shoelace2 (A' ++ m :: (B ++ [a, c])) := by
      have h : (a :: c :: (A' ++ [m] ++ B)).rotate 2 = A' ++ m :: (B ++ [a, c]) := by
        rw [List.rotate_eq_drop_append_take (by simp)]; simp
      rw [← shoelace2_rotate _ 2, h]
    rw [r1, r2]
    obtain ⟨suf, hsuf⟩ : ∃ suf, B ++ [a, c] = n :: suf := by
      by_cases hBnil : B = []
      · subst hBnil; exact ⟨[c], by simp [hBe rfl]⟩
      · obtain ⟨b0, B0, hB0⟩ : ∃ b0 B0, B = b0 :: B0 := by
          cases B with
          | nil => exact absurd rfl hBnil
          | cons b0 B0 => exact ⟨b0, B0, rfl⟩
        have hb0 : b0 = n := by
          have h := hB hBnil; rw [hB0] at h; simpa using h
        exact ⟨B0 ++ [a, c], by rw [hB0, hb0]; simp⟩
    rw [hsuf, shoelace2_insert_mid A' suf m v n, htri, add_zero]

/-! ## 3. The geometric input -/

/-- **The flat seam vertex avoids the ear of the deletion.**

Let `v :: L` be a simple closed polygon whose head `v` is a *flat* vertex — `v`
lies strictly between its cyclic neighbours `m = L.getLast` and `n = L.head` —
and let the deletion `L` be simple and cyclically non-degenerate.  Let `a, b, c`
be a cyclically consecutive triple of `L` whose tip `b` is neither `m` nor `n`,
whose corner triangle contains no vertex of `L` in its strict interior and whose
diagonal `[a, c]` carries no vertex of `L`.  Then the deleted vertex `v` also
avoids that triangle and that diagonal.

This is the ear-clearance property: `v` lies in the *open* segment of the cyclic
edge `(m, n)` of `L` (that edge is the seam left behind by the deletion), and by
`ear_edge_interior_not_strict` / `ear_edge_interior_not_base`
(`RequestProject.SAWUmlaufTriangleClosed`) the open segment of an edge of `L`
other than the two ear sides misses both the strict interior and the base of the
ear triangle. -/
lemma flatSeam_avoids_ear (v : ℂ) (L : List ℂ) (m n : ℂ) (s : ℝ)
    (h4 : 4 ≤ L.length)
    (hn : L.head? = some n) (hm : L.getLast? = some m)
    (hLsimple : PolygonSimple L) (hLnd : polyCycNondeg L)
    (hs0 : 0 < s) (hs1 : s < 1) (hflat : v - m = (s : ℂ) * (n - m))
    (ρ : ℕ) (a b c : ℂ) (rest : List ℂ) (hrot : L.rotate ρ = a :: b :: c :: rest)
    (hbm : b ≠ m) (hbn : b ≠ n)
    (hempty : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (hdiag : ∀ x ∈ rest, x ∉ segment ℝ a c) :
    ¬ HexArea.inTriangleStrict a b c v ∧ v ∉ segment ℝ a c := by
  -- the seam `(m, n)` is a cyclic edge of `L`, and `v` lies in its interior
  have hedge : (m, n) ∈ closedEdges L := by
    rw [HexArea.closedEdges_eq_pathEdges L n m hn hm]
    simp
  have hvopen : v ∈ openSegment ℝ m n := by
    refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    linear_combination -hflat
  refine ⟨ear_edge_interior_not_strict L h4 hLsimple hLnd ρ a b c rest hrot hempty hdiag
      m n hedge hbm hbn v hvopen,
    ear_edge_interior_not_base L h4 hLsimple hLnd ρ a b c rest hrot hempty hdiag
      m n hedge hbm hbn v hvopen⟩

/-! ## 4. The quadrilateral base case -/

/-- Two positive multiples of the same real number are simultaneously positive. -/
lemma flatSeam_pos_iff (t1 t2 K : ℝ) (h1 : 0 < t1) (h2 : 0 < t2) :
    (0 < t1 * K ↔ 0 < t2 * K) := by
  rw [mul_pos_iff_of_pos_left h1, mul_pos_iff_of_pos_left h2]

/-- **A quadrilateral with a flat vertex has an ear at each neighbour of it.**
If `[v, n, x, m]` is a simple quadrilateral in which `v` lies strictly between
its neighbours `m` and `n`, then both `n` and `m` are ears in the sense of
`EmptyCornerData2`.  (The fourth vertex `x` is *not* an ear: the flat vertex `v`
lies on its diagonal `[n, m]`.  This is why the quadrilateral base case of the
flat-seam lift has to be done by hand.)

Since the two ears have tips `n` and `m`, an ear avoiding any prescribed one of
them — which is what the Meisters recursion needs — is always available. -/
lemma flatSeam_quad_ear (v n x m : ℂ) (s : ℝ)
    (hsimple : PolygonSimple [v, n, x, m])
    (hs0 : 0 < s) (hs1 : s < 1) (hflat : v - m = (s : ℂ) * (n - m)) :
    EmptyCornerData2 [v, n, x, m] v m ∧ EmptyCornerData2 [v, n, x, m] v n := by
  have hv : v = m + (s : ℂ) * (n - m) := by linear_combination hflat
  have hnd : ([v, n, x, m] : List ℂ).Nodup := hsimple.1
  have hvn : v ≠ n := by simp at hnd; tauto
  have hvm : v ≠ m := by simp at hnd; tauto
  have hnm : n ≠ m := by simp at hnd; tauto
  have hmn : n - m ≠ 0 := sub_ne_zero.mpr hnm
  have hs1' : 0 < 1 - s := by linarith
  -- the fourth vertex is off the line of the flat edge
  have hK : HexArea.cross (n - m) (x - m) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := exists_real_of_cross_zero (n - m) (x - m) hmn h
    refine not_collinear_of_simple [v, n, x, m] (by simp) hsimple m (n - m) hmn ?_
    intro y hy
    simp at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨s, hv⟩
    · exact ⟨1, by push_cast; ring⟩
    · exact ⟨t, by linear_combination ht⟩
    · exact ⟨0, by push_cast; ring⟩
  have e1 : HexArea.shoelace2 [v, n, x] = (1 - s) * HexArea.cross (n - m) (x - m) := by
    rw [hv, shoelace2_triple_eq_cross]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have e2 : HexArea.shoelace2 [v, x, m] = s * HexArea.cross (n - m) (x - m) := by
    rw [hv, shoelace2_triple_eq_cross]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have e3 : HexArea.shoelace2 [x, m, v] = s * HexArea.cross (n - m) (x - m) := by
    rw [hv, shoelace2_triple_eq_cross]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have e4 : HexArea.shoelace2 [x, v, n] = (1 - s) * HexArea.cross (n - m) (x - m) := by
    rw [hv, shoelace2_triple_eq_cross]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c1 : HexArea.cross (n - v) (m - v) = 0 := by
    rw [hv]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c2 : HexArea.cross (v - m) (n - m) = 0 := by
    rw [hv]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c3 : HexArea.cross (x - v) (m - v) = s * HexArea.cross (n - m) (x - m) := by
    rw [hv]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c4 : HexArea.cross (v - x) (n - x) = (1 - s) * HexArea.cross (n - m) (x - m) := by
    rw [hv]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have hrot0 : ([v, n, x, m] : List ℂ).rotate 0 = v :: n :: x :: [m] := by simp
  have hrot2 : ([v, n, x, m] : List ℂ).rotate 2 = x :: m :: v :: [n] := by
    rw [List.rotate_eq_drop_append_take (by simp)]; simp
  constructor
  · -- the ear at `n`
    refine ⟨0, v, n, x, m, m, [m], hrot0, hvn.symm, hnm, by simp, by simp, ?_, ?_, ?_⟩
    · intro y hy hin
      have hym : y = m := by simpa using hy
      rw [hym] at hin
      rcases hin with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> rw [c1] at h1 <;> simp at h1
    · intro y hy hmem
      have hym : y = m := by simpa using hy
      rw [hym] at hmem
      have hz := HexArea.cross_eq_zero_of_mem_segment v x m hmem
      rw [c3] at hz
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (ne_of_gt hs0)
      · exact hK h
    · rw [e1, e2]; exact flatSeam_pos_iff _ _ _ hs1' hs0
  · -- the ear at `m`
    refine ⟨2, x, m, v, n, n, [n], hrot2, hvm.symm, hnm.symm, by simp, by simp, ?_, ?_, ?_⟩
    · intro y hy hin
      have hyn : y = n := by simpa using hy
      rw [hyn] at hin
      rcases hin with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> rw [c2] at h2 <;> simp at h2
    · intro y hy hmem
      have hyn : y = n := by simpa using hy
      rw [hyn] at hmem
      have hz := HexArea.cross_eq_zero_of_mem_segment x v n hmem
      rw [c4] at hz
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (ne_of_gt hs1')
      · exact hK h
    · rw [e3, e4]; exact flatSeam_pos_iff _ _ _ hs0 hs1'

/-- **Deleting the flat head vertex preserves simplicity.**  Rotate the flat
vertex into second position and apply `PolygonSimple_remove_flat_second`. -/
lemma flatSeam_delete_simple (v : ℂ) (L : List ℂ) (m n : ℂ) (h2 : 2 ≤ L.length)
    (hn : L.head? = some n) (hm : L.getLast? = some m)
    (hsimple : PolygonSimple (v :: L)) (hseg : v ∈ segment ℝ m n) :
    PolygonSimple L := by
  obtain ⟨t, ht⟩ : ∃ t, L = n :: t := by
    cases L with
    | nil => simp at hn
    | cons a t => refine ⟨t, ?_⟩; simp at hn; rw [hn]
  have htne : t ≠ [] := by
    intro h; rw [ht, h] at h2; simp at h2
  obtain ⟨mid, hmid⟩ : ∃ mid, t = mid ++ [m] := by
    rcases List.eq_nil_or_concat t with h | ⟨mid, w, hw⟩
    · exact absurd h htne
    · have hw' : t = mid ++ [w] := by simpa using hw
      have hlast : L.getLast? = some w := by
        rw [ht, hw']
        have := List.getLast?_append_of_ne_nil (l₁ := n :: mid) (l₂ := [w]) (by simp)
        simpa using this
      rw [hm] at hlast
      exact ⟨mid, by rw [hw', Option.some.inj hlast]⟩
  subst ht; subst hmid
  have hX : PolygonSimple (m :: v :: n :: mid) := by
    have h := (PolygonSimple_rotate (v :: n :: (mid ++ [m])) (mid.length + 2)).mpr hsimple
    rwa [show (v :: n :: (mid ++ [m])).rotate (mid.length + 2) = m :: v :: n :: mid by
      rw [List.rotate_eq_drop_append_take (by simp)]; simp] at h
  have hY : PolygonSimple (m :: n :: mid) := PolygonSimple_remove_flat_second m v n mid hX hseg
  have hR := (PolygonSimple_rotate (n :: (mid ++ [m])) (mid.length + 1))
  rw [show (n :: (mid ++ [m])).rotate (mid.length + 1) = m :: n :: mid by
      rw [List.rotate_eq_drop_append_take (by simp)]; simp] at hR
  exact hR.mp hY

/-! ## 5. The lift -/

/-- **The flat-seam ear lift.**  Let `v :: L` be a simple closed polygon whose
head `v` is flat between its cyclic neighbours `m = L.getLast`, `n = L.head`, let
the deletion `L` be cyclically non-degenerate, and let `u` be one of the two
neighbours of `v`.  If `L` carries an ear avoiding the seam edge `{m, n}`, then
`v :: L` carries an ear avoiding `v` and `u`.

The tip of the produced ear is the tip of the given ear of `L`; its tail is the
tail of that ear with `v` re-inserted at the seam.  The quadrilateral case
`L.length = 3`, where no ear of `L` is available, is handled separately by
`flatSeam_quad_ear`. -/
theorem flatSeam_ear_lift (v : ℂ) (L : List ℂ) (m n u : ℂ) (s : ℝ)
    (h3 : 3 ≤ L.length)
    (hn : L.head? = some n) (hm : L.getLast? = some m)
    (hsimple : PolygonSimple (v :: L)) (hLnd : polyCycNondeg L)
    (hs0 : 0 < s) (hs1 : s < 1) (hflat : v - m = (s : ℂ) * (n - m))
    (hu : u = m ∨ u = n)
    (hdata : 4 ≤ L.length → EmptyCornerData2 L m n)
    (z1 z2 : ℂ) (hz1 : z1 = v ∨ z1 = u) (hz2 : z2 = v ∨ z2 = u) :
    EmptyCornerData2 (v :: L) z1 z2 := by
  have hvL : v ∉ L := by
    have h := hsimple.1; rw [List.nodup_cons] at h; exact h.1
  rcases Nat.lt_or_ge L.length 4 with hlt | hge
  · -- the quadrilateral base case
    have h3' : L.length = 3 := by omega
    obtain ⟨n0, x0, m0, hL3⟩ : ∃ n0 x0 m0, L = [n0, x0, m0] :=
      List.length_eq_three.mp h3'
    have hn0 : n0 = n := by rw [hL3] at hn; simpa using hn
    have hm0 : m0 = m := by rw [hL3] at hm; simpa using hm
    rw [hL3, hn0, hm0] at hsimple ⊢
    obtain ⟨hearm, hearn⟩ := flatSeam_quad_ear v n x0 m s hsimple hs0 hs1 hflat
    rcases hu with rfl | rfl
    · obtain ⟨r, a', b', c', p', q', rest', hrot, hb1, hb2, hp, hq, he, hd, ho⟩ := hearm
      exact ⟨r, a', b', c', p', q', rest', hrot,
        (by rcases hz1 with rfl | rfl <;> assumption),
        (by rcases hz2 with rfl | rfl <;> assumption), hp, hq, he, hd, ho⟩
    · obtain ⟨r, a', b', c', p', q', rest', hrot, hb1, hb2, hp, hq, he, hd, ho⟩ := hearn
      exact ⟨r, a', b', c', p', q', rest', hrot,
        (by rcases hz1 with rfl | rfl <;> assumption),
        (by rcases hz2 with rfl | rfl <;> assumption), hp, hq, he, hd, ho⟩
  -- the generic case: recurse on the deletion and lift
  obtain ⟨r, a, b, c, p, q, rest, hrot, hbm, hbn, hp, hq, hempty, hdiag, horient⟩ :=
    hdata hge
  obtain ⟨ρ, hρ, hrotρ⟩ := flatSeam_ear_index L m n hn hm r a b c rest hrot hbn hbm
  obtain ⟨hdrop, hrest, hrotM⟩ := flatSeam_insert_rotation v L ρ a b c rest hρ hrotρ
  -- the new tail: `rest` with `v` re-inserted at the seam
  obtain ⟨p', hp'⟩ : ∃ y, (L.drop (ρ + 3) ++ v :: L.take ρ).getLast? = some y := by
    cases hcase : (L.drop (ρ + 3) ++ v :: L.take ρ).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hcase) (by simp)
    | some y => exact ⟨y, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ y, (L.drop (ρ + 3) ++ v :: L.take ρ).head? = some y := by
    cases hcase : (L.drop (ρ + 3) ++ v :: L.take ρ).head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hcase) (by simp)
    | some y => exact ⟨y, rfl⟩
  have hLsimple : PolygonSimple L :=
    flatSeam_delete_simple v L m n (by omega) hn hm hsimple
      (mem_segment_of_param m n s (le_of_lt hs0) (le_of_lt hs1) v hflat)
  have hgeo := flatSeam_avoids_ear v L m n s hge hn hm hLsimple hLnd hs0 hs1 hflat
    ρ a b c rest hrotρ hbm hbn hempty hdiag
  have hmem : ∀ y, y ∈ (L.drop (ρ + 3) ++ v :: L.take ρ) → y = v ∨ y ∈ rest := by
    intro y hy
    simp at hy
    rw [hrest]
    simp
    tauto
  have hbv : b ≠ v := by
    intro h
    exact hvL (h ▸ (List.mem_rotate (n := ρ)).mp (by rw [hrotρ]; simp))
  refine ⟨ρ + 1, a, b, c, p', q', _, hrotM, ?_, ?_, hp', hq', ?_, ?_, ?_⟩
  · rcases hz1 with rfl | rfl
    · exact hbv
    · rcases hu with rfl | rfl <;> assumption
  · rcases hz2 with rfl | rfl
    · exact hbv
    · rcases hu with rfl | rfl <;> assumption
  · intro y hy
    rcases hmem y hy with rfl | hy'
    · exact hgeo.1
    · exact hempty y hy'
  · intro y hy
    rcases hmem y hy with rfl | hy'
    · exact hgeo.2
    · exact hdiag y hy'
  · -- the orientation clause survives: the clip has the same signed area
    have hshoe : HexArea.shoelace2 (a :: c :: (L.drop (ρ + 3) ++ v :: L.take ρ))
        = HexArea.shoelace2 (a :: c :: rest) := by
      rw [hrest]
      refine flatSeam_shoelace2_insert a c v m n (L.drop (ρ + 3)) (L.take ρ) s hflat ?_ ?_ ?_ ?_
      · intro hAne
        have h := List.getLast?_append_of_ne_nil (L.take (ρ + 3)) (l₂ := L.drop (ρ + 3)) hAne
        rw [List.take_append_drop] at h
        rw [← h]; exact hm
      · intro hAnil
        -- `L.drop (ρ + 3) = []` makes `c` the last vertex of `L`
        have hdrop3 : L.drop ρ = [a, b, c] := by rw [hdrop, hAnil]
        have h := List.getLast?_append_of_ne_nil (L.take ρ) (l₂ := L.drop ρ)
          (by rw [hdrop3]; simp)
        rw [List.take_append_drop, hdrop3] at h
        rw [hm] at h
        simp at h
        exact h.symm
      · intro hBne
        have h := List.head?_append_of_ne_nil (l₂ := L.drop ρ) (L.take ρ) hBne
        rw [List.take_append_drop] at h
        rw [← h]; exact hn
      · intro hBnil
        have hρ0 : ρ = 0 := by
          by_contra hcon
          have h0 : (L.take ρ).length = 0 := by rw [hBnil]; rfl
          rw [List.length_take] at h0
          omega
        have hLeq : L = a :: b :: c :: L.drop (ρ + 3) := by
          rw [← hdrop, hρ0]; simp
        rw [hLeq] at hn
        simp at hn
        exact hn
    rw [hshoe]
    exact horient

/-! ## 6. Packaging: the flat-seam data of a degenerate recursion piece -/

/-- The Meisters ear package is invariant under cyclic rotation. -/
lemma EmptyCornerData2_rotate (P : List ℂ) (t : ℕ) (z1 z2 : ℂ)
    (h : EmptyCornerData2 (P.rotate t) z1 z2) : EmptyCornerData2 P z1 z2 := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, h1, h2, hp, hq, he, hd, ho⟩ := h
  exact ⟨t + r, a, b, c, p, q, rest, by rw [← List.rotate_rotate]; exact hrot,
    h1, h2, hp, hq, he, hd, ho⟩

/-- **The flat-seam data of a recursion piece.**  `FlatSeamData P u v` says that
the cycle `P` is flat at one of the two prescribed vertices `u`, `v` — the two
endpoints of the cut edge, in the application — that the *other* one is a cyclic
neighbour of it, and that deleting the flat vertex leaves a cyclically
non-degenerate cycle.  This is exactly the input the flat-seam lift consumes. -/
def FlatSeamData (P : List ℂ) (u v : ℂ) : Prop :=
  ∃ (t : ℕ) (M : List ℂ) (f w mm nn : ℂ) (σ : ℝ),
    ((f = u ∧ w = v) ∨ (f = v ∧ w = u)) ∧
    P.rotate t = f :: M ∧ M.head? = some nn ∧ M.getLast? = some mm ∧
    (w = mm ∨ w = nn) ∧ 0 < σ ∧ σ < 1 ∧ f - mm = (σ : ℂ) * (nn - mm) ∧
    polyCycNondeg M

/-- **The flat-seam recursion step.**  A simple cycle `P` with flat-seam data at
`{u, v}` carries a Meisters ear avoiding both `u` and `v`, given the induction
hypothesis for strictly shorter non-degenerate simple cycles.  The recursion is
run on the deletion `M`, forbidding its seam edge `{mm, nn}`; the returned ear is
lifted back over the deleted vertex by `flatSeam_ear_lift`. -/
lemma flatSeam_EmptyCornerData2_of_data (P : List ℂ) (hPsimple : PolygonSimple P)
    (h4 : 4 ≤ P.length) (u v : ℂ) (hdata : FlatSeamData P u v)
    (IH : ∀ M : List ℂ, M.length < P.length → 4 ≤ M.length → PolygonSimple M →
       polyCycNondeg M → ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge M w1 w2) →
       EmptyCornerData2 M w1 w2) :
    EmptyCornerData2 P u v := by
  obtain ⟨t, M, f, w, mm, nn, σ, hfw, hrotP, hMhead, hMlast, hwmn, hσ0, hσ1, hflat, hMnd⟩ :=
    hdata
  have hlen : M.length + 1 = P.length := by
    have h := congrArg List.length hrotP; simp at h; omega
  have h3 : 3 ≤ M.length := by omega
  have hfM : PolygonSimple (f :: M) := by
    rw [← hrotP]; exact (PolygonSimple_rotate P t).mpr hPsimple
  have hseg : f ∈ segment ℝ mm nn :=
    mem_segment_of_param mm nn σ (le_of_lt hσ0) (le_of_lt hσ1) f hflat
  have hMsimple : PolygonSimple M :=
    flatSeam_delete_simple f M mm nn (by omega) hMhead hMlast hfM hseg
  have hedge : IsCycEdge M mm nn := by
    refine Or.inl ?_
    rw [HexArea.closedEdges_eq_pathEdges M nn mm hMhead hMlast]
    simp
  have hdataM : 4 ≤ M.length → EmptyCornerData2 M mm nn :=
    fun h => IH M (by omega) h hMsimple hMnd mm nn (Or.inr hedge)
  have hz1 : u = f ∨ u = w := by
    rcases hfw with ⟨h1, h2⟩ | ⟨h1, h2⟩; exacts [Or.inl h1.symm, Or.inr h2.symm]
  have hz2 : v = f ∨ v = w := by
    rcases hfw with ⟨h1, h2⟩ | ⟨h1, h2⟩; exacts [Or.inr h2.symm, Or.inl h1.symm]
  have hres := flatSeam_ear_lift f M mm nn w σ h3 hMhead hMlast hfM hMnd hσ0 hσ1 hflat
    hwmn hdataM u v hz1 hz2
  rw [← hrotP] at hres
  exact EmptyCornerData2_rotate P t u v hres

/-! ## 7. The flat-seam data of an interior-split piece -/

/-- **The flat-seam data of the LEFT interior-split piece.**  If the `chordLeft`
piece of the interior cut `W[0]–W[k]` (with `W = b :: c :: rest ++ [a]`) has at
least four vertices but fails to be cyclically non-degenerate, then its seam
corner at the cut endpoint `w` is the degenerate one — the corner at the apex `b`
is `(w, b, c)`, non-flat because `w` lies strictly inside the triangle `a, b, c` —
so by `flat_between_of_cross_zero` the vertex `w` lies strictly between its two
neighbours `prev` and `b` in the piece.  Deleting it leaves `chordLeft W (k-1)`,
whose two seam corners are non-flat by `cross_pred_corner_remove_flat` /
`cross_succ_corner_remove_flat`.  Hence the piece carries `FlatSeamData P b w`. -/
lemma interior_flat_seam_data_left (a b c w : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (hPsimple : PolygonSimple (HexArea.chordLeft (b :: c :: rest ++ [a]) k))
    (hP4 : 4 ≤ (HexArea.chordLeft (b :: c :: rest ++ [a]) k).length)
    (hPdeg : ¬ polyCycNondeg (HexArea.chordLeft (b :: c :: rest ++ [a]) k)) :
    FlatSeamData (HexArea.chordLeft (b :: c :: rest ++ [a]) k) b w := by
  have hWlen : (b :: c :: rest ++ [a]).length = rest.length + 3 := by simp
  have hPlen : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).length = k + 1 :=
    HexArea.chordLeft_length _ k (by omega)
  have hk3 : 3 ≤ k := by rw [hPlen] at hP4; omega
  have hWnd : polyCycNondeg (b :: c :: rest ++ [a]) := by
    have h1 : (a :: b :: c :: rest).rotate 1 = b :: c :: rest ++ [a] := by
      rw [HexArea.rotate_one_cons]
    rw [← h1]
    exact (polyCycNondeg_rotate1 (a :: b :: c :: rest) (by simp)).mpr hnd
  have hk1lt : k - 1 < (b :: c :: rest ++ [a]).length := by omega
  have hk2lt : k - 2 < (b :: c :: rest ++ [a]).length := by omega
  have hklt : k < (b :: c :: rest ++ [a]).length := by omega
  set prev : ℂ := (b :: c :: rest ++ [a])[k-1]'hk1lt with hprevdef
  set prev2 : ℂ := (b :: c :: rest ++ [a])[k-2]'hk2lt with hprev2def
  have hprev : (b :: c :: rest ++ [a])[k-1]? = some prev := by
    rw [hprevdef, List.getElem?_eq_getElem hk1lt]
  have hprev2 : (b :: c :: rest ++ [a])[k-2]? = some prev2 := by
    rw [hprev2def, List.getElem?_eq_getElem hk2lt]
  have hwW : (b :: c :: rest ++ [a])[k]'hklt = w := by
    have h := List.getElem?_eq_getElem hklt; rw [hwk] at h; exact (Option.some.inj h).symm
  -- the seam corner of the piece at `w` is the degenerate one
  have hzero : HexArea.cross (w - prev) (b - w) = 0 := by
    by_contra h
    exact hPdeg (interior_split_nondeg_left a b c w prev rest k hnd hwin hk2 hk hwk hprev h)
  have hdrop1 : (b :: c :: rest ++ [a]).drop (k-1) = prev :: (b :: c :: rest ++ [a]).drop k := by
    have h := List.drop_eq_getElem_cons (l := b :: c :: rest ++ [a]) (i := k-1) hk1lt
    rw [show k - 1 + 1 = k by omega] at h
    exact h
  have hdrop2 : (b :: c :: rest ++ [a]).drop k = w :: (b :: c :: rest ++ [a]).drop (k+1) := by
    have h := List.drop_eq_getElem_cons (l := b :: c :: rest ++ [a]) (i := k) hklt
    rw [hwW] at h; exact h
  have htake : (b :: c :: rest ++ [a]).take (k-1) = b :: c :: ((rest ++ [a]).take (k-3)) := by
    rw [show k - 1 = (k-3) + 2 by omega]
    simp
  -- the rotation of the piece exhibiting the degenerate corner in the middle
  have hProt : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).rotate (k-1)
      = prev :: w :: b :: c :: ((rest ++ [a]).take (k-3)) := by
    rw [List.rotate_eq_drop_append_take (by rw [hPlen]; omega)]
    have hd : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).drop (k-1) = [prev, w] := by
      rw [HexArea.chordLeft, List.drop_take, hdrop1, hdrop2,
        show k + 1 - (k-1) = 2 by omega]
      simp
    have ht : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).take (k-1)
        = (b :: c :: rest ++ [a]).take (k-1) := by
      rw [HexArea.chordLeft, List.take_take]
      congr 1
      omega
    rw [hd, ht, htake]
    simp
  have hRotSimple : PolygonSimple (prev :: w :: b :: c :: ((rest ++ [a]).take (k-3))) := by
    rw [← hProt]
    exact (PolygonSimple_rotate _ _).mpr hPsimple
  -- the degenerate corner of a simple polygon is flat
  obtain ⟨σ, hσ0, hσ1, hσ⟩ :=
    flat_between_of_cross_zero prev w b (c :: ((rest ++ [a]).take (k-3))) (by simp)
      hRotSimple hzero
  -- the deletion is `chordLeft W (k-1) = W.take k`
  have hProtk : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).rotate k
      = w :: (b :: c :: rest ++ [a]).take k := by
    rw [List.rotate_eq_drop_append_take (by rw [hPlen]; omega)]
    have hd : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).drop k = [w] := by
      rw [HexArea.chordLeft, List.drop_take, hdrop2, show k + 1 - k = 1 by omega]
      simp
    have ht : (HexArea.chordLeft (b :: c :: rest ++ [a]) k).take k
        = (b :: c :: rest ++ [a]).take k := by
      rw [HexArea.chordLeft, List.take_take]
      congr 1
      omega
    rw [hd, ht]
    simp
  have hMhead : ((b :: c :: rest ++ [a]).take k).head? = some b := by
    rw [show k = (k-1) + 1 by omega]
    simp
  have hMlast : ((b :: c :: rest ++ [a]).take k).getLast? = some prev := by
    rw [show k = (k-1) + 1 by omega, List.take_add_one, hprev]
    simp
  have hseg : w ∈ segment ℝ prev b :=
    mem_segment_of_param prev b σ (le_of_lt hσ0) (le_of_lt hσ1) w hσ
  -- the two seam corners of the deletion are non-flat
  have hcorner : HexArea.cross (prev - prev2) (w - prev) ≠ 0 :=
    polyCycNondeg_interior_corner (b :: c :: rest ++ [a]) (k-1) prev2 prev w hWnd (by omega)
      (by omega) (by rw [show k - 1 - 1 = k - 2 by omega]; exact hprev2) hprev
      (by rw [show k - 1 + 1 = k by omega]; exact hwk)
  have hseam1 : HexArea.cross (prev - prev2) (b - prev) ≠ 0 :=
    cross_pred_corner_remove_flat prev2 prev b w hseg hcorner
  have hwbc : HexArea.cross (c - b) (w - b) ≠ 0 := by
    rcases hwin with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
    · exact ne_of_gt h2
    · exact ne_of_lt h2
  have hbw : HexArea.cross (b - w) (c - b) ≠ 0 := by
    have hEq : HexArea.cross (b - w) (c - b) = HexArea.cross (c - b) (w - b) := by
      simp [HexArea.cross]; ring
    rw [hEq]; exact hwbc
  have hseam2 : HexArea.cross (b - prev) (c - b) ≠ 0 :=
    cross_succ_corner_remove_flat c prev b w hseg hbw
  have hMnd : polyCycNondeg ((b :: c :: rest ++ [a]).take k) := by
    rw [show (b :: c :: rest ++ [a]).take k = HexArea.chordLeft (b :: c :: rest ++ [a]) (k-1) by
      rw [HexArea.chordLeft, show k - 1 + 1 = k by omega]]
    exact HexArea.chordLeft_polyCycNondeg (b :: c :: rest ++ [a]) (k-1) b c prev prev2
      (by omega) (by omega) hWnd (by simp) (by simp) hprev
      (by rw [show k - 1 - 1 = k - 2 by omega]; exact hprev2) hseam1 hseam2
  exact ⟨k, (b :: c :: rest ++ [a]).take k, w, b, prev, b, σ, Or.inr ⟨rfl, rfl⟩, hProtk,
    hMhead, hMlast, Or.inr rfl, hσ0, hσ1, hσ, hMnd⟩

/-- **The flat-seam data of the RIGHT interior-split piece.**  Mirror image of
`interior_flat_seam_data_left`: a degenerate `chordRight` piece is flat at the cut
endpoint `w` (its seam corner there is `(b, w, succ)`), and deleting `w` leaves
`chordRight W (k+1)`, whose two seam corners are non-flat by
`cross_pred_corner_remove_flat` / `cross_succ_corner_remove_flat`. -/
lemma interior_flat_seam_data_right (a b c w : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (hPsimple : PolygonSimple (HexArea.chordRight (b :: c :: rest ++ [a]) k))
    (hP4 : 4 ≤ (HexArea.chordRight (b :: c :: rest ++ [a]) k).length)
    (hPdeg : ¬ polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) k)) :
    FlatSeamData (HexArea.chordRight (b :: c :: rest ++ [a]) k) b w := by
  have hWlen : (b :: c :: rest ++ [a]).length = rest.length + 3 := by simp
  have hPlen : (HexArea.chordRight (b :: c :: rest ++ [a]) k).length
      = (b :: c :: rest ++ [a]).length - k + 1 :=
    HexArea.chordRight_length _ k (by omega)
  have hk3 : k + 3 ≤ (b :: c :: rest ++ [a]).length := by omega
  have hWnd : polyCycNondeg (b :: c :: rest ++ [a]) := by
    have h1 : (a :: b :: c :: rest).rotate 1 = b :: c :: rest ++ [a] := by
      rw [HexArea.rotate_one_cons]
    rw [← h1]
    exact (polyCycNondeg_rotate1 (a :: b :: c :: rest) (by simp)).mpr hnd
  have hklt : k < (b :: c :: rest ++ [a]).length := by omega
  have hk1lt : k + 1 < (b :: c :: rest ++ [a]).length := by omega
  have hk2lt : k + 2 < (b :: c :: rest ++ [a]).length := by omega
  set succ : ℂ := (b :: c :: rest ++ [a])[k+1]'hk1lt with hsuccdef
  set succ2 : ℂ := (b :: c :: rest ++ [a])[k+2]'hk2lt with hsucc2def
  have hsucc : (b :: c :: rest ++ [a])[k+1]? = some succ := by
    rw [hsuccdef, List.getElem?_eq_getElem hk1lt]
  have hsucc2 : (b :: c :: rest ++ [a])[k+2]? = some succ2 := by
    rw [hsucc2def, List.getElem?_eq_getElem hk2lt]
  have hwW : (b :: c :: rest ++ [a])[k]'hklt = w := by
    have h := List.getElem?_eq_getElem hklt; rw [hwk] at h; exact (Option.some.inj h).symm
  have hzero : HexArea.cross (w - b) (succ - w) = 0 := by
    by_contra h
    exact hPdeg (interior_split_nondeg_right a b c w succ rest k hnd hwin hk2 hk hwk hsucc h)
  have hdropk : (b :: c :: rest ++ [a]).drop k
      = w :: succ :: (b :: c :: rest ++ [a]).drop (k+2) := by
    have h1 := List.drop_eq_getElem_cons (l := b :: c :: rest ++ [a]) (i := k) hklt
    have h2 := List.drop_eq_getElem_cons (l := b :: c :: rest ++ [a]) (i := k+1) hk1lt
    rw [hwW] at h1
    rw [h1, h2, ← hsuccdef]
  have hPeq : HexArea.chordRight (b :: c :: rest ++ [a]) k
      = (b :: c :: rest ++ [a]).drop k ++ [b] := by
    rw [HexArea.chordRight]; simp
  have hProt : (HexArea.chordRight (b :: c :: rest ++ [a]) k).rotate
        (((b :: c :: rest ++ [a]).drop k).length)
      = b :: w :: succ :: (b :: c :: rest ++ [a]).drop (k+2) := by
    rw [hPeq, List.rotate_eq_drop_append_take (by simp), List.drop_left, List.take_left,
      ← hdropk]
    simp
  have hRotSimple : PolygonSimple (b :: w :: succ :: (b :: c :: rest ++ [a]).drop (k+2)) := by
    rw [← hProt]
    exact (PolygonSimple_rotate _ _).mpr hPsimple
  have hdropne : (b :: c :: rest ++ [a]).drop (k+2) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  obtain ⟨σ, hσ0, hσ1, hσ⟩ :=
    flat_between_of_cross_zero b w succ ((b :: c :: rest ++ [a]).drop (k+2)) hdropne
      hRotSimple hzero
  have hMeq : HexArea.chordRight (b :: c :: rest ++ [a]) (k+1)
      = (b :: c :: rest ++ [a]).drop (k+1) ++ [b] := by
    rw [HexArea.chordRight]; simp
  have hProt0 : (HexArea.chordRight (b :: c :: rest ++ [a]) k).rotate 0
      = w :: HexArea.chordRight (b :: c :: rest ++ [a]) (k+1) := by
    rw [List.rotate_zero, hPeq, hMeq,
      List.drop_eq_getElem_cons (l := b :: c :: rest ++ [a]) (i := k) hklt, hwW]
    simp
  have hMhead : (HexArea.chordRight (b :: c :: rest ++ [a]) (k+1)).head? = some succ := by
    rw [hMeq, List.drop_eq_getElem_cons (l := b :: c :: rest ++ [a]) (i := k+1) hk1lt,
      ← hsuccdef]
    simp
  have hMlast : (HexArea.chordRight (b :: c :: rest ++ [a]) (k+1)).getLast? = some b := by
    rw [hMeq]
    exact List.getLast?_append_of_ne_nil _ (by simp)
  have hseg : w ∈ segment ℝ b succ :=
    mem_segment_of_param b succ σ (le_of_lt hσ0) (le_of_lt hσ1) w hσ
  have hwab : HexArea.cross (b - a) (w - a) ≠ 0 := by
    rcases hwin with ⟨h1, _, _⟩ | ⟨h1, _, _⟩
    · exact ne_of_gt h1
    · exact ne_of_lt h1
  have hbaw : HexArea.cross (b - a) (w - b) ≠ 0 := by
    have hEq : HexArea.cross (b - a) (w - b) = HexArea.cross (b - a) (w - a) := by
      simp [HexArea.cross]; ring
    rw [hEq]; exact hwab
  have hseam1 : HexArea.cross (b - a) (succ - b) ≠ 0 :=
    cross_pred_corner_remove_flat a b succ w hseg hbaw
  have hcorner : HexArea.cross (succ - w) (succ2 - succ) ≠ 0 :=
    polyCycNondeg_interior_corner (b :: c :: rest ++ [a]) (k+1) w succ succ2 hWnd (by omega)
      (by omega) (by rw [show k + 1 - 1 = k by omega]; exact hwk) hsucc hsucc2
  have hseam2 : HexArea.cross (succ - b) (succ2 - succ) ≠ 0 :=
    cross_succ_corner_remove_flat succ2 b succ w hseg hcorner
  have hlastW : (b :: c :: rest ++ [a])[(b :: c :: rest ++ [a]).length - 1]? = some a := by
    rw [← List.getLast?_eq_getElem?,
      show b :: c :: rest ++ [a] = (b :: c :: rest) ++ [a] by simp]
    exact List.getLast?_append_of_ne_nil _ (by simp)
  have hMnd : polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) (k+1)) :=
    HexArea.chordRight_polyCycNondeg (b :: c :: rest ++ [a]) (k+1) b succ succ2 a
      (by omega) (by omega) hWnd (by simp) hsucc hsucc2 hlastW hseam1 hseam2
  exact ⟨0, HexArea.chordRight (b :: c :: rest ++ [a]) (k+1), w, b, b, succ, σ,
    Or.inr ⟨rfl, rfl⟩, hProt0, hMhead, hMlast, Or.inl rfl, hσ0, hσ1, hσ, hMnd⟩

/-- **The interior branch produces flat-seam data at the cut endpoint `w`
(PROVED).**  Setting of the Meisters interior branch: `a, b, c` is a cyclically
consecutive triple of the simple non-degenerate cycle `a :: b :: c :: rest`, the
vertex `w` lies strictly inside the corner triangle, and `W = b :: c :: rest ++ [a]`
is cut along the interior diagonal `b–w = W[0]–W[k]`.  If a chord piece with at
least four vertices fails to be cyclically non-degenerate, then it is flat exactly
at `w`, and deleting `w` restores non-degeneracy: it carries `FlatSeamData P b w`.

This is the input of the flat-seam case of `interior_lift_via_piece`. -/
lemma interior_flat_seam_data (a b c w : ℂ) (rest : List ℂ) (k : ℕ)
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hwin : HexArea.inTriangleStrict a b c w)
    (hk2 : 2 ≤ k) (hk : k + 2 ≤ (b :: c :: rest ++ [a]).length)
    (hwk : (b :: c :: rest ++ [a])[k]? = some w)
    (P : List ℂ)
    (hP : P = HexArea.chordLeft (b :: c :: rest ++ [a]) k ∨
          P = HexArea.chordRight (b :: c :: rest ++ [a]) k)
    (hPsimple : PolygonSimple P) :
    4 ≤ P.length → ¬ polyCycNondeg P → FlatSeamData P b w := by
  rcases hP with rfl | rfl
  · exact fun h4 hdeg =>
      interior_flat_seam_data_left a b c w rest k hnd hwin hk2 hk hwk hPsimple h4 hdeg
  · exact fun h4 hdeg =>
      interior_flat_seam_data_right a b c w rest k hnd hwin hk2 hk hwk hPsimple h4 hdeg

end
