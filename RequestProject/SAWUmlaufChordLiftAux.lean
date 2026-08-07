import Mathlib
import RequestProject.SAWUmlaufPolyEscape
import RequestProject.SAWUmlaufRayIndex
import RequestProject.SAWUmlaufEarTipEscape
import RequestProject.SAWUmlaufJordanStep
import RequestProject.SAWUmlaufExtremeOrient

/-!
# `SAWUmlaufChordLiftAux` — the two geometric inputs of the chord-split ear lift

This file sits between `SAWUmlaufPolyEscape` and `SAWUmlaufPolyMeisters` on the
route to the planar Umlaufsatz.  It isolates, as two sharply stated declarations,
the *geometric* content still needed by `chord_ear_lift` (the lift of an ear of a
chord-split piece to an ear of the whole polygon), and proves the purely
combinatorial part of that lift (`chord_lift_ear_rotation`).

After the correction of the Meisters invariant to its weak form (see
`RequestProject.SAWUmlaufFlatClipCounterexample` and the `EmptyCornerData2`
docstring), `chord_ear_lift` needs exactly four inputs:

1. **list surgery** — an ear of a piece whose tip avoids both cut endpoints is a
   triple of cyclically consecutive vertices of `W`; this is proved, in the two
   piece cases, by `chordLeft_interior_ear_extract` /
   `chordRight_interior_ear_extract`, and packaged here as
   `chord_lift_ear_rotation`;
2. **other-piece emptiness** — a vertex of the other piece is not strictly inside
   the ear triangle; this is the proved `chord_ear_empty_other`;
3. **other-piece diagonal avoidance** — a vertex of the other piece does not lie
   on the *closed ear diagonal* `[a', c']`; stated here as
   `chord_lift_other_not_on_diagonal` (**`sorry`**);
4. **orientation transfer** — each chord piece carries the same orientation as
   the whole polygon; stated here as `chord_piece_orient` (**`sorry`**).

Both `sorry`s are genuine plane-geometry facts (Jordan-level), not bookkeeping;
each is stated in the minimal form the lift consumes.
-/

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 1000000

/-- **The combinatorial half of the chord-split ear lift (proved).**  Let `W` be
a `Nodup` cycle cut at the chord `W[0]–W[k]`, let `P` be one of the two chord
pieces and let `P.rotate s = a' :: b' :: c' :: rest0` be an ear rotation of `P`
whose tip `b'` avoids both cut endpoints.  Then `a', b', c'` are three
cyclically consecutive vertices of `W` itself.

This is pure list/modular arithmetic; it merely dispatches to the two banked
bricks `chordLeft_interior_ear_extract` / `chordRight_interior_ear_extract`. -/
lemma chord_lift_ear_rotation (W : List ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ W.length) (hWnd : W.Nodup)
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (s : ℕ) (a' b' c' : ℂ) (rest0 : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: rest0)
    (hbu : b' ≠ W[0]!) (hbv : b' ≠ W[k]!) :
    ∃ (j : ℕ) (tl : List ℂ), W.rotate j = a' :: b' :: c' :: tl := by
  rcases hP with rfl | rfl
  · obtain ⟨i, hi1, hi2, hrot⟩ :=
      chordLeft_interior_ear_extract W k hk1 hk hWnd s a' b' c' rest0 hrotP hbu hbv
    exact ⟨i - 1, _, hrot⟩
  · obtain ⟨i, tl, hi1, hi2, hrot⟩ :=
      chordRight_interior_ear_extract W k hk1 hk hWnd s a' b' c' rest0 hrotP hbu hbv
    exact ⟨i - 1, tl, hrot⟩

/-- **Other-piece vertices avoid the closed ear diagonal (PROVED).**

Let the chord `W[0]–W[k]` be a valid interior diagonal of the simple polygon `W`,
splitting it into the piece `P` and the other piece, and let
`a' :: b' :: c' :: tlP` be an ear rotation of `P` (empty corner triangle, no
`P`-vertex on the closed diagonal `[a', c']`, coherent orientation).  Then no
vertex of `W` outside `P` lies on the closed segment `[a', c']` either.

Proof.  Such a vertex `x` lies off every edge of `P`
(`chordPiece_cycleEdge_or_diag` splits the edges of `P` into edges of `W` — which
`x` avoids by simplicity, `vertex_off_nonincident_edge` — and the cut diagonal,
which `x` avoids by `other_piece_vertex_not_on_valid_diagonal`), and it is not an
endpoint of the base, hence lies in its relative interior.  The midpoint of
`[x, b']` is then strictly inside the ear triangle
(`inTriangleStrict_base_perturb`) and the whole segment from `x` to it misses the
boundary of `P`, so the winding numbers agree
(`HexArea.ptWind_eq_of_segment_avoids`).  But the winding number of `P` around `x`
vanishes (`chord_ear_other_ptWind_zero`) while it is nonzero inside the ear
(`ear_interior_ptWind_ne_zero_of_rotation`, `RequestProject.SAWUmlaufEarTipEscape`)
— a contradiction.

NOT a dead branch: it is one of the four inputs of `chord_ear_lift`. -/
lemma chord_lift_other_not_on_diagonal (N : ℕ) (hN : DichBelow N)
    (W : List ℂ) (h4 : 4 ≤ W.length) (hWN : W.length ≤ N)
    (hsimple : PolygonSimple W) (hnd : polyCycNondeg W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a' b' c' : ℂ) (s : ℕ) (tlP : List ℂ)
    (hrotP : P.rotate s = a' :: b' :: c' :: tlP)
    (hDP : HexArea.cross (b' - a') (c' - b') ≠ 0)
    (hemptyP : ∀ y ∈ tlP, ¬ HexArea.inTriangleStrict a' b' c' y)
    (hdiagP : ∀ y ∈ tlP, y ∉ segment ℝ a' c')
    (horientP : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tlP)))
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    x ∉ segment ℝ a' c' := by
  intro hxseg
  -- (1) `x` lies off every edge of the piece `P`.
  have hxoff : ∀ e ∈ closedEdges P, x ∉ segment ℝ e.1 e.2 := by
    intro e he
    have he' : e ∈ HexArea.cycleEdges P := by rw [HexArea.cycleEdges_eq_closedEdges]; exact he
    obtain ⟨⟨h1P, h2P⟩, hcase⟩ := chordPiece_cycleEdge_or_diag W k hk1 hk u v hu hv P hP e he'
    rcases hcase with heW | hseg
    · exact vertex_off_nonincident_edge W h4 hsimple x hxW e.1 e.2 heW
        (fun h => hxP (h ▸ h1P)) (fun h => hxP (h ▸ h2P))
    · rw [hseg]
      exact other_piece_vertex_not_on_valid_diagonal W h4 hsimple hnd k hk1 hk u v hu hv hdiag
        P hP x hxW hxP
  -- (2) `x` lies in the *relative interior* of the ear base.
  have ha'P : a' ∈ P := by
    have hmem : a' ∈ P.rotate s := by rw [hrotP]; simp
    exact (List.mem_rotate).mp hmem
  have hc'P : c' ∈ P := by
    have hmem : c' ∈ P.rotate s := by rw [hrotP]; simp
    exact (List.mem_rotate).mp hmem
  have hxa : x ≠ a' := fun h => hxP (h ▸ ha'P)
  have hxc : x ≠ c' := fun h => hxP (h ▸ hc'P)
  have hxopen : x ∈ openSegment ℝ a' c' := by
    rw [← insert_endpoints_openSegment] at hxseg
    simp only [Set.mem_insert_iff] at hxseg
    rcases hxseg with h | h | h
    · exact absurd h hxa
    · exact absurd h hxc
    · exact h
  -- (3) Perturb `x` towards the tip: the midpoint of `[x, b']` is strictly inside.
  set y : ℂ := ((1 - (1/2 : ℝ) : ℝ) : ℂ) * x + (((1/2 : ℝ)) : ℂ) * b' with hy
  have hyin : HexArea.inTriangleStrict a' b' c' y :=
    inTriangleStrict_base_perturb a' b' c' x hDP hxopen (1/2) (by norm_num) (by norm_num)
  -- (4) The winding number of `P` is unchanged along `[x, y]`.
  have hwind : HexArea.ptWind x P = HexArea.ptWind y P := by
    refine HexArea.ptWind_eq_of_segment_avoids P x y ?_
    intro e he
    rw [HexArea.cycleEdges_eq_closedEdges] at he
    rw [Set.disjoint_left]
    intro w hw hwe
    obtain ⟨u1, u2, hu1, hu2, husum, hweq⟩ := hw
    by_cases hu2z : u2 = 0
    · have hwx : w = x := by
        have hu1' : u1 = 1 := by rw [hu2z] at husum; linarith
        rw [← hweq, hu2z, hu1']; simp
      exact hxoff e he (hwx ▸ hwe)
    · have hu2pos : 0 < u2 := lt_of_le_of_ne hu2 (Ne.symm hu2z)
      have hwform : w = ((1 - u2 / 2 : ℝ) : ℂ) * x + ((u2 / 2 : ℝ) : ℂ) * b' := by
        have hu1' : u1 = 1 - u2 := by linarith
        rw [← hweq, hy, hu1']
        push_cast [Complex.real_smul]
        ring
      have hwin : HexArea.inTriangleStrict a' b' c' w := by
        rw [hwform]
        exact inTriangleStrict_base_perturb a' b' c' x hDP hxopen (u2 / 2) (by linarith)
          (by linarith)
      exact ear_interior_off_closedEdges_of_rotation P hPsimple a' b' c' s tlP hrotP hDP
        hemptyP hdiagP w hwin e he hwe
  -- (5) The piece does not wind around `x`, but it does wind around `y`.
  have hzero := chord_ear_other_ptWind_zero W hsimple k hk1 hk u v hu hv hdiag hint P hP x hxW hxP
  have hPN : P.length ≤ N := by
    have : P.length ≤ W.length := by
      rcases hP with rfl | rfl
      · rw [HexArea.chordLeft_length W k hk]; omega
      · rw [HexArea.chordRight_length W k (by omega)]; omega
    omega
  exact ear_interior_ptWind_ne_zero_of_rotation_below N hN P hPN hPsimple a' b' c' s tlP
    hrotP hDP hemptyP hdiagP horientP y hyin (by rw [← hwind]; exact hzero)

/-- **Corner signs at a strictly interior chord endpoint (pure algebra).**  If
`v` lies strictly inside the corner triangle `pu, u, nu` of the polygon at `u`,
then the two corners that the chord `u–v` creates at `u` — namely `pu → u → v`
and `v → u → nu` — turn the same way as the corner `pu → u → nu` of the polygon
itself, and neither of them is flat.

The three cross products are the three sub-triangle areas of the corner
triangle, and they add up to the area of the whole corner triangle; strict
interiority makes all three of them have one and the same (nonzero) sign. -/
lemma HexArea.corner_signs_of_inTriangleStrict (pu u nu v : ℂ)
    (h : HexArea.inTriangleStrict pu u nu v) :
    (((0:ℝ) < HexArea.cross (u - pu) (v - u))
        ↔ ((0:ℝ) < HexArea.cross (u - pu) (nu - u))) ∧
    (((0:ℝ) < HexArea.cross (u - v) (nu - u))
        ↔ ((0:ℝ) < HexArea.cross (u - pu) (nu - u))) ∧
    HexArea.cross (v - u) (nu - u) ≠ 0 ∧
    HexArea.cross (pu - u) (v - u) ≠ 0 := by
  have e1 : HexArea.cross (u - pu) (v - pu) = HexArea.cross (u - pu) (v - u) := by
    simp [HexArea.cross]; ring
  have e2 : HexArea.cross (nu - u) (v - u) = HexArea.cross (u - v) (nu - u) := by
    simp [HexArea.cross]; ring
  have e3 : HexArea.cross (u - pu) (v - u) + HexArea.cross (u - v) (nu - u)
      + HexArea.cross (pu - nu) (v - nu) = HexArea.cross (u - pu) (nu - u) := by
    simp [HexArea.cross]; ring
  have e4 : HexArea.cross (v - u) (nu - u) = - HexArea.cross (u - v) (nu - u) := by
    simp [HexArea.cross]; ring
  have e5 : HexArea.cross (pu - u) (v - u) = - HexArea.cross (u - pu) (v - u) := by
    simp [HexArea.cross]; ring
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [e1] at h1; rw [e2] at h2
    have hs : (0:ℝ) < HexArea.cross (u - pu) (nu - u) := by linarith
    exact ⟨⟨fun _ => hs, fun _ => h1⟩, ⟨fun _ => hs, fun _ => h2⟩,
      by rw [e4]; linarith, by rw [e5]; linarith⟩
  · rw [e1] at h1; rw [e2] at h2
    have hs : HexArea.cross (u - pu) (nu - u) < 0 := by linarith
    refine ⟨⟨fun hh => absurd hh (by linarith), fun hh => absurd hh (by linarith)⟩,
      ⟨fun hh => absurd hh (by linarith), fun hh => absurd hh (by linarith)⟩,
      by rw [e4]; linarith, by rw [e5]; linarith⟩

/-- **Both chord pieces of a valid diagonal cut are simple.**  Packaging of the
banked combinatorial bricks `HexArea.chordLeft_PolygonSimple` /
`HexArea.chordRight_PolygonSimple` against the diagonal-validity hypothesis
`hdiag` in the form the Meisters chain carries it. -/
lemma chord_pieces_PolygonSimple (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk2 : 2 ≤ k) (hk : k + 1 ≤ W.length) (u v : ℂ)
    (hu : W.head? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2)) :
    PolygonSimple (HexArea.chordLeft W k) ∧ PolygonSimple (HexArea.chordRight W k) := by
  constructor
  · refine HexArea.chordLeft_PolygonSimple W k u v hk2 hk hsimple hu hv ?_
    intro e he hv1 hv2 hu1 hu2
    rw [segment_symm]
    refine hdiag e (HexArea.mem_closedEdges_of_mem_pathEdges W e ?_) hu1 hu2 hv1 hv2
    exact HexArea.mem_pathEdges_take W (k + 1) e he
  · refine HexArea.chordRight_PolygonSimple W k u v (by omega) (by omega) hsimple hu hv ?_
    intro e he hu1 hu2 hv1 hv2
    exact hdiag e (HexArea.pathEdges_chordRight_mem_closedEdges W k (by omega) e he)
      hu1 hu2 hv1 hv2

/-- **Both chord pieces carry the orientation of the whole polygon (PROVED).**

If the chord `W[0]–W[k]` is a valid interior diagonal of the simple polygon `W`
(`hdiag` : it meets no non-incident edge; `hint` : its start `u = W[0]` is a
strictly extreme convex corner of `W` and its end `v = W[k]` lies strictly
inside the corner triangle at `u`), then the signed areas of the two pieces
`chordLeft W k`, `chordRight W k` are both positive exactly when the signed area
of `W` is (and, by `HexArea.shoelace2_chord_split`, they add up to it).

Proof.  The corner `u` is strictly extreme for `W`, hence also for either piece,
and the chord `u–v` splits the corner `pu → u → nu` into the two corners
`pu → u → v` and `v → u → nu`, which by `HexArea.corner_signs_of_inTriangleStrict`
turn the same way.  Reading the orientation of each piece off at `u` with
`HexArea.extreme_corner_orient` therefore gives both pieces the sign of the
corner `pu → u → nu`; the additivity of `shoelace2` then transfers that common
sign to `W`.

Because the orientation is read off through the point-in-polygon dichotomy, the
statement is relative to `DichBelow N` for an `N` bounding `W.length`; the two
pieces are strictly shorter than `W`, so `W.length ≤ N` suffices. -/
lemma chord_piece_orient (N : ℕ) (hN : DichBelow N) (W : List ℂ) (h4 : 4 ≤ W.length)
    (hWN : W.length ≤ N) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v) :
    ((0:ℝ) < HexArea.shoelace2 (HexArea.chordLeft W k)
        ↔ (0:ℝ) < HexArea.shoelace2 W) ∧
    ((0:ℝ) < HexArea.shoelace2 (HexArea.chordRight W k)
        ↔ (0:ℝ) < HexArea.shoelace2 W) := by
  classical
  obtain ⟨pu, nu, hhead, hlast, hnu, hconv, ⟨d, hd⟩, htri⟩ := hint
  obtain ⟨hsign1, hsign2, hXL, hXR⟩ := HexArea.corner_signs_of_inTriangleStrict pu u nu v htri
  -- the chord index is genuinely interior: `2 ≤ k ≤ |W| - 2`
  have hvnu : v ≠ nu := HexArea.inTriangleStrict_ne_c pu u nu v htri
  have hvpu : v ≠ pu := HexArea.inTriangleStrict_ne_a pu u nu v htri
  have hk2 : 2 ≤ k := by
    rcases Nat.eq_or_lt_of_le hk1 with h1 | h1
    · exfalso
      rw [← h1, hnu] at hv
      exact hvnu (Option.some_inj.mp hv).symm
    · omega
  have hklast : k + 2 ≤ W.length := by
    by_contra hcon
    have hkeq : k = W.length - 1 := by omega
    have hgl : W.getLast? = W[k]? := by rw [List.getLast?_eq_getElem?, hkeq]
    rw [hlast, hv] at hgl
    exact hvpu (Option.some_inj.mp hgl).symm
  -- write `W` out at its first two vertices
  obtain ⟨tw, hWeq⟩ : ∃ tw, W = u :: nu :: tw := by
    match W, h4 with
    | w0 :: w1 :: tw, _ =>
      have h0 : w0 = u := by simpa using hu
      have h1 : w1 = nu := by simpa using hnu
      exact ⟨tw, by rw [h0, h1]⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have htwlen : tw.length = W.length - 2 := by rw [hWeq]; simp
  have hjlt : j < tw.length := by omega
  -- the two pieces, explicitly
  have hLeq : HexArea.chordLeft W (j + 2) = u :: nu :: tw.take (j + 1) := by
    rw [hWeq]; simp [HexArea.chordLeft]
  have hdropk : W.drop (j + 2) = tw.drop j := by rw [hWeq]; simp
  have htwj : tw[j]? = some v := by rw [hWeq] at hv; simpa using hv
  have hdropj : tw.drop j = v :: tw.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hjlt]
    congr 1
    exact (List.getElem?_eq_getElem hjlt ▸ htwj : some tw[j] = some v) |> Option.some_inj.mp
  have hReq : HexArea.chordRight W (j + 2) = (v :: tw.drop (j + 1)) ++ [u] := by
    rw [HexArea.chordRight, hdropk, hdropj, hWeq]; simp
  -- the rotation of the right piece that puts the extreme corner `u` first
  have hRrot : (HexArea.chordRight W (j + 2)).rotate (v :: tw.drop (j + 1)).length
      = u :: v :: tw.drop (j + 1) := by
    rw [hReq, List.rotate_append_length_eq]; rfl
  -- simplicity of the two pieces
  have huhead : W.head? = some u := by rw [hWeq]; simp
  obtain ⟨hLsimple, hRsimple⟩ :=
    chord_pieces_PolygonSimple W hsimple (j + 2) (by omega) (by omega) u v huhead hv hdiag
  -- memberships
  have hLmem : ∀ y ∈ u :: nu :: tw.take (j + 1), y ∈ W := by
    intro y hy
    rw [← hLeq] at hy
    exact List.mem_of_mem_take hy
  have hRmem : ∀ y ∈ u :: v :: tw.drop (j + 1), y ∈ W := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact List.mem_of_mem_head? huhead
    · have : y ∈ W.drop (j + 2) := by rw [hdropk, hdropj]; exact hy'
      exact List.mem_of_mem_drop this
  -- lengths
  have hLlen : (u :: nu :: tw.take (j + 1)).length = j + 3 := by
    simp [List.length_take]; omega
  have hRlen : (u :: v :: tw.drop (j + 1)).length = W.length - j - 1 := by
    simp [List.length_drop]; omega
  -- the last vertex of the right piece is `pu`
  have hRlast : (u :: v :: tw.drop (j + 1)).getLast? = some pu := by
    have hne : (tw.drop (j + 1)) ≠ [] := by
      intro hcon
      have := congrArg List.length hcon
      simp [List.length_drop] at this
      omega
    have hcons : ∀ (a : ℂ) (l : List ℂ), l ≠ [] → (a :: l).getLast? = l.getLast? := by
      intro a l hl
      cases l with
      | nil => exact absurd rfl hl
      | cons b t => simp [List.getLast?_cons_cons]
    have h1 : (u :: v :: tw.drop (j + 1)).getLast? = (tw.drop (j + 1)).getLast? := by
      rw [hcons u (v :: tw.drop (j + 1)) (by simp), hcons v _ hne]
    have h2 : (tw.drop (j + 1)).getLast? = tw.getLast? := by
      rw [List.getLast?_drop]
      have : ¬ (tw.length ≤ j + 1) := by omega
      simp [this]
    have h3 : tw.getLast? = W.getLast? := by
      have hne2 : tw ≠ [] := by
        intro hcon; rw [hcon] at hjlt; simp at hjlt
      rw [hWeq, hcons u (nu :: tw) (by simp), hcons nu tw hne2]
    rw [h1, h2, h3, hlast]
  -- **orientation of the left piece**, read off at the extreme corner `u`
  have horL : ((0:ℝ) < HexArea.shoelace2 (HexArea.chordLeft W (j + 2)))
      ↔ (0:ℝ) < HexArea.cross (u - v) (nu - u) := by
    rw [hLeq]
    refine HexArea.extreme_corner_orient N hN u nu v d (tw.take (j + 1)) ?_ ?_ ?_ ?_ ?_ hXL
    · rw [hLlen]; omega
    · rw [hLlen]; omega
    · rw [← hLeq]; exact hLsimple
    · rw [← hLeq, HexArea.chordLeft_getLast W (j + 2) (by omega)]; exact hv
    · intro y hy hyu; exact hd y (hLmem y hy) hyu
  -- **orientation of the right piece**, read off at the same corner
  have horR : ((0:ℝ) < HexArea.shoelace2 (HexArea.chordRight W (j + 2)))
      ↔ (0:ℝ) < HexArea.cross (u - pu) (v - u) := by
    have hrotarea : HexArea.shoelace2 (HexArea.chordRight W (j + 2))
        = HexArea.shoelace2 (u :: v :: tw.drop (j + 1)) := by
      rw [← hRrot, shoelace2_rotate]
    rw [hrotarea]
    refine HexArea.extreme_corner_orient N hN u v pu d (tw.drop (j + 1)) ?_ ?_ ?_ hRlast ?_ hXR
    · rw [hRlen]; omega
    · rw [hRlen]; omega
    · rw [← hRrot]; exact (PolygonSimple_rotate _ _).mpr hRsimple
    · intro y hy hyu; exact hd y (hRmem y hy) hyu
  -- assemble: both pieces have the sign of the corner `pu → u → nu`
  have hLW : ((0:ℝ) < HexArea.shoelace2 (HexArea.chordLeft W (j + 2)))
      ↔ (0:ℝ) < HexArea.cross (u - pu) (nu - u) := horL.trans hsign2
  have hRW : ((0:ℝ) < HexArea.shoelace2 (HexArea.chordRight W (j + 2)))
      ↔ (0:ℝ) < HexArea.cross (u - pu) (nu - u) := horR.trans hsign1
  have hsplit := HexArea.shoelace2_chord_split W (j + 2) (by omega) (by omega)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h1 := hRW.mpr (hLW.mp h); linarith
  · by_contra hcon
    have h2 : ¬ ((0:ℝ) < HexArea.shoelace2 (HexArea.chordRight W (j + 2))) :=
      fun hh => hcon (hLW.mpr (hRW.mp hh))
    push_neg at hcon h2
    linarith
  · have h1 := hLW.mpr (hRW.mp h); linarith
  · by_contra hcon
    have h2 : ¬ ((0:ℝ) < HexArea.shoelace2 (HexArea.chordLeft W (j + 2))) :=
      fun hh => hcon (hRW.mpr (hLW.mp hh))
    push_neg at hcon h2
    linarith

/-- **Triangle piece: the other piece's vertices are outside it (PROVED).**
If a chord piece `P` of the valid interior cut `W[0]–W[k]` is a *triangle*
`[a, b, c]`, then no vertex of `W` outside `P` lies strictly inside that
triangle.

Unlike the general `chord_ear_empty_other`, this needs no ear data and no
orientation hypothesis: the winding number of the triangle about a strictly
interior point is `±2π` (`HexArea.ptWind_triangle`), whereas the winding of the
piece about a vertex of the other piece is `0` (the corner-escape theorem
`chord_ear_other_ptWind_zero`).

This is exactly the emptiness input needed when the recursion piece of the
Meisters interior branch degenerates to a triangle — the case in which
`EmptyCornerData2 P` is unavailable and the `V`-ear must be built directly. -/
lemma chord_triangle_piece_empty (W : List ℂ) (hsimple : PolygonSimple W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (a b c : ℂ) (hPeq : P = [a, b, c])
    (x : ℂ) (hxW : x ∈ W) (hxP : x ∉ P) :
    ¬ HexArea.inTriangleStrict a b c x := by
  intro hin
  have h0 : HexArea.ptWind x P = 0 :=
    chord_ear_other_ptWind_zero W hsimple k hk1 hk u v hu hv hdiag hint P hP x hxW hxP
  rw [hPeq, HexArea.ptWind_triangle a b c x hin] at h0
  have hpi := Real.pi_pos
  split_ifs at h0 <;> linarith


/-- **The triangle-piece ear package (PROVED).**
When a chord piece `P` of the valid interior cut `W[0]–W[k]` has only three
vertices, the single vertex it cuts off is an ear of `W` itself: `P = [u, m, v]`
(left piece, forcing `k = 2`) or `P = [v, m, u]` (right piece, forcing
`k = W.length - 2`), and in both cases the triple is a cyclically consecutive
triple of `W` whose corner triangle is `P` itself.  Its emptiness against the
other piece is `chord_triangle_piece_empty`, the avoidance of the closed ear
diagonal — which here *is* the chord `[u, v]` — is
`other_piece_vertex_not_on_valid_diagonal`, and the orientation clause follows
from `chord_piece_orient` and the additivity `HexArea.shoelace2_chord_split`.

This is the degenerate branch of the Meisters interior recursion, where the piece
is too short to apply the induction hypothesis. -/
lemma chord_triangle_piece_package (N : ℕ) (hN : DichBelow N)
    (W : List ℂ) (h4 : 4 ≤ W.length) (hWN : W.length ≤ N)
    (hsimple : PolygonSimple W) (hnd : polyCycNondeg W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (hP3 : P.length = 3) :
    ∃ (j : ℕ) (a' b' c' p' q' : ℂ) (tl : List ℂ),
      W.rotate j = a' :: b' :: c' :: tl ∧
      b' ∈ P ∧ b' ≠ u ∧ b' ≠ v ∧
      tl.getLast? = some p' ∧ tl.head? = some q' ∧
      (∀ x ∈ tl, ¬ HexArea.inTriangleStrict a' b' c' x) ∧
      (∀ x ∈ tl, x ∉ segment ℝ a' c') ∧
      ((0:ℝ) < HexArea.shoelace2 [a', b', c']
          ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tl)) := by
  have hWnd : W.Nodup := hsimple.1
  have hklt : k < W.length := by omega
  have hsplit := HexArea.shoelace2_chord_split W k hk1 hklt
  obtain ⟨hL, hR⟩ :=
    chord_piece_orient N hN W h4 hWN hsimple k hk1 hk u v hu hv hdiag hint
  -- The generic orientation step, shared by the two cases.
  have horient_of : ∀ (T aP aQ : ℝ), aP + aQ = HexArea.shoelace2 W → T = aP →
      ((0:ℝ) < aP ↔ (0:ℝ) < HexArea.shoelace2 W) →
      ((0:ℝ) < aQ ↔ (0:ℝ) < HexArea.shoelace2 W) →
      ((0:ℝ) < T ↔ (0:ℝ) < HexArea.shoelace2 W - T) := by
    intro T aP aQ hsum hTP hPo hQo
    subst hTP
    constructor
    · intro hT
      have : (0:ℝ) < aQ := hQo.mpr (hPo.mp hT)
      linarith
    · intro hW
      have : (0:ℝ) < aQ := by linarith
      exact hPo.mpr (hQo.mp this)
  rcases hP with rfl | rfl
  · -- **Left piece**: `chordLeft W k = W.take (k+1)` has length `k+1 = 3`.
    have hk2 : k = 2 := by
      have : (HexArea.chordLeft W k).length = k + 1 := by
        simp [HexArea.chordLeft, List.length_take]; omega
      omega
    subst hk2
    obtain ⟨w1, w3, rest, rfl⟩ : ∃ w1 w3 rest, W = u :: w1 :: v :: w3 :: rest := by
      match W, h4 with
      | w0 :: w1 :: w2 :: w3 :: rest, _ =>
        have hu' : w0 = u := by simpa using hu
        have hv' : w2 = v := by simpa using hv
        exact ⟨w1, w3, rest, by rw [hu', hv']⟩
    have hPeq : HexArea.chordLeft (u :: w1 :: v :: w3 :: rest) 2 = [u, w1, v] := by
      simp [HexArea.chordLeft]
    have hndc : (u :: w1 :: v :: w3 :: rest).Nodup := hWnd
    simp only [List.nodup_cons, List.mem_cons] at hndc
    push_neg at hndc
    obtain ⟨⟨hu1, huv, hu3, hurest⟩, ⟨h1v, h13, h1rest⟩, ⟨hv3, hvrest⟩, -⟩ := hndc
    have hx_ne : ∀ x ∈ (w3 :: rest), x ≠ u ∧ x ≠ w1 ∧ x ≠ v := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨fun h => hu3 h.symm, fun h => h13 h.symm, fun h => hv3 h.symm⟩
      · exact ⟨fun h => hurest (h ▸ hx), fun h => h1rest (h ▸ hx), fun h => hvrest (h ▸ hx)⟩
    have hxP' : ∀ x ∈ (w3 :: rest),
        x ∉ HexArea.chordLeft (u :: w1 :: v :: w3 :: rest) 2 := by
      intro x hx
      obtain ⟨e1, e2, e3⟩ := hx_ne x hx
      rw [hPeq]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      push_neg
      exact ⟨e1, e2, e3⟩
    have hxW' : ∀ x ∈ (w3 :: rest), x ∈ (u :: w1 :: v :: w3 :: rest) := by
      intro x hx; simp only [List.mem_cons] at hx ⊢; tauto
    refine ⟨0, u, w1, v, (w3 :: rest).getLast (by simp), w3, w3 :: rest, by simp, ?_,
      ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
    · rw [hPeq]; simp
    · exact fun h => hu1 h.symm
    · exact h1v
    · exact List.getLast?_eq_some_getLast _
    · -- emptiness
      intro x hx
      exact chord_triangle_piece_empty _ hsimple 2 hk1 hk u v (by simp) (by simp) hdiag hint
        _ (Or.inl rfl) u w1 v hPeq x (hxW' x hx) (hxP' x hx)
    · -- diagonal avoidance: the ear diagonal is the chord itself
      intro x hx
      exact other_piece_vertex_not_on_valid_diagonal _ h4 hsimple hnd 2 hk1 hk u v
        (by simp) (by simp) hdiag _ (Or.inl rfl) x (hxW' x hx) (hxP' x hx)
    · -- orientation
      have hT : HexArea.shoelace2 [u, w1, v]
          = HexArea.shoelace2 (HexArea.chordLeft (u :: w1 :: v :: w3 :: rest) 2) := by
        rw [hPeq]
      have hclip : HexArea.shoelace2 (u :: w1 :: v :: w3 :: rest)
          = HexArea.shoelace2 (u :: v :: w3 :: rest) + HexArea.shoelace2 [u, w1, v] :=
        shoelace2_clip_second u w1 v (w3 :: rest)
      have := horient_of (HexArea.shoelace2 [u, w1, v]) _ _ hsplit hT hL hR
      rw [this]
      constructor <;> intro h <;> linarith
  · -- **Right piece**: `chordRight W k = W.drop k ++ W.take 1` has length
    -- `W.length - k + 1 = 3`.
    have hlenR : (HexArea.chordRight W k).length = W.length - k + 1 := by
      simp only [HexArea.chordRight, List.length_append, List.length_drop, List.length_take]
      omega
    have hkval : k + 2 = W.length := by omega
    obtain ⟨W1, rfl⟩ : ∃ W1, W = u :: W1 := by
      match W, h4 with
      | w0 :: W1, _ =>
        have hu' : w0 = u := by simpa using hu
        exact ⟨W1, by rw [hu']⟩
    set W := u :: W1 with hWdef
    have hW1len : W1.length = W.length - 1 := by rw [hWdef]; simp
    have hdropk : W.drop k = [W[k], W[k + 1]] := by
      have h1 : W.drop (k + 2) = [] := by rw [List.drop_eq_nil_iff]; omega
      rw [List.drop_eq_getElem_cons hklt,
        List.drop_eq_getElem_cons (show k + 1 < W.length by omega), h1]
    have hvv : W[k] = v := by
      have : W[k]? = some W[k] := List.getElem?_eq_getElem hklt
      rw [hv] at this; exact (Option.some.injEq _ _ ▸ this).symm
    have htakek : W.take k = u :: W1.take (k - 1) := by
      rw [hWdef, show k = (k - 1) + 1 by omega]
      simp
    have hrotk : W.rotate k = v :: W[k + 1] :: u :: W1.take (k - 1) := by
      rw [List.rotate_eq_drop_append_take (by omega), hdropk, htakek, hvv]
      simp
    have htake1 : W.take 1 = [u] := by rw [hWdef]; simp
    have hPeq : HexArea.chordRight W k = [v, W[k + 1], u] := by
      rw [HexArea.chordRight, hdropk, htake1, hvv]
      simp
    have htlne : W1.take (k - 1) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      simp only [List.length_take, List.length_nil] at hlen
      omega
    have hWnd' : (W.rotate k).Nodup := List.nodup_rotate.mpr hWnd
    rw [hrotk] at hWnd'
    simp only [List.nodup_cons, List.mem_cons] at hWnd'
    push_neg at hWnd'
    obtain ⟨⟨hv1, hvu, hvtl⟩, ⟨h1u, h1tl⟩, ⟨hutl, -⟩⟩ := hWnd'
    have hxW' : ∀ x ∈ W1.take (k - 1), x ∈ W := by
      intro x hx
      have : x ∈ W.rotate k := by rw [hrotk]; simp [hx]
      exact (List.mem_rotate).mp this
    have hxP' : ∀ x ∈ W1.take (k - 1), x ∉ HexArea.chordRight W k := by
      intro x hx
      rw [hPeq]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      push_neg
      exact ⟨fun h => hvtl (h ▸ hx), fun h => h1tl (h ▸ hx), fun h => hutl (h ▸ hx)⟩
    refine ⟨k, v, W[k + 1], u, (W1.take (k - 1)).getLast htlne, (W1.take (k - 1)).head htlne,
      W1.take (k - 1), hrotk, ?_, h1u, fun h => hv1 h.symm,
      List.getLast?_eq_some_getLast _, List.head?_eq_some_head _, ?_, ?_, ?_⟩
    · rw [hPeq]; simp
    · -- emptiness
      intro x hx
      exact chord_triangle_piece_empty W hsimple k hk1 hk u v (by rw [hWdef]; simp) hv hdiag
        hint _ (Or.inr rfl) v W[k + 1] u hPeq x (hxW' x hx) (hxP' x hx)
    · -- diagonal avoidance
      intro x hx
      have := other_piece_vertex_not_on_valid_diagonal W h4 hsimple hnd k hk1 hk u v
        (by rw [hWdef]; simp) hv hdiag _ (Or.inr rfl) x (hxW' x hx) (hxP' x hx)
      rwa [segment_symm]
    · -- orientation
      have hT : HexArea.shoelace2 [v, W[k + 1], u]
          = HexArea.shoelace2 (HexArea.chordRight W k) := by rw [hPeq]
      have hclip : HexArea.shoelace2 (v :: W[k + 1] :: u :: W1.take (k - 1))
          = HexArea.shoelace2 (v :: u :: W1.take (k - 1))
            + HexArea.shoelace2 [v, W[k + 1], u] :=
        shoelace2_clip_second v W[k + 1] u (W1.take (k - 1))
      have hWrot : HexArea.shoelace2 (v :: W[k + 1] :: u :: W1.take (k - 1))
          = HexArea.shoelace2 W := by rw [← hrotk]; exact shoelace2_rotate W k
      have := horient_of (HexArea.shoelace2 [v, W[k + 1], u]) _
        (HexArea.shoelace2 (HexArea.chordLeft W k)) (by linarith) hT hR hL
      rw [this]
      constructor <;> intro h <;> linarith

/-- The orientation transfer in the form the ear lift consumes: if the ear
triangle `T` of the piece `P` has the piece's clip orientation, it also has the
whole polygon's clip orientation.  Pure arithmetic from `chord_piece_orient` and
the additivity `shoelace2 P + shoelace2 Q = shoelace2 W`. -/
lemma orient_transfer_of_split (T aP aQ aW : ℝ)
    (hsplit : aP + aQ = aW)
    (hP : (0:ℝ) < aP ↔ (0:ℝ) < aW) (hQ : (0:ℝ) < aQ ↔ (0:ℝ) < aW)
    (horientP : (0:ℝ) < T ↔ (0:ℝ) < aP - T) :
    ((0:ℝ) < T ↔ (0:ℝ) < aW - T) := by
  constructor
  · intro hT
    have h1 : (0:ℝ) < aP - T := horientP.mp hT
    have h2 : (0:ℝ) < aP := by linarith
    have h3 : (0:ℝ) < aQ := hQ.mpr (hP.mp h2)
    linarith
  · intro hW
    by_contra hT
    push_neg at hT
    have h1 : ¬ ((0:ℝ) < aP - T) := fun h => absurd (horientP.mpr h) (by linarith)
    push_neg at h1
    have h2 : ¬ ((0:ℝ) < aP) := by intro h; linarith
    have h3 : ¬ ((0:ℝ) < aQ) := fun h => h2 (hP.mpr (hQ.mp h))
    push_neg at h3
    linarith

end
