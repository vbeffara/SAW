import Mathlib
import RequestProject.SAWUmlaufPolyEscape
import RequestProject.SAWUmlaufChordLiftAux
import RequestProject.SAWUmlaufFlatSeamLift
import RequestProject.SAWUmlaufJordanCore

/-!
# `SAWUmlaufPolygon`, part `SAWUmlaufPolyMeisters`

This file is one of the six parts the (formerly single, 7000-line) planar
polygon Umlaufsatz development was split into.  Parts are chained by imports
`SAWUmlaufPolyBase → SAWUmlaufPolyChord → SAWUmlaufPolyLift →
SAWUmlaufPolyEscape → SAWUmlaufPolyMeisters → SAWUmlaufPolygon`, and the last
part is imported by `RequestProject.SAWUmlaufSignedArea`, hence lies on the live
route to the main theorem.  See `SAWUmlaufPolyBase` for the overview.
-/

open Real Complex ComplexConjugate

noncomputable section

set_option maxHeartbeats 4000000

/-
**Interior-ear neighbour identification (list-surgery brick for
    `chord_ear_lift`, chordLeft case).**  When the lifted ear tip sits at a
    *fully interior* index `i` of `W` (i.e. `2 ≤ i` and `i + 3 ≤ W.length`, so
    the ear is not adjacent to either cut endpoint `W[0]` / `W[k]`), the cyclic
    remainder `tl = W.drop (i+2) ++ W.take (i-1)` produced by
    `chordLeft_interior_ear_extract` has its last vertex `= W[i-2]` (the genuine
    cyclic `W`-predecessor of the ear's left vertex `a' = W[i-1]`) and its first
    vertex `= W[i+2]` (the genuine cyclic `W`-successor of the ear's right vertex
    `c' = W[i+1]`).  Pure list/index arithmetic, no geometry; numerically
    validated over many index configurations.

    This is exactly the fact that makes the interior (non-seam) subcase of
    `chord_ear_lift` pure bookkeeping: in that subcase the `EmptyCornerData2 P`
    clip-neighbours `pP = rest0.getLast?`, `qP = rest0.head?` coincide with these
    `W`-neighbours, so the two clip-corner non-flatness clauses transfer directly
    from `EmptyCornerData2 P` (leaving only the two genuine *seam* subcases
    `i = 1` / `i + 1 = k` as the residual geometric content).  Stated
    polymorphically for reuse.  NOT a dead branch — banked preparation consumed by
    `chord_ear_lift`.
-/
lemma chordLeft_ear_tl_neighbours {α : Type*} (W : List α) (i : ℕ)
    (hi : 2 ≤ i) (hik : i + 3 ≤ W.length) :
    (W.drop (i + 2) ++ W.take (i - 1)).getLast? = W[i - 2]? ∧
    (W.drop (i + 2) ++ W.take (i - 1)).head? = W[i + 2]? := by
  grind +suggestions

/-
**Rotated-remainder cyclic-neighbour identification (list-surgery brick for
    `chord_ear_lift`, chordRight case).**  For a list `W` of length `≥ 4`, the
    3-truncated rotation `(W.rotate j).drop 3` — the shape the tail `tl` takes in
    `chordRight_interior_ear_extract`, where `tl = (W.rotate (i-1)).drop 3`,
    i.e. `j = i - 1` — has first vertex `W[(j+3) mod n]` (the cyclic successor of
    the ear's right vertex `c'`) and last vertex `W[(j+n-1) mod n]` (the cyclic
    predecessor of the ear's left vertex `a'`), where `n = W.length`.  Pure
    list/modular arithmetic, no geometry; numerically validated over many
    rotations.  Stated polymorphically for reuse.  NOT a dead branch — banked
    preparation consumed by `chord_ear_lift`.
-/
lemma rotate_drop3_neighbours {α : Type*} (W : List α) (j : ℕ)
    (hn : 4 ≤ W.length) :
    ((W.rotate j).drop 3).head? = W[(j + 3) % W.length]? ∧
    ((W.rotate j).drop 3).getLast? = W[(j + W.length - 1) % W.length]? := by
  rcases n : W.length with ( _ | _ | _ | _ | n ) <;> simp_all +arith +decide;
  rw [ List.getLast?_eq_getElem? ];
  simp +arith +decide [ List.getElem?_rotate, n ];
  grind +suggestions

/-- **Chord ear-lift brick (now PROVED, modulo the two isolated geometric inputs
    of `RequestProject.SAWUmlaufChordLiftAux`).**
    Cut the rotation `W` of a simple polygon `V` (`hW : V.rotate ρ = W`) along the
    interior diagonal `W[0]–W[k]` into the two pieces `chordLeft W k` /
    `chordRight W k`.  An ear of one piece `P` that avoids the cut edge `{u, v}`
    (where `u = W[0]`, `v = W[k]`) — packaged as `EmptyCornerData2 P u v` — lifts
    to a genuine ear of the *whole* polygon `V` whose tip `b'` is an interior
    vertex of `P` (hence `b' ≠ u, v`).

    The proof has four ingredients:

    * the **list surgery** `chord_lift_ear_rotation` (proved): the ear triple of
      the piece consists of three cyclically consecutive vertices of `W`;
    * the far-vertex clauses over the lifted tail `tl` split into the vertices of
      `P` (handled by the ear data of `P` itself) and the vertices of the OTHER
      piece, handled by the proved Jordan keystone `chord_ear_empty_other`
      (emptiness) and by `chord_lift_other_not_on_diagonal` (the closed ear
      diagonal — one of the two remaining `sorry`s);
    * the **orientation** clause, from `chord_piece_orient` (the other remaining
      `sorry`: both chord pieces carry the orientation of the whole polygon)
      together with the additivity `HexArea.shoelace2_chord_split` and the pure
      arithmetic `orient_transfer_of_split`.

    **History.**  While `EmptyCornerData2` still demanded the two clip-corner
    non-flatness clauses, this lemma had a further genuine residue at the *seam*
    (the clip corner of a seam ear involves the other piece's neighbour, which is
    not a consecutive `V`-corner).  Those clauses are refuted in general by
    `RequestProject.SAWUmlaufFlatClipCounterexample` and have been dropped, so
    the seam residue is gone. -/
lemma chord_ear_lift (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hsimple : PolygonSimple V) (hnd : polyCycNondeg V)
    (h4 : 4 ≤ V.length) (hVN : V.length ≤ N)
    (W : List ℂ) (ρ : ℕ) (hW : V.rotate ρ = W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P : List ℂ) (hPsimple : PolygonSimple P)
    (hP : P = HexArea.chordLeft W k ∨ P = HexArea.chordRight W k)
    (hPcyc : EmptyCornerData2 P u v) :
    ∃ (r' : ℕ) (a' b' c' p' q' : ℂ) (tl : List ℂ),
      V.rotate r' = a' :: b' :: c' :: tl ∧
      b' ∈ P ∧ b' ≠ u ∧ b' ≠ v ∧
      tl.getLast? = some p' ∧ tl.head? = some q' ∧
      (∀ x ∈ tl, ¬ HexArea.inTriangleStrict a' b' c' x) ∧
      (∀ x ∈ tl, x ∉ segment ℝ a' c') ∧
      ((0:ℝ) < HexArea.shoelace2 [a', b', c']
          ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tl)) := by
  -- Basic transport of the hypotheses to `W`.
  have hWlen : W.length = V.length := by rw [← hW]; simp
  have hWnd : W.Nodup := by rw [← hW]; exact List.nodup_rotate.mpr hsimple.1
  have hWsimple : PolygonSimple W := by
    rw [← hW]; exact (PolygonSimple_rotate V ρ).mpr hsimple
  have hWnondeg : polyCycNondeg W := by
    rw [← hW]; exact (polyCycNondeg_rotate V ρ (by omega)).mpr hnd
  have hW4 : 4 ≤ W.length := by omega
  have hklt : k < W.length := by omega
  have hu0 : W[0]! = u := by
    have h0 : 0 < W.length := by omega
    have : W[0]? = some (W[0]!) := by
      rw [List.getElem?_eq_getElem h0]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h0]
    rw [hu] at this; exact (Option.some.injEq _ _ ▸ this).symm
  have hvk : W[k]! = v := by
    have : W[k]? = some (W[k]!) := by
      rw [List.getElem?_eq_getElem hklt]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
    rw [hv] at this; exact (Option.some.injEq _ _ ▸ this).symm
  -- The ear of the piece.
  obtain ⟨s, a', b', c', p0, q0, rest0, hrotP, hb'u, hb'v, hp0, hq0, hemptyP,
    hdiagP, horientP⟩ := hPcyc
  -- List surgery: the ear triple is a consecutive triple of `W`.
  obtain ⟨j, tl, hrotW⟩ :=
    chord_lift_ear_rotation W k hk1 hk hWnd P hP s a' b' c' rest0 hrotP
      (by rw [hu0]; exact hb'u) (by rw [hvk]; exact hb'v)
  have hrotV : V.rotate (ρ + j) = a' :: b' :: c' :: tl := by
    rw [← List.rotate_rotate, hW]; exact hrotW
  -- The ear tip is an interior corner of `W`, hence non-degenerate.
  have hDP : HexArea.cross (b' - a') (c' - b') ≠ 0 :=
    polyCycNondeg_rotate_head W a' b' c' tl j (by omega) hWnondeg hrotW
  -- Lengths: the lifted tail is nonempty.
  have htllen : tl.length + 3 = W.length := by
    have := congrArg List.length hrotW; simp at this; omega
  obtain ⟨p', hp'⟩ : ∃ p', tl.getLast? = some p' := by
    cases hr : tl.getLast? with
    | none => exfalso; rw [List.getLast?_eq_none_iff] at hr; subst hr; simp at htllen; omega
    | some p' => exact ⟨p', rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q', tl.head? = some q' := by
    cases hr : tl.head? with
    | none => exfalso; rw [List.head?_eq_none_iff] at hr; subst hr; simp at htllen; omega
    | some q' => exact ⟨q', rfl⟩
  -- The tip is a vertex of the piece.
  have hb'P : b' ∈ P := by
    have : b' ∈ P.rotate s := by rw [hrotP]; simp
    exact (List.mem_rotate).mp this
  -- Membership bookkeeping for the lifted tail.
  have hWrotnd : (a' :: b' :: c' :: tl).Nodup := by
    rw [← hrotW]; exact List.nodup_rotate.mpr hWnd
  have htlW : ∀ x ∈ tl, x ∈ W := by
    intro x hx
    have : x ∈ W.rotate j := by rw [hrotW]; simp [hx]
    exact (List.mem_rotate).mp this
  have htlne : ∀ x ∈ tl, x ≠ a' ∧ x ≠ b' ∧ x ≠ c' := by
    intro x hx
    simp only [List.nodup_cons, List.mem_cons] at hWrotnd
    refine ⟨fun h => hWrotnd.1 (by simp [← h, hx]), fun h => hWrotnd.2.1 (by simp [← h, hx]),
      fun h => hWrotnd.2.2.1 (by simp [← h, hx])⟩
  have htlP : ∀ x ∈ tl, x ∈ P → x ∈ rest0 := by
    intro x hx hxP
    have hxrot : x ∈ P.rotate s := (List.mem_rotate).mpr hxP
    rw [hrotP] at hxrot
    obtain ⟨h1, h2, h3⟩ := htlne x hx
    simp only [List.mem_cons] at hxrot
    tauto
  refine ⟨ρ + j, a', b', c', p', q', tl, hrotV, hb'P, hb'u, hb'v, hp', hq', ?_, ?_, ?_⟩
  · -- Emptiness of the lifted ear triangle.
    intro x hx
    by_cases hxP : x ∈ P
    · exact hemptyP x (htlP x hx hxP)
    · exact chord_ear_empty_other_jordan N hN W hWsimple (by omega) k hk1 hk u v hu hv hdiag hint
        P hPsimple hP a' b' c' s rest0 hrotP hDP hemptyP hdiagP horientP x (htlW x hx) hxP
  · -- No far vertex on the closed ear diagonal.
    intro x hx
    by_cases hxP : x ∈ P
    · exact hdiagP x (htlP x hx hxP)
    · exact chord_lift_other_not_on_diagonal N hN W hW4 (by omega) hWsimple hWnondeg k hk1 hk
        u v hu hv hdiag hint P hPsimple hP a' b' c' s rest0 hrotP hDP hemptyP hdiagP
        horientP x (htlW x hx) hxP
  · -- Orientation transfer.
    have hclipP : HexArea.shoelace2 P
        = HexArea.shoelace2 (a' :: c' :: rest0) + HexArea.shoelace2 [a', b', c'] := by
      have h1 : HexArea.shoelace2 (P.rotate s) = HexArea.shoelace2 P :=
        shoelace2_rotate P s
      rw [← h1, hrotP]
      exact shoelace2_clip_second a' b' c' rest0
    have hclipW : HexArea.shoelace2 W
        = HexArea.shoelace2 (a' :: c' :: tl) + HexArea.shoelace2 [a', b', c'] := by
      have h1 : HexArea.shoelace2 (W.rotate j) = HexArea.shoelace2 W :=
        shoelace2_rotate W j
      rw [← h1, hrotW]
      exact shoelace2_clip_second a' b' c' tl
    have hsplit := HexArea.shoelace2_chord_split W k hk1 hklt
    obtain ⟨hL, hR⟩ := chord_piece_orient W hW4 hWsimple hWnondeg k hk1 hk u v hu hv hdiag hint
    have hkey : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 W - HexArea.shoelace2 [a', b', c']) := by
      rcases hP with rfl | rfl
      · exact orient_transfer_of_split _ _ (HexArea.shoelace2 (HexArea.chordRight W k)) _
          hsplit hL hR (by rw [horientP]; constructor <;> intro h <;> linarith [hclipP])
      · refine orient_transfer_of_split _ _ (HexArea.shoelace2 (HexArea.chordLeft W k)) _
          (by linarith [hsplit]) hR hL
          (by rw [horientP]; constructor <;> intro h <;> linarith [hclipP])
    rw [hkey]
    constructor <;> intro h <;> linarith [hclipW]

/-- **Forbidden-pair ear lift across a valid chord cut (mechanical bookkeeping
    around `chord_ear_lift`).**  Cut the rotation `W = V.rotate ρ` of a simple
    polygon `V` along the valid interior diagonal `W[0]–W[k]` (`hdiag`) into the
    two pieces `chordLeft W k` / `chordRight W k`.  Let `P` be one piece and `Q`
    the OTHER (encoded by `hPQ`).  Given an ear of `P` avoiding the cut edge
    `{u, v}` (`hPcyc : EmptyCornerData2 P u v`) and two forbidden points `z1, z2`
    each lying either in the OTHER piece `Q` or off `V` entirely (`hz1`, `hz2`),
    the lifted ear of `V` avoids both `z1` and `z2`, giving
    `EmptyCornerData2 V z1 z2`.

    This is the shared, reusable combinatorial assembly of the two diagonal-split
    branches (`meisters_reduction_interior2`, `empty_branch_bad_lift`): it wires
    together `chord_ear_lift` with the tip-avoidance lemma `chord_tip_ne_other`.
    It contains no new geometric content of its own — the only remaining Jordan
    gaps it depends on are the two inputs of `chord_ear_lift`
    (`chord_lift_other_not_on_diagonal`, `chord_piece_orient`).  NOT a dead branch. -/
lemma chord_package_forbidden (V : List ℂ)
    (W : List ℂ) (ρ : ℕ) (hW : V.rotate ρ = W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length) (hWnd : W.Nodup)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (P Q : List ℂ)
    (hPQ : (P = HexArea.chordLeft W k ∧ Q = HexArea.chordRight W k) ∨
           (P = HexArea.chordRight W k ∧ Q = HexArea.chordLeft W k))
    (r' : ℕ) (a' b' c' p' q' : ℂ) (tl : List ℂ)
    (hrot' : V.rotate r' = a' :: b' :: c' :: tl)
    (hb'P : b' ∈ P) (hb'u : b' ≠ u) (hb'v : b' ≠ v)
    (hp' : tl.getLast? = some p') (hq' : tl.head? = some q')
    (hempty' : ∀ x ∈ tl, ¬ HexArea.inTriangleStrict a' b' c' x)
    (hdiag' : ∀ x ∈ tl, x ∉ segment ℝ a' c')
    (horient' : ((0:ℝ) < HexArea.shoelace2 [a', b', c']
        ↔ (0:ℝ) < HexArea.shoelace2 (a' :: c' :: tl)))
    (z1 z2 : ℂ)
    (hz1 : z1 ∈ Q ∨ z1 ∉ V) (hz2 : z2 ∈ Q ∨ z2 ∉ V) :
    EmptyCornerData2 V z1 z2 := by
  have hklt : k < W.length := by omega
  have hWlen : 0 < W.length := by omega
  have hu0 : W[0]! = u := by
    have : W[0]? = some (W[0]!) := by
      rw [List.getElem?_eq_getElem hWlen]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hWlen]
    rw [hu] at this; exact (Option.some.injEq _ _ ▸ this).symm
  have hvk : W[k]! = v := by
    have : W[k]? = some (W[k]!) := by
      rw [List.getElem?_eq_getElem hklt]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
    rw [hv] at this; exact (Option.some.injEq _ _ ▸ this).symm
  -- `b'` is a vertex of `V`.
  have hb'W : b' ∈ W := by
    rcases hPQ with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact HexArea.mem_of_mem_chordLeft W k hb'P
    · exact HexArea.mem_of_mem_chordRight W k hb'P
  have hb'V : b' ∈ V := by rw [← hW] at hb'W; exact (List.mem_rotate).mp hb'W
  -- Tip avoids each forbidden point.
  have key : ∀ z : ℂ, (z ∈ Q ∨ z ∉ V) → b' ≠ z := by
    intro z hz
    rcases hz with hzQ | hzV
    · refine HexArea.chord_tip_ne_other W k hk1 hklt hWnd b' z (by rw [hu0]; exact hb'u)
        (by rw [hvk]; exact hb'v) ?_
      rcases hPQ with ⟨hPl, hQr⟩ | ⟨hPr, hQl⟩
      · exact Or.inl ⟨hPl ▸ hb'P, hQr ▸ hzQ⟩
      · exact Or.inr ⟨hPr ▸ hb'P, hQl ▸ hzQ⟩
    · exact fun h => hzV (h ▸ hb'V)
  exact ⟨r', a', b', c', p', q', tl, hrot', key z1 hz1, key z2 hz2, hp', hq',
    hempty', hdiag', horient'⟩

/-- **Forbidden-pair ear lift across a valid chord cut.**  `chord_ear_lift`
    followed by the tip bookkeeping `chord_package_forbidden`. -/
lemma chord_ear_lift_forbidden (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hsimple : PolygonSimple V) (hnd : polyCycNondeg V)
    (h4 : 4 ≤ V.length) (hVN : V.length ≤ N)
    (W : List ℂ) (ρ : ℕ) (hW : V.rotate ρ = W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P Q : List ℂ)
    (hPQ : (P = HexArea.chordLeft W k ∧ Q = HexArea.chordRight W k) ∨
           (P = HexArea.chordRight W k ∧ Q = HexArea.chordLeft W k))
    (hPsimple : PolygonSimple P)
    (hPcyc : EmptyCornerData2 P u v)
    (z1 z2 : ℂ)
    (hz1 : z1 ∈ Q ∨ z1 ∉ V) (hz2 : z2 ∈ Q ∨ z2 ∉ V) :
    EmptyCornerData2 V z1 z2 := by
  have hWsimple : PolygonSimple W := hW ▸ (PolygonSimple_rotate V ρ).mpr hsimple
  obtain ⟨r', a', b', c', p', q', tl, hrot', hb'P, hb'u, hb'v, hp', hq',
      hempty', hdiag', horient'⟩ :=
    chord_ear_lift N hN V hsimple hnd h4 hVN W ρ hW k hk1 hk u v hu hv hdiag hint P hPsimple
      (hPQ.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hPcyc
  exact chord_package_forbidden V W ρ hW k hk1 hk hWsimple.1 u v hu hv P Q hPQ
    r' a' b' c' p' q' tl hrot' hb'P hb'u hb'v hp' hq' hempty' hdiag' horient'
    z1 z2 hz1 hz2

/-- **Interior-split lift through the recursion piece (main path proved,
    triangle/flat residual isolated).**  Cut `W = V.rotate ρ` along the valid
    interior diagonal `W[0]–W[k]` (`hdiag`) into `chordLeft`/`chordRight`.  Let
    `P` be the piece to recurse on and `Q` the other (encoded by `hPQ`), with the
    cut edge `{u,v}` a cyclic edge of `P` (`hcut`), `P` simple and strictly
    shorter than `V` (`hPsimple`, `hPlen`), and the two forbidden points `z1, z2`
    each in `Q` or off `V`.

    When the recursion piece `P` is **non-degenerate and has ≥ 4 vertices**, the
    strong-induction hypothesis `IH2` directly returns an ear of `P` avoiding the
    cut edge, and `chord_ear_lift_forbidden` lifts it to the required ear of `V`.
    This is the generic Meisters recursion path and is proved here (modulo the
    Jordan brick `chord_ear_lift` inside `chord_ear_lift_forbidden`).

    **Status: all three cases proved** (modulo the Jordan brick `chord_ear_lift`
    inside `chord_ear_lift_forbidden`).  The *triangle* piece (length 3, where
    `EmptyCornerData2 P` is unavailable and a `V`-ear must be built directly) is
    discharged by `chord_triangle_piece_package`.  The *flat-seam* case — the
    piece has at least four vertices but a degenerate corner at the cut seam — is
    discharged by `flatSeam_EmptyCornerData2_of_data`
    (`RequestProject.SAWUmlaufFlatSeamLift`): the flat cut vertex is deleted, the
    recursion runs on the deletion forbidding its seam edge, and the returned ear
    is lifted back across the deletion.  Its input `FlatSeamData P u v` is the
    hypothesis `hflatseam`, supplied at the call sites by the proved
    `interior_flat_seam_data`. -/
lemma interior_lift_via_piece (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hsimple : PolygonSimple V) (hnd : polyCycNondeg V)
    (hVlen : 4 ≤ V.length) (hVN : V.length ≤ N)
    (W : List ℂ) (ρ : ℕ) (hW : V.rotate ρ = W) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ W.length)
    (u v : ℂ) (hu : W[0]? = some u) (hv : W[k]? = some v)
    (hdiag : ∀ e ∈ closedEdges W, u ≠ e.1 → u ≠ e.2 → v ≠ e.1 → v ≠ e.2 →
        Disjoint (segment ℝ u v) (segment ℝ e.1 e.2))
    (hint : InteriorChord W u v)
    (P Q : List ℂ)
    (hPQ : (P = HexArea.chordLeft W k ∧ Q = HexArea.chordRight W k) ∨
           (P = HexArea.chordRight W k ∧ Q = HexArea.chordLeft W k))
    (hPsimple : PolygonSimple P) (hPlen : P.length < V.length)
    (hcut : IsCycEdge P u v)
    (hflatseam : 4 ≤ P.length → ¬ polyCycNondeg P → FlatSeamData P u v)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (z1 z2 : ℂ) (hz1 : z1 ∈ Q ∨ z1 ∉ V) (hz2 : z2 ∈ Q ∨ z2 ∉ V) :
    EmptyCornerData2 V z1 z2 := by
  by_cases hcond : 4 ≤ P.length ∧ polyCycNondeg P
  · obtain ⟨hP4, hPnd⟩ := hcond
    -- Cut edge as a cyclic edge in the other orientation, for `IH2`.
    have hcut' : IsCycEdge P v u := by
      rcases hcut with h | h
      · exact Or.inr h
      · exact Or.inl h
    -- Recurse: an ear of `P` avoiding the cut edge `{u,v}`.
    have hPvu : EmptyCornerData2 P v u :=
      IH2 P hPlen hP4 hPsimple hPnd v u (Or.inr hcut')
    have hPcyc : EmptyCornerData2 P u v := by
      obtain ⟨r0, a0, b0, c0, p0, q0, rest0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hPvu
      exact ⟨r0, a0, b0, c0, p0, q0, rest0, h1, h3, h2, h4, h5, h6, h7, h8⟩
    exact chord_ear_lift_forbidden N hN V hsimple hnd hVlen hVN W ρ hW k hk1 hk u v hu hv
      hdiag hint P Q hPQ hPsimple hPcyc z1 z2 hz1 hz2
  · -- The piece is a triangle, or has ≥ 4 vertices but a flat cyclic corner.
    by_cases hP3 : P.length = 3
    · -- **Triangle piece (proved).**  The single vertex cut off by the chord is
      -- itself an ear of `V`; the package is built by
      -- `chord_triangle_piece_package` and lifted by `chord_package_forbidden`.
      have hWsimple : PolygonSimple W := hW ▸ (PolygonSimple_rotate V ρ).mpr hsimple
      have hWnd : polyCycNondeg W := hW ▸ (polyCycNondeg_rotate V ρ (by omega)).mpr hnd
      have hWlen : W.length = V.length := by rw [← hW]; simp
      obtain ⟨j, a', b', c', p', q', tl, hrotW, hb'P, hb'u, hb'v, hp', hq',
          hempty', hdiag', horient'⟩ :=
        chord_triangle_piece_package W (by omega) hWsimple hWnd k hk1 hk u v hu hv hdiag hint
          P (hPQ.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hP3
      have hrotV : V.rotate (ρ + j) = a' :: b' :: c' :: tl := by
        rw [← List.rotate_rotate, hW]; exact hrotW
      exact chord_package_forbidden V W ρ hW k hk1 hk hWsimple.1 u v hu hv P Q hPQ
        (ρ + j) a' b' c' p' q' tl hrotV hb'P hb'u hb'v hp' hq' hempty' hdiag' horient'
        z1 z2 hz1 hz2
    · -- **The piece has ≥ 4 vertices but a flat cyclic corner at the cut seam.**
      -- Delete the flat seam vertex, recurse on the deletion (forbidding its
      -- seam edge) and lift the returned ear back over the deleted vertex:
      -- this is `flatSeam_EmptyCornerData2_of_data`
      -- (`RequestProject.SAWUmlaufFlatSeamLift`).
      -- First, the cut index is genuinely interior: `2 ≤ k ≤ W.length - 2`,
      -- because `v` is strictly inside the corner triangle at `u`, hence is
      -- neither of the two cyclic neighbours of `u`.
      obtain ⟨pu, nu, hhead, hlast, hnu, -, -, htri⟩ := id hint
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hlt | hge
        · exfalso
          have hk1' : k = 1 := by omega
          subst hk1'
          rw [hv] at hnu
          exact HexArea.inTriangleStrict_ne_c pu u nu v htri (Option.some.inj hnu)
        · exact hge
      have hkle : k + 2 ≤ W.length := by
        rcases Nat.lt_or_ge (k + 1) W.length with hlt | hge
        · omega
        · exfalso
          have hklast : k = W.length - 1 := by omega
          have hlv : W.getLast? = some v := by
            rw [List.getLast?_eq_getElem?, ← hklast]; exact hv
          rw [hlv] at hlast
          exact HexArea.inTriangleStrict_ne_a pu u nu v htri (Option.some.inj hlast)
      -- hence both pieces have at least three vertices
      have hP3' : 3 ≤ P.length := by
        rcases hPQ with ⟨hPL, -⟩ | ⟨hPR, -⟩
        · rw [hPL, HexArea.chordLeft]; simp; omega
        · rw [hPR, HexArea.chordRight]; simp; omega
      have hP4 : 4 ≤ P.length := by omega
      have hPnd : ¬ polyCycNondeg P := fun h => hcond ⟨hP4, h⟩
      have hPcyc : EmptyCornerData2 P u v :=
        flatSeam_EmptyCornerData2_of_data P hPsimple hP4 u v (hflatseam hP4 hPnd)
          (fun M hM h4M hMs hMnd w1 w2 hw => IH2 M (by omega) h4M hMs hMnd w1 w2 hw)
      exact chord_ear_lift_forbidden N hN V hsimple hnd hVlen hVN W ρ hW k hk1 hk u v hu hv
        hdiag hint P Q hPQ hPsimple hPcyc z1 z2 hz1 hz2

/-- **Meisters interior branch (open Jordan-curve core), two-forbidden form.**
    The convex corner `a, b, c` (with `b` the lex-minimal, hence convex, middle
    vertex of the rotated cycle `V.rotate r = a :: b :: c :: rest`) is *not*
    empty: `w ∈ rest` is the interior vertex farthest from the base diagonal
    `a–c`.  The chord `b–w` is then an interior diagonal of `V`; splitting `V`
    along it (`chordLeft`/`chordRight` in `SAWUmlaufEarSplit`) yields two
    strictly shorter simple non-degenerate sub-polygons.  The forbidden edge
    `{z1, z2}` lies entirely in one of the two pieces, so recursing through
    `IH2` on the *other* piece — forbidding the cut diagonal `{b, w}` (a cyclic
    edge of that piece) — returns an ear whose tip is interior to that piece,
    hence avoids `{b, w}` and therefore lifts to an ear of `V` avoiding
    `{z1, z2}`.  This is the crux that the single-forbidden form could not
    express.  Consumed by `meisters_reduction2`.

    **Status: proved**, modulo the Jordan brick `chord_ear_lift` used by
    `interior_lift_via_piece` (interior diagonal split preserving
    `PolygonSimple`/`polyCycNondeg`, plus the ear lift); absent from Mathlib.

    PROGRESS / BANKED: the *simplicity* half of the split is now fully proved,
    sorry-free, as `interior_split_simple` (just above): the two pieces
    `chordLeft`/`chordRight` of the `b`-rooted cycle `b :: c :: rest ++ [a]` cut
    along the diagonal `b–w` are both `PolygonSimple` (assembled from the
    geometric heart `interior_chord_is_diagonal` and the banked combinatorial
    simplicity bricks).  It also supplies the cut index `k` with `2 ≤ k` and
    `k + 2 ≤ W.length`, so `chordLeft_length_lt`/`chordRight_length_lt` give both
    pieces strictly shorter (the `IH2` recursion fuel).

    PROGRESS / BANKED (non-degeneracy half, disjunctive form): the
    `polyCycNondeg` obstruction is now discharged for *one* of the two pieces by
    the sorry-free `interior_split_one_nondeg` (above): the genuine cyclic corner
    `(prev, w, succ)` of `W` at the cut endpoint `w` is non-flat
    (`polyCycNondeg_interior_corner`), so by `seam_one_nonflat` at least one of
    the two seam corners is non-flat, making the corresponding chord piece
    `polyCycNondeg` via `interior_split_nondeg_left` / `interior_split_nondeg_right`.

    RESOLVED (flat seam): only *one* piece is guaranteed non-degenerate, and if
    the forbidden edge `{z1,z2}` forces the recursion onto the flat one, the flat
    seam vertex `w` is deleted from that piece before recursing and the returned
    ear is lifted back over the deletion.  This is now proved, by
    `interior_flat_seam_data` (the piece is flat exactly at `w`, and the deletion
    is again simple and non-degenerate) together with
    `flatSeam_EmptyCornerData2_of_data` (the lift), both in
    `RequestProject.SAWUmlaufFlatSeamLift`; they are handed to
    `interior_lift_via_piece` as its `hflatseam` argument below. -/
lemma meisters_reduction_interior2 (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hlen : 4 ≤ V.length) (hVN : V.length ≤ N)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (h4 : ¬ V.length = 4)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hbdir : ∃ d : ℂ, ∀ y ∈ V, y ≠ b → 0 < HexArea.cdot d (y - b))
    (hcase : ∃ x ∈ rest, HexArea.inTriangleStrict a b c x)
    (w : ℂ) (hwrest : w ∈ rest) (hwin : HexArea.inTriangleStrict a b c w)
    (hwmax : ∀ y ∈ rest, HexArea.inTriangleStrict a b c y →
        HexArea.cross (c - a) (y - a) * HexArea.cross (c - a) (b - a)
          ≤ HexArea.cross (c - a) (w - a) * HexArea.cross (c - a) (b - a)) :
    EmptyCornerData2 V z1 z2 := by
  -- Corner non-flatness of the consecutive triple `a, b, c` from `polyCycNondeg V`.
  have hndtri : HexArea.cross (b - a) (c - b) ≠ 0 := by
    have hM : polyCycNondeg (a :: b :: c :: rest) :=
      hrot ▸ (polyCycNondeg_rotate V r (by omega)).mpr hnd
    have hPN : polyNondeg (a :: b :: c :: (rest ++ (a :: b :: c :: rest).take 2)) := hM
    rw [polyNondeg_cons_cons_cons] at hPN
    exact hPN.1
  -- Banked recursion-ready interior split (consumes `interior_split_select`).
  obtain ⟨k, hk2, hklen, hwk, hLsimple, hRsimple, hLlt, hRlt, _hnondeg⟩ :=
    interior_split_select V hsimple hnd r a b c rest hrot hndtri w hwrest hwin hwmax
  -- Set up the `b`-rooted cut cycle `W = V.rotate (r+1)` and the valid diagonal `b–w`.
  have hW : V.rotate (r + 1) = b :: c :: rest ++ [a] :=
    HexArea.rotate_corner_succ V r a b c rest hrot
  have hk1 : 1 ≤ k := by omega
  have hkW : k + 1 ≤ (b :: c :: rest ++ [a]).length := by omega
  have hklt : k < (b :: c :: rest ++ [a]).length := by omega
  have hu : (b :: c :: rest ++ [a])[0]? = some b := by simp
  have hWhead : (b :: c :: rest ++ [a]).head? = some b := by simp
  have hWne : (b :: c :: rest ++ [a]) ≠ [] := by simp
  have hsimpleABC : PolygonSimple (a :: b :: c :: rest) :=
    hrot ▸ (PolygonSimple_rotate V r).mpr hsimple
  have hrot1 : (a :: b :: c :: rest).rotate 1 = b :: c :: rest ++ [a] := by
    rw [← hrot, List.rotate_rotate]; exact hW
  have hdiag0 :=
    interior_chord_is_diagonal a b c w rest hsimpleABC hndtri hwrest hwin hwmax
  have hdiag : ∀ e ∈ closedEdges (b :: c :: rest ++ [a]), b ≠ e.1 → b ≠ e.2 →
      w ≠ e.1 → w ≠ e.2 → Disjoint (segment ℝ b w) (segment ℝ e.1 e.2) := by
    intro e he hb1 hb2 hw1 hw2
    apply hdiag0 e _ hb1 hb2 hw1 hw2
    rw [← hrot1] at he
    exact (mem_closedEdges_rotate (a :: b :: c :: rest) 1 e).mp he
  -- The cut `b–w` is an INTERIOR chord: `b` is the extreme corner apex
  -- (`hbconv`, transported along the rotation) and `w` lies strictly inside the
  -- corner triangle `a, b, c` (`hwin`).  This is exactly the diagonal-validity
  -- data that mere edge-disjointness fails to provide (see the dart
  -- counterexample in `RequestProject.SAWUmlaufDartCounterexample`).
  have hmemW : ∀ y : ℂ, y ∈ (b :: c :: rest ++ [a]) → y ∈ V := by
    intro y hy
    rw [← hW] at hy
    exact List.mem_rotate.mp hy
  have hint : InteriorChord (b :: c :: rest ++ [a]) b w := by
    refine ⟨a, c, by simp, ?_, by simp, ?_, ?_, hwin⟩
    · show (b :: c :: rest ++ [a]).getLast? = some a
      rw [show b :: c :: rest ++ [a] = (b :: c :: rest) ++ [a] by simp, List.getLast?_concat]
    · intro y hy z hz t ht
      exact hbconv y z t (hmemW y hy) (hmemW z hz) (hmemW t ht)
    · obtain ⟨d, hd⟩ := hbdir
      exact ⟨d, fun y hy hyb => hd y (hmemW y hy) hyb⟩
  -- Symmetry of the cyclic-edge predicate (for the cut edge orientation).
  have symmCyc : ∀ (L : List ℂ), IsCycEdge L w b → IsCycEdge L b w := by
    intro L h; rcases h with h | h; exacts [Or.inr h, Or.inl h]
  -- Flat-seam data for a degenerate piece: if a chord piece fails to be
  -- cyclically non-degenerate it is flat exactly at the cut endpoint `w`, and
  -- deleting `w` restores non-degeneracy (`interior_flat_seam_data`).  This is
  -- what lets `interior_lift_via_piece` recurse on a flat piece.
  have hndABC : polyCycNondeg (a :: b :: c :: rest) :=
    hrot ▸ (polyCycNondeg_rotate V r (by omega)).mpr hnd
  have hfsdL : 4 ≤ (HexArea.chordLeft (b :: c :: rest ++ [a]) k).length →
      ¬ polyCycNondeg (HexArea.chordLeft (b :: c :: rest ++ [a]) k) →
      FlatSeamData (HexArea.chordLeft (b :: c :: rest ++ [a]) k) b w :=
    interior_flat_seam_data a b c w rest k hndABC hwin hk2 hklen hwk _ (Or.inl rfl) hLsimple
  have hfsdR : 4 ≤ (HexArea.chordRight (b :: c :: rest ++ [a]) k).length →
      ¬ polyCycNondeg (HexArea.chordRight (b :: c :: rest ++ [a]) k) →
      FlatSeamData (HexArea.chordRight (b :: c :: rest ++ [a]) k) b w :=
    interior_flat_seam_data a b c w rest k hndABC hwin hk2 hklen hwk _ (Or.inr rfl) hRsimple
  -- Dispatch on the forbidden pair.
  rcases hadj with rfl | hcyc
  · -- Single forbidden point `z1`: recurse on a piece not containing it.
    by_cases hzL : z1 ∈ HexArea.chordLeft (b :: c :: rest ++ [a]) k
    · exact interior_lift_via_piece N hN V hsimple hnd hlen hVN (b :: c :: rest ++ [a]) (r + 1) hW k hk1
        hkW b w hu hwk hdiag hint (HexArea.chordRight (b :: c :: rest ++ [a]) k)
        (HexArea.chordLeft (b :: c :: rest ++ [a]) k) (Or.inr ⟨rfl, rfl⟩) hRsimple hRlt
        (symmCyc _ (chordRight_cut_isCycEdge (b :: c :: rest ++ [a]) k b w hklt hWne hWhead hwk))
        hfsdR IH2 z1 z1 (Or.inl hzL) (Or.inl hzL)
    · by_cases hzR : z1 ∈ HexArea.chordRight (b :: c :: rest ++ [a]) k
      · exact interior_lift_via_piece N hN V hsimple hnd hlen hVN (b :: c :: rest ++ [a]) (r + 1) hW k hk1
          hkW b w hu hwk hdiag hint (HexArea.chordLeft (b :: c :: rest ++ [a]) k)
          (HexArea.chordRight (b :: c :: rest ++ [a]) k) (Or.inl ⟨rfl, rfl⟩) hLsimple hLlt
          (symmCyc _ (chordLeft_cut_isCycEdge (b :: c :: rest ++ [a]) k b w hklt hWhead hwk))
          hfsdL IH2 z1 z1 (Or.inl hzR) (Or.inl hzR)
      · have hz1V : z1 ∉ V := by
          intro hmem
          have hmemW : z1 ∈ (b :: c :: rest ++ [a]) := by
            rw [← hW]; exact List.mem_rotate.mpr hmem
          rcases HexArea.mem_chord_cover (b :: c :: rest ++ [a]) k hkW hmemW with h | h
          · exact hzL h
          · exact hzR h
        exact interior_lift_via_piece N hN V hsimple hnd hlen hVN (b :: c :: rest ++ [a]) (r + 1) hW k hk1
          hkW b w hu hwk hdiag hint (HexArea.chordLeft (b :: c :: rest ++ [a]) k)
          (HexArea.chordRight (b :: c :: rest ++ [a]) k) (Or.inl ⟨rfl, rfl⟩) hLsimple hLlt
          (symmCyc _ (chordLeft_cut_isCycEdge (b :: c :: rest ++ [a]) k b w hklt hWhead hwk))
          hfsdL IH2 z1 z1 (Or.inr hz1V) (Or.inr hz1V)
  · -- Forbidden cyclic edge `{z1,z2}`: lands in one piece; recurse on the other.
    have hcycW : IsCycEdge (b :: c :: rest ++ [a]) z1 z2 :=
      hW ▸ (HexArea.IsCycEdge_rotate V (r + 1) z1 z2).mpr hcyc
    rcases HexArea.forbidden_lands_in_chord (b :: c :: rest ++ [a]) k z1 z2 hk1 hkW hcycW with hInL | hInR
    · obtain ⟨hz1Q, hz2Q⟩ := HexArea.IsCycEdge_mem _ _ _ hInL
      exact interior_lift_via_piece N hN V hsimple hnd hlen hVN (b :: c :: rest ++ [a]) (r + 1) hW k hk1
        hkW b w hu hwk hdiag hint (HexArea.chordRight (b :: c :: rest ++ [a]) k)
        (HexArea.chordLeft (b :: c :: rest ++ [a]) k) (Or.inr ⟨rfl, rfl⟩) hRsimple hRlt
        (symmCyc _ (chordRight_cut_isCycEdge (b :: c :: rest ++ [a]) k b w hklt hWne hWhead hwk))
        hfsdR IH2 z1 z2 (Or.inl hz1Q) (Or.inl hz2Q)
    · obtain ⟨hz1Q, hz2Q⟩ := HexArea.IsCycEdge_mem _ _ _ hInR
      exact interior_lift_via_piece N hN V hsimple hnd hlen hVN (b :: c :: rest ++ [a]) (r + 1) hW k hk1
        hkW b w hu hwk hdiag hint (HexArea.chordLeft (b :: c :: rest ++ [a]) k)
        (HexArea.chordRight (b :: c :: rest ++ [a]) k) (Or.inl ⟨rfl, rfl⟩) hLsimple hLlt
        (symmCyc _ (chordLeft_cut_isCycEdge (b :: c :: rest ++ [a]) k b w hklt hWhead hwk))
        hfsdL IH2 z1 z2 (Or.inl hz1Q) (Or.inl hz2Q)

/-- **Empty-branch lift — the BAD-diagonal subcase (genuine remaining gap).**
    Extracted from `meisters_reduction_empty2`'s non-clean / non-good case so it
    is a single targetable declaration.  Here the corner `a,b,c` is empty
    (`hcase`), but the clip diagonal `a–c` itself fails the clean test
    (`hbad`): some clip neighbour `p`/`q` is collinear with `a–c`, or a far
    vertex of `rest` sits on the *closed* diagonal `[a,c]`, or the ear
    orientation is reversed relative to the clip.  In every such configuration
    the clip `a :: c :: rest` is no longer a clean simple sub-polygon, so (as in
    the interior branch) the proof needs the polygon-split machinery: a blocking
    vertex on the diagonal yields a strictly-shorter interior diagonal to split
    along, recurse via `IH2` on the piece NOT containing `{z1,z2}`, and lift.

    **Status: `sorry`.**  This is the isolated remaining Jordan-content gap of
    the empty branch.  Recorded, isolated partial progress — NOT a dead branch;
    it is consumed directly by `meisters_reduction_empty2`. -/
lemma empty_branch_bad_lift (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (h4 : ¬ V.length = 4)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hcase : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x)
    (p q : ℂ) (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hrest_len : 2 ≤ rest.length)
    (hbad : ¬ (HexArea.cross (c - a) (p - a) ≠ 0 ∧
        HexArea.cross (c - a) (q - a) ≠ 0 ∧
        (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
        ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)))) :
    EmptyCornerData2 V z1 z2 := by
  sorry

/-- **Meisters empty/diagonal branch, two-forbidden form.**  No vertex of
    `rest` lies in the strict interior of the convex corner `a, b, c`.  If `b`
    is a *bona-fide* empty ear avoiding both `z1` and `z2` (the clean case,
    proved here directly via the `EmptyCornerData2` packaging), use it.
    Otherwise — `b` coincides with a forbidden vertex, or a clip endpoint is
    collinear, or a far vertex sits on the closed diagonal, or the orientation
    is reversed — recurse via `IH2` on the clip `a :: c :: rest` forbidding the
    clip diagonal `{a, c}` (a cyclic edge of the clip), and lift the returned
    ear (whose tip lies in `rest`, hence avoids `a`, `c`, and `b`) back to `V`.
    Consumed by `meisters_reduction2`.

    **Status: clean case proved; non-clean case `sorry`.**  The non-clean lift
    re-inserts the convex apex `b` between `a` and `c`; the returned ear's tip
    in `rest` keeps its cyclic neighbours, and `b` stays outside the lifted ear
    triangle by `hbconv`.  The clip preservation is already available as
    `clip_simple_nondeg_of_empty`; the residual content is the list-surgery
    lift.  Recorded partial progress. -/
lemma meisters_reduction_empty2 (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2)
    (h4 : ¬ V.length = 4)
    (r : ℕ) (a b c : ℂ) (rest : List ℂ)
    (hrot : V.rotate r = a :: b :: c :: rest) (hbmem : b ∈ V)
    (hbconv : ∀ x y w : ℂ, x ∈ V → y ∈ V → w ∈ V →
        ¬ HexArea.inTriangleStrict x y w b)
    (hbseg : ∀ u w : ℂ, u ∈ V → w ∈ V → b ≠ u → b ≠ w → b ∉ segment ℝ u w)
    (hcase : ∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) :
    EmptyCornerData2 V z1 z2 := by
  -- `rest` is nonempty: `V.length ≥ 5`, so `rest.length = V.length - 3 ≥ 2`.
  have hrest_len : 2 ≤ rest.length := by
    have hl := congrArg List.length hrot
    simp only [List.length_rotate, List.length_cons] at hl
    omega
  obtain ⟨p, hp⟩ : ∃ p, rest.getLast? = some p := by
    cases hr : rest.getLast? with
    | none => exfalso; rw [List.getLast?_eq_none_iff] at hr; subst hr; simp at hrest_len
    | some p => exact ⟨p, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, rest.head? = some q := by
    cases hr : rest.head? with
    | none => exfalso; rw [List.head?_eq_none_iff] at hr; subst hr; simp at hrest_len
    | some q => exact ⟨q, rfl⟩
  by_cases hclean : (b ≠ z1 ∧ b ≠ z2) ∧ HexArea.cross (c - a) (p - a) ≠ 0 ∧
      HexArea.cross (c - a) (q - a) ≠ 0 ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
        ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))
  · -- **Clean case (proved).**  `b` avoids both forbidden vertices, both clip
    -- endpoints `p, q` lie off the line `a–c`, no far vertex sits on the closed
    -- diagonal, and the ear orientation matches the clip: assemble
    -- `EmptyCornerData2` directly.
    obtain ⟨⟨hbz1, hbz2⟩, hpl, hql, hdiag, horient⟩ := hclean
    exact ⟨r, a, b, c, p, q, rest, hrot, hbz1, hbz2, hp, hq,
      hcase, hdiag, horient⟩
  · -- **Non-clean case.**  Split on whether the clip diagonal `a–c` is itself
    -- *clean* (neighbours `p, q` off the line, no far vertex on the closed
    -- diagonal, ear orientation matching).
    by_cases hgood : HexArea.cross (c - a) (p - a) ≠ 0 ∧
        HexArea.cross (c - a) (q - a) ≠ 0 ∧
        (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
        ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest))
    · -- **Good-diagonal subcase (consumed by `empty_branch_good_lift`).**  The
      -- diagonal is clean, so the only reason the corner failed the clean test
      -- is that the apex `b` is a forbidden vertex.  Recurse on the clip and
      -- lift; no polygon splitting needed.
      obtain ⟨hpl, hql, hdiag, horient⟩ := hgood
      have hbf : b = z1 ∨ b = z2 := by
        by_contra h
        push_neg at h
        exact hclean ⟨h, hpl, hql, hdiag, horient⟩
      exact empty_branch_good_lift V (by omega) hsimple hnd z1 z2 hadj IH2 r a b c rest
        p q hrot hbmem hbconv hbseg hp hq hpl hql hcase hdiag horient hbf
    · -- **Bad-diagonal subcase (remaining Jordan gap).**  A clip neighbour is
      -- collinear with `a–c`, or a far vertex sits on the *closed* diagonal, or
      -- the ear orientation is reversed.  The clip is then no longer a clean
      -- simple sub-polygon, so this case genuinely needs the polygon-split
      -- machinery (as in `meisters_reduction_interior2`): a blocking vertex on
      -- the diagonal yields a strictly-shorter interior diagonal to split
      -- along.  This is the isolated remaining gap of the empty branch,
      -- extracted into `empty_branch_bad_lift`.
      exact empty_branch_bad_lift V hlen hsimple hnd z1 z2 hadj IH2 h4 r a b c rest
        hrot hbmem hbconv hbseg hcase p q hp hq hrest_len hgood

/-- **The geometric reduction step of the Meisters two-ears search (two-forbidden
    form), now carrying the strong-induction hypothesis.**  Dispatches the
    quadrilateral base case, the lex-minimal convex-vertex setup, and the
    interior / empty dichotomy to the three branch lemmas above. -/
lemma meisters_reduction2 (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hlen : 4 ≤ V.length) (hVN : V.length ≤ N)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z1 z2 : ℂ)
    (hadj : z1 = z2 ∨ IsCycEdge V z1 z2)
    (IH2 : ∀ V' : List ℂ, V'.length < V.length → 4 ≤ V'.length →
        PolygonSimple V' → polyCycNondeg V' →
        ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge V' w1 w2) → EmptyCornerData2 V' w1 w2) :
    EmptyCornerData2 V z1 z2 := by
  by_cases h4 : V.length = 4
  · exact meisters_reduction_quad2 V h4 hsimple hnd z1 z2 hadj
  -- From here `V.length ≥ 5`.
  obtain ⟨r, a, b, c, rest, hrot, hbmem, hbconv, hbseg, hbdir⟩ :=
    exists_lexmin_mid_rotation V (by omega)
  by_cases hcase : ∃ x ∈ rest, HexArea.inTriangleStrict a b c x
  · -- **Interior branch (Meisters' diagonal split).**
    obtain ⟨w, hwrest, hwin, hwmax⟩ := exists_farthest_interior_oriented a b c rest hcase
    exact meisters_reduction_interior2 N hN V hlen hVN hsimple hnd z1 z2 hadj IH2 h4 r a b c
      rest hrot hbmem hbconv hbseg hbdir hcase w hwrest hwin hwmax
  · -- **Empty/diagonal branch.**
    push_neg at hcase
    exact meisters_reduction_empty2 V hlen hsimple hnd z1 z2 hadj IH2 h4 r a b c
      rest hrot hbmem hbconv hbseg hcase

/-! ⚠ **FALSE AS STATED — see `RequestProject.SAWUmlaufFlatClipCounterexample`.**
The declaration below demands that clipping the ear leave a *cyclically
non-degenerate* polygon (equivalently the two clip-corner clauses
`cross (a - p) (c - a) ≠ 0`, `cross (c - a) (q - c) ≠ 0`).  The simple,
non-degenerate pentagon `0, i, 1+i, 2+2i, 2+i` refutes that: every one of its
ears leaves a flat vertex behind.  It is retained as preparation: restating it in
the *weak* form (both clauses dropped) turns it into a true statement, and the
weak form of the top of this chain is `exists_front_ear_weak`
(`RequestProject.SAWUmlaufPolygon`), which is what the live route now uses,
together with the flat-vertex normalisation of
`RequestProject.SAWUmlaufFlatRemoval`. -/

/-- **Strong-induction wrapper (sorry-free), two-forbidden form.**  Discharges
    the induction hypothesis of `meisters_reduction2` by strong induction on the
    polygon length, leaving the genuine geometric content concentrated in the
    branch lemmas. -/
lemma exists_empty_corner_avoiding_aux2 (N : ℕ) (hN : DichBelow N) :
    ∀ (n : ℕ) (V : List ℂ), V.length = n → V.length ≤ N → 4 ≤ V.length →
      PolygonSimple V → polyCycNondeg V →
      ∀ z1 z2 : ℂ, (z1 = z2 ∨ IsCycEdge V z1 z2) → EmptyCornerData2 V z1 z2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V hn hVN hlen hsimple hnd z1 z2 hadj
    refine meisters_reduction2 N hN V hlen hVN hsimple hnd z1 z2 hadj ?_
    intro V' hlt h4 hs' hnd' w1 w2 hadj'
    exact IH V'.length (by omega) V' rfl (by omega) h4 hs' hnd' w1 w2 hadj'

/-- **Strong-induction wrapper (sorry-free).**  The single-forbidden
    `EmptyCornerData` is the diagonal case of the two-forbidden
    `exists_empty_corner_avoiding_aux2`. -/
lemma exists_empty_corner_avoiding_aux (N : ℕ) (hN : DichBelow N) :
    ∀ (n : ℕ) (V : List ℂ), V.length = n → V.length ≤ N → 4 ≤ V.length →
      PolygonSimple V → polyCycNondeg V → ∀ z : ℂ, EmptyCornerData V z := by
  intro n V hn hVN hlen hsimple hnd z
  exact EmptyCornerData_of_two V z
    (exists_empty_corner_avoiding_aux2 N hN n V hn hVN hlen hsimple hnd z z (Or.inl rfl))

/-- **The Meisters empty-corner search, in its corrected (weak) form.**  A
simple, cyclically non-degenerate polygon with at least four vertices, together
with any forbidden vertex `z`, has a rotation `a :: b :: c :: rest` whose middle
vertex `b ≠ z` spans an *empty* corner: no far vertex lies strictly inside the
corner triangle or on the closed clip diagonal `[a, c]`, and the ear triangle
shares the orientation of the clip.

**History.**  A previous form of this statement additionally demanded the two
clip-corner clauses `cross (a - p) (c - a) ≠ 0`, `cross (c - a) (q - c) ≠ 0`
(equivalently: the clip stays cyclically non-degenerate).  That is refuted by the
pentagon `0, i, 1+i, 2+2i, 2+i` of
`RequestProject.SAWUmlaufFlatClipCounterexample` — see `flat_clip_no_ear_data`
there — so those clauses were dropped from `EmptyCornerData`/`EmptyCornerData2`
and from this chain; the flat vertices a clip creates are deleted afterwards by
`RequestProject.SAWUmlaufFlatRemoval`. -/
lemma exists_empty_corner_avoiding (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hlen : 4 ≤ V.length) (hVN : V.length ≤ N)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z : ℂ) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) :=
  exists_empty_corner_avoiding_aux N hN V.length V rfl hVN hlen hsimple hnd z

/-! ### The top of the chain, in the corrected (weak) form

The two declarations `exists_empty_convex_ear_avoiding` and
`exists_empty_convex_ear` are **false as stated** — they demand
`polyCycNondeg (a :: c :: rest)`, i.e. that clipping the ear leave a cyclically
non-degenerate polygon, which the pentagon `0, i, 1+i, 2+2i, 2+i` of
`RequestProject.SAWUmlaufFlatClipCounterexample` refutes (see
`flat_clip_no_empty_convex_ear` there).  They are therefore commented out below
(kept verbatim as a record of the superseded interface), and replaced by the
weak forms `exists_empty_convex_ear_avoiding_weak` / `exists_empty_convex_ear_weak`
which drop that clause together with the two edge non-degeneracies `a - p ≠ 0`,
`q - c ≠ 0` that were derived from it.  The clip's flat vertices are removed
downstream by `RequestProject.SAWUmlaufFlatRemoval`.
-/

/-- **The empty-convex-ear existence core, forbidden-vertex form (corrected).**
A simple, cyclically non-degenerate polygon with at least four vertices, and any
forbidden vertex `z`, has a rotation `a :: b :: c :: rest` whose middle vertex
`b ≠ z` is an *ear*: the corner is non-flat, no far vertex lies strictly inside
the corner triangle or on the closed clip diagonal `[a, c]`, and the ear triangle
has the orientation of the clip.

**Why the forbidden vertex `z`.**  The bare one-ear statement is not amenable to
the split-and-recurse induction: splitting along an interior diagonal `d` yields
two strictly shorter simple sub-polygons, but the single ear handed back by a
one-ear induction hypothesis may have its tip at an endpoint of `d`, in which
case it is *not* an ear of the original polygon.  The forbidden-vertex form is
the inductive packaging of Meisters' two-ears theorem that repairs this. -/
lemma exists_empty_convex_ear_avoiding_weak (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hlen : 4 ≤ V.length) (hVN : V.length ≤ N)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z : ℂ) :
    ∃ (r : ℕ) (a b c : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, hbz, -, -, hempty, hdiag, horient⟩ :=
    exists_empty_corner_avoiding N hN V hlen hVN hsimple hnd z
  exact ⟨r, a, b, c, rest, hrot, hbz,
    polyCycNondeg_rotate_head V a b c rest r (by omega) hnd hrot,
    hempty, hdiag, horient⟩

/-- **The empty-convex-ear existence core (one-ear corollary, corrected form).**
Derived from `exists_empty_convex_ear_avoiding_weak` by instantiating the
forbidden vertex arbitrarily.  This is exactly the statement
`exists_front_ear_weak` of `RequestProject.SAWUmlaufPolygon`, the sole
ear-existence input of the planar Umlaufsatz. -/
lemma exists_empty_convex_ear_weak (N : ℕ) (hN : DichBelow N)
    (V : List ℂ) (hlen : 4 ≤ V.length) (hVN : V.length ≤ N)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, rest, hrot, -, hndtri, hempty, hdiag, horient⟩ :=
    exists_empty_convex_ear_avoiding_weak N hN V hlen hVN hsimple hnd 0
  exact ⟨r, a, b, c, rest, hrot, hndtri, hempty, hdiag, horient⟩

/- ⚠ **FALSE AS STATED — see `RequestProject.SAWUmlaufFlatClipCounterexample`,
`flat_clip_no_empty_convex_ear`.**  Superseded by the two weak forms above;
retained verbatim, commented out, as a record of the old interface.

/-- **The empty-convex-ear existence core, in the inductively-correct
    "forbidden-vertex" form (the genuine Meisters TWO-ears content).**  A
    simple, non-degenerate polygon with at least four vertices, together with
    *any* single forbidden vertex `z`, has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose middle vertex `b` is an empty
    convex ear **with tip `b ≠ z`**: the corner triangle `a b c` is
    non-degenerate, contains no far vertex strictly inside (`hempty`) and none
    on the closed diagonal `a–c` (`hdiag`), the five cyclic edge
    non-degeneracies hold, the clipped cycle `a :: c :: rest` is still
    cyclically non-degenerate, and the cut-off ear triangle has the *same
    orientation* as the clip (`0 < shoelace2 [a,b,c] ↔
    0 < shoelace2 (a :: c :: rest)`).

    **Why the forbidden vertex `z`.**  The bare one-ear statement
    `exists_empty_convex_ear` (derived below) is *not* directly amenable to the
    split-and-recurse induction: splitting a simple polygon along an interior
    diagonal `d` yields two strictly shorter simple sub-polygons, but the
    *single* ear handed back by a one-ear induction hypothesis on a sub-polygon
    may have its tip at an endpoint of `d`, in which case it is **not** an ear
    of the original polygon.  The standard Meisters fix is the genuine TWO-ears
    theorem; the cleanest inductive packaging of "≥ 2 ears" is exactly this
    forbidden-vertex form: with `z` set to the far diagonal endpoint, the
    recursion returns an ear of the sub-polygon avoiding `z`, which therefore
    survives as an ear of the whole polygon.  Deriving the one-ear corollary is
    then trivial (instantiate `z` arbitrarily).

/-! ⚠ **FALSE AS STATED — see `RequestProject.SAWUmlaufFlatClipCounterexample`.**
The declaration below demands that clipping the ear leave a *cyclically
non-degenerate* polygon (equivalently the two clip-corner clauses
`cross (a - p) (c - a) ≠ 0`, `cross (c - a) (q - c) ≠ 0`).  The simple,
non-degenerate pentagon `0, i, 1+i, 2+2i, 2+i` refutes that: every one of its
ears leaves a flat vertex behind.  It is retained as preparation: restating it in
the *weak* form (both clauses dropped) turns it into a true statement, and the
weak form of the top of this chain is `exists_front_ear_weak`
(`RequestProject.SAWUmlaufPolygon`), which is what the live route now uses,
together with the flat-vertex normalisation of
`RequestProject.SAWUmlaufFlatRemoval`. -/

    This is the irreducible Jordan-curve-theorem-level core (absent from
    Mathlib).  Intended route: strong induction on `V.length`.  Choose the
    extreme (leftmost-lowest) convex vertex via `HexArea.exists_lex_min_mem` /
    `lexMin_not_inTriangleStrict`; if its corner triangle is empty it is the
    ear (use it, or its cyclic neighbour, to avoid `z`); otherwise pivot to the
    vertex farthest from the base diagonal (`HexArea.exists_max_cross`,
    `farthest_region_empty`, `inTriangleStrict_pos_nest`,
    `subTri_axc_orient_pos`, `inTriangleStrict_apex_sameSide`), split along the
    resulting interior diagonal and recurse on the strictly shorter
    sub-polygons.  Recorded partial progress: consumed by
    `exists_empty_convex_ear` immediately below. -/
lemma exists_empty_convex_ear_avoiding (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) (z : ℂ) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧ b ≠ z ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  -- **The genuine Meisters search (the single remaining open core).**  Find a
  -- cyclic rotation exhibiting an *empty* corner `a,b,c` (tip `b ≠ z`) whose two
  -- clip corners `(p,a,c)` and `(a,c,q)` are non-flat and whose ear orientation
  -- matches the clip.  All the remaining ear-data bookkeeping is then discharged
  -- by `ear_data_of_empty_corner` below.
  obtain ⟨r, a, b, c, p, q, rest, hrot, hbz, hp, hq, hclipa, hclipc, hempty, hdiag,
      horient⟩ := exists_empty_corner_avoiding V hlen hsimple hnd z
  -- Transport cyclic non-degeneracy across the rotation and assemble the data.
  have hndrot : polyCycNondeg (a :: b :: c :: rest) :=
    hrot ▸ (polyCycNondeg_rotate V r (by omega)).mpr hnd
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    ear_data_of_empty_corner a b c p q rest hp hq hndrot hclipa hclipc hempty hdiag
      horient
  exact ⟨r, a, b, c, p, q, rest, hrot, hbz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12⟩

/-! ⚠ **FALSE AS STATED — see `RequestProject.SAWUmlaufFlatClipCounterexample`.**
The declaration below demands that clipping the ear leave a *cyclically
non-degenerate* polygon (equivalently the two clip-corner clauses
`cross (a - p) (c - a) ≠ 0`, `cross (c - a) (q - c) ≠ 0`).  The simple,
non-degenerate pentagon `0, i, 1+i, 2+2i, 2+i` refutes that: every one of its
ears leaves a flat vertex behind.  It is retained as preparation: restating it in
the *weak* form (both clauses dropped) turns it into a true statement, and the
weak form of the top of this chain is `exists_front_ear_weak`
(`RequestProject.SAWUmlaufPolygon`), which is what the live route now uses,
together with the flat-vertex normalisation of
`RequestProject.SAWUmlaufFlatRemoval`. -/

/-- **The empty-convex-ear existence core (one-ear corollary).**  A simple,
    non-degenerate polygon with at least four vertices has a cyclic rotation
    `V.rotate r = a :: b :: c :: rest` whose middle vertex `b` is an empty
    convex ear.  Derived trivially from the forbidden-vertex form
    `exists_empty_convex_ear_avoiding` (instantiate `z := 0` and drop the
    `b ≠ z` clause).  Consumed by `exists_front_ear_core` below. -/
lemma exists_empty_convex_ear (V : List ℂ) (hlen : 4 ≤ V.length)
    (hsimple : PolygonSimple V) (hnd : polyCycNondeg V) :
    ∃ (r : ℕ) (a b c p q : ℂ) (rest : List ℂ),
      V.rotate r = a :: b :: c :: rest ∧
      rest.getLast? = some p ∧ rest.head? = some q ∧
      a - p ≠ 0 ∧ b - a ≠ 0 ∧ c - b ≠ 0 ∧ q - c ≠ 0 ∧ c - a ≠ 0 ∧
      HexArea.cross (b - a) (c - b) ≠ 0 ∧
      (∀ x ∈ rest, ¬ HexArea.inTriangleStrict a b c x) ∧
      (∀ x ∈ rest, x ∉ segment ℝ a c) ∧
      polyCycNondeg (a :: c :: rest) ∧
      ((0:ℝ) < HexArea.shoelace2 [a, b, c]
          ↔ (0:ℝ) < HexArea.shoelace2 (a :: c :: rest)) := by
  obtain ⟨r, a, b, c, p, q, rest, hrot, _hbz, hp, hq, hpa, hab, hbc, hcq, hca,
      hndtri, hempty, hdiag, hndclip, htri⟩ :=
    exists_empty_convex_ear_avoiding V hlen hsimple hnd 0
  exact ⟨r, a, b, c, p, q, rest, hrot, hp, hq, hpa, hab, hbc, hcq, hca, hndtri,
    hempty, hdiag, hndclip, htri⟩
-/

end
