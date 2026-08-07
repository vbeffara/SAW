import Mathlib
import RequestProject.SAWUmlaufFlatSeamLift

/-!
# `SAWUmlaufFlatClipLift` — the empty branch when the clip has a flat seam corner

In the empty branch of the Meisters ear search the tip `b` is the lexicographic
minimum of the simple polygon `V.rotate r = a :: b :: c :: rest`, the corner
triangle `a, b, c` contains no vertex of `rest`, and the base `[a, c]` is clear.
The clip `M = a :: c :: rest` is then a *simple* polygon with one vertex fewer,
and the orientation clause of `EmptyCornerData2` is automatic
(`clip_orient_of_extreme_tip`).  If moreover `b` is one of the two forbidden
vertices, the ear at `b` is unusable and the search must recurse on `M`.

The recursion hypothesis `IH2` demands `polyCycNondeg M`, and that can fail: the
two *seam* corners of the clip, at `a` (with cyclic predecessor `p`, the last
vertex of `rest`) and at `c` (with cyclic successor `q`, the head of `rest`), are
new corners, and either of them may be flat.  Every other corner of `M` is a
corner of `V`, hence non-flat.  So exactly three configurations can occur:

* **only the corner at `a` is flat.**  Then `a` lies strictly between `p` and `c`,
  and deleting it from `M` leaves the cyclically non-degenerate `c :: rest`.  The
  clip therefore carries `FlatSeamData M a c` and
  `flatSeam_EmptyCornerData2_of_data` produces the ear.
* **only the corner at `c` is flat.**  Mirror image: `c` lies strictly between
  `a` and `q`, and deleting it from `M` leaves the cyclically non-degenerate
  `rest ++ [a]`.
* **both seam corners are flat.**  Then `p, a, c, q` are collinear in that order
  and two deletions are needed; this configuration is genuinely realisable and is
  handled by `clip_both_flat_ear`, which recurses on `rest` and re-inserts the
  two flat vertices (`clip_double_insert_ear`, with the pentagon base case
  `flat_pent_ear`).

This file provides the `polyNondeg` bookkeeping (`polyCycNondeg_clip_weak`, which
weakens `polyCycNondeg_clip` by dropping the hypothesis at the deleted vertex —
that is precisely the corner which is flat here) and all three cases; the single
entry point is `clip_flat_ear`.  The whole file is `sorry`-free.

NOT a dead branch: the results are consumed by `empty_branch_flat_clip_lift`
(`RequestProject.SAWUmlaufPolyMeisters`).
-/

open Real Complex

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. `polyNondeg` bookkeeping -/

/-- **Replacing the last vertex of a chain.**  If the chain `L ++ [a, y]` is
non-degenerate and the corner `(last L, a, x)` is non-flat, then `L ++ [a, x]` is
non-degenerate: the two chains share every triple except the final one. -/
lemma polyNondeg_replace_last (L : List ℂ) (w a x y : ℂ) (hw : L.getLast? = some w)
    (hL : polyNondeg (L ++ [a, y]))
    (hx : HexArea.cross (a - w) (x - a) ≠ 0) :
    polyNondeg (L ++ [a, x]) := by
  induction' L with z L ih generalizing w y
  · simp at hw
  · rcases L with _ | ⟨u, L⟩
    · simp at hw; subst hw; exact ⟨hx, trivial⟩
    · have hw' : (u :: L).getLast? = some w := by simpa using hw
      rcases L with _ | ⟨v, L⟩
      · simp at hw'; subst hw'
        exact ⟨hL.1, hx, trivial⟩
      · exact ⟨hL.1, ih w y hw' hL.2 hx⟩

/-- **A chain gains a new head vertex.**  Prepending `a` to `c :: X` keeps
non-degeneracy provided the new corner `(a, c, X.head)` is non-flat. -/
lemma polyNondeg_cons_head (a c : ℂ) (X : List ℂ) (q : ℂ) (hq : X.head? = some q)
    (h : polyNondeg (c :: X)) (hcq : HexArea.cross (c - a) (q - c) ≠ 0) :
    polyNondeg (a :: c :: X) := by
  obtain ⟨X', rfl⟩ := List.head?_eq_some_iff.mp hq
  exact ⟨hcq, h⟩

/-- **The clip is cyclically non-degenerate — weak form.**  This is
`polyCycNondeg_clip` with the hypothesis at the *deleted* vertex `b` removed:
only `polyNondeg (b :: c :: rest ++ [a, b])`, i.e. cyclic non-degeneracy of
`a :: b :: c :: rest` at every corner *other than* `b`, is required.  That is the
form needed when `b` itself is the flat vertex being deleted. -/
lemma polyCycNondeg_clip_weak (a b c p q : ℂ) (rest : List ℂ)
    (hq : rest.head? = some q) (hp : rest.getLast? = some p)
    (hnd : polyNondeg (b :: c :: rest ++ [a, b]))
    (hpa : HexArea.cross (a - p) (c - a) ≠ 0)
    (hcq : HexArea.cross (c - a) (q - c) ≠ 0) :
    polyCycNondeg (a :: c :: rest) := by
  have htake : (a :: c :: rest).take 2 = [a, c] := by simp
  rw [polyCycNondeg_def, htake]
  have h1 : polyNondeg (c :: rest ++ [a, b]) := by
    have := HexArea.polyNondeg_drop _ 1 hnd
    simpa using this
  have hlast : (c :: rest).getLast? = some p := by
    obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp hp
    exact List.getLast?_concat (l := c :: t)
  have h2 : polyNondeg ((c :: rest) ++ [a, c]) :=
    polyNondeg_replace_last (c :: rest) p a c b hlast (by simpa using h1) hpa
  refine polyNondeg_cons_head a c (rest ++ [a, c]) q ?_ (by simpa using h2) hcq
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hq
  simp

/-! ## 2. Reading a cyclic corner off a rotation -/

/-- **Every cyclic corner of a cyclically non-degenerate polygon is non-flat**,
read off through the first three entries of an arbitrary rotation. -/
lemma polyCycNondeg_corner_of_rotate (V : List ℂ) (h3 : 3 ≤ V.length)
    (hnd : polyCycNondeg V) (i : ℕ) (x y z : ℂ)
    (hx : (V.rotate i)[0]? = some x) (hy : (V.rotate i)[1]? = some y)
    (hz : (V.rotate i)[2]? = some z) :
    HexArea.cross (y - x) (z - y) ≠ 0 := by
  obtain ⟨x', y', z', tl, hr⟩ : ∃ x' y' z' tl, V.rotate i = x' :: y' :: z' :: tl := by
    have hlen3 : 3 ≤ (V.rotate i).length := by simpa using h3
    match hh : V.rotate i with
    | a :: b :: c :: t => exact ⟨a, b, c, t, rfl⟩
    | [] => simp [hh] at hlen3
    | [_] => simp [hh] at hlen3
    | [_, _] => simp [hh] at hlen3
  rw [hr] at hx hy hz
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some_inj] at hx hy hz
  have := polyCycNondeg_rotate_head V x' y' z' tl i h3 hnd hr
  rw [hx, hy, hz] at this
  exact this

/-- The cyclic-corner statement in terms of `getElem?` of `V` itself. -/
lemma polyCycNondeg_corner_getElem (V : List ℂ) (h3 : 3 ≤ V.length)
    (hnd : polyCycNondeg V) (i : ℕ) (x y z : ℂ)
    (hx : V[i % V.length]? = some x) (hy : V[(i + 1) % V.length]? = some y)
    (hz : V[(i + 2) % V.length]? = some z) :
    HexArea.cross (y - x) (z - y) ≠ 0 := by
  have hlen : 0 < V.length := by omega
  refine polyCycNondeg_corner_of_rotate V h3 hnd i x y z ?_ ?_ ?_
  · rw [List.getElem?_rotate (by omega)]
    simpa [Nat.zero_add] using hx
  · rw [List.getElem?_rotate (by omega)]
    rw [show (1 + i) % V.length = (i + 1) % V.length by ring_nf]
    exact hy
  · rw [List.getElem?_rotate (by omega)]
    rw [show (2 + i) % V.length = (i + 2) % V.length by ring_nf]
    exact hz

/-! ## 3. Deleting a flat seam corner of the clip -/

/-- `polyNondeg` is inherited by `dropLast`. -/
lemma polyNondeg_dropLast (L : List ℂ) (h : polyNondeg L) : polyNondeg L.dropLast := by
  rw [List.dropLast_eq_take]
  exact HexArea.polyNondeg_take L _ h

/-- **Case A: the clip's seam corner at `a` is flat.**  Let
`V₀ = a :: b :: c :: rest` be cyclically non-degenerate with `rest = t ++ [p₂, p]`,
and suppose the clip's other seam corner, at `c`, is non-flat (`hcq`) while the
apex `a` of the clip lies on the segment from its cyclic predecessor `p` to `c`
(`hseg`, the geometric content of the corner at `a` being flat).  Then deleting
`a` from the clip leaves the cyclically non-degenerate cycle `c :: rest`. -/
lemma clip_delete_a_nondeg (a b c p q p₂ : ℂ) (t : List ℂ)
    (hnd : polyCycNondeg (a :: b :: c :: (t ++ [p₂, p])))
    (hq : (t ++ [p₂, p]).head? = some q)
    (hcq : HexArea.cross (c - a) (q - c) ≠ 0)
    (hseg : a ∈ segment ℝ p c) :
    polyCycNondeg (c :: (t ++ [p₂, p])) := by
  have hclosed : polyNondeg (a :: b :: c :: (t ++ [p₂, p]) ++ [a, b]) := by
    have h := hnd
    rw [polyCycNondeg_def] at h
    simpa using h
  have hmidhead : (t ++ [p₂]).head? = some q := by
    cases t with
    | nil => simpa using hq
    | cons u t' => simpa using hq
  have hmidlast : (t ++ [p₂]).getLast? = some p₂ := List.getLast?_concat
  -- the corner of `V₀` at `p`
  have hcorner_p : HexArea.cross (p - p₂) (a - p) ≠ 0 := by
    have hd := HexArea.polyNondeg_drop _ (t.length + 3) hclosed
    have he : (a :: b :: c :: (t ++ [p₂, p]) ++ [a, b]).drop (t.length + 3) = [p₂, p, a, b] := by
      simp
    rw [he] at hd
    exact hd.1
  have hpa' : HexArea.cross (p - p₂) (c - p) ≠ 0 :=
    cross_pred_corner_remove_flat p₂ p c a hseg hcorner_p
  have hcq' : HexArea.cross (c - p) (q - c) ≠ 0 :=
    cross_succ_corner_remove_flat q p c a hseg hcq
  have hsub : polyNondeg (c :: (t ++ [p₂, p, a])) := by
    have h1 : polyNondeg (c :: (t ++ [p₂, p]) ++ [a, b]) := by
      have := HexArea.polyNondeg_drop _ 2 hclosed
      simpa using this
    have h2 := polyNondeg_dropLast _ h1
    have he : (c :: (t ++ [p₂, p]) ++ [a, b]).dropLast = c :: (t ++ [p₂, p, a]) := by
      rw [show c :: (t ++ [p₂, p]) ++ [a, b] = (c :: (t ++ [p₂, p, a])) ++ [b] by simp,
        List.dropLast_concat]
    rwa [he] at h2
  have hnd' : polyNondeg (a :: c :: (t ++ [p₂, p, a])) :=
    polyNondeg_cons_head a c (t ++ [p₂, p, a]) q
      (by cases t with
          | nil => simpa using hmidhead
          | cons u t' => simpa using hmidhead) hsub hcq
  have hres := polyCycNondeg_clip_weak p a c p₂ q (t ++ [p₂]) hmidhead hmidlast
    (by simpa using hnd') hpa' hcq'
  have hrot : (p :: c :: (t ++ [p₂])).rotate 1 = c :: (t ++ [p₂]) ++ [p] := by
    simp [List.rotate_cons_succ]
  have hfin := (polyCycNondeg_rotate (p :: c :: (t ++ [p₂])) 1 (by simp)).mpr hres
  rw [hrot] at hfin
  have he : c :: (t ++ [p₂]) ++ [p] = c :: (t ++ [p₂, p]) := by simp
  rwa [he] at hfin

/-- **Case B: the clip's seam corner at `c` is flat.**  Let
`V₀ = a :: b :: c :: (q :: rest')` be cyclically non-degenerate with `rest'`
non-empty and last vertex `p`, suppose the clip's other seam corner, at `a`, is
non-flat (`hpl`), and let `c` lie on the segment from `a` to its cyclic successor
`q` (`hseg`, the geometric content of the corner at `c` being flat).  Then
deleting `c` from the clip leaves the cyclically non-degenerate cycle
`(q :: rest') ++ [a]`. -/
lemma clip_delete_c_nondeg (a b c p q q₂ : ℂ) (rest' : List ℂ)
    (hnd : polyCycNondeg (a :: b :: c :: (q :: rest')))
    (hq₂ : rest'.head? = some q₂) (hp : rest'.getLast? = some p)
    (hpl : HexArea.cross (a - p) (c - a) ≠ 0)
    (hseg : c ∈ segment ℝ a q) :
    polyCycNondeg ((q :: rest') ++ [a]) := by
  have hclosed : polyNondeg (a :: b :: c :: (q :: rest') ++ [a, b]) := by
    have h := hnd
    rw [polyCycNondeg_def] at h
    simpa using h
  have h1 : polyNondeg (c :: q :: rest' ++ [a, b]) := by
    have := HexArea.polyNondeg_drop _ 2 hclosed
    simpa using this
  -- the corner of `V₀` at `q`
  have hcorner_q : HexArea.cross (q - c) (q₂ - q) ≠ 0 := by
    obtain ⟨s, rfl⟩ := List.head?_eq_some_iff.mp hq₂
    exact h1.1
  have hpa : HexArea.cross (a - p) (q - a) ≠ 0 :=
    cross_pred_corner_remove_flat p a q c hseg hpl
  have hcq : HexArea.cross (q - a) (q₂ - q) ≠ 0 :=
    cross_succ_corner_remove_flat q₂ a q c hseg hcorner_q
  have hlast : (c :: q :: rest').getLast? = some p := by
    obtain ⟨s, rfl⟩ := List.getLast?_eq_some_iff.mp hp
    exact List.getLast?_concat (l := c :: q :: s)
  have hnd' : polyNondeg (c :: q :: rest' ++ [a, c]) := by
    have := polyNondeg_replace_last (c :: q :: rest') p a c b hlast (by simpa using h1) hpl
    simpa using this
  have hres := polyCycNondeg_clip_weak a c q p q₂ rest' hq₂ hp hnd' hpa hcq
  have hrest'ne : rest' ≠ [] := by
    intro h; rw [h] at hq₂; simp at hq₂
  have hrot : (a :: q :: rest').rotate 1 = (q :: rest') ++ [a] := by
    simp [List.rotate_cons_succ]
  have hfin := (polyCycNondeg_rotate (a :: q :: rest') 1
    (by simp; exact List.length_pos_iff.mpr hrest'ne)).mpr hres
  rwa [hrot] at hfin

/-! ## 4. The two seam cross products -/

/-- The corner turn at the clip vertex `a` is the base cross product at `p`. -/
lemma cross_seam_a (a c p : ℂ) :
    HexArea.cross (a - p) (c - a) = HexArea.cross (c - a) (p - a) := by
  simp [HexArea.cross]; ring

/-- The corner turn at the clip vertex `c` is the base cross product at `q`. -/
lemma cross_seam_c (a c q : ℂ) :
    HexArea.cross (c - a) (q - c) = HexArea.cross (c - a) (q - a) := by
  simp [HexArea.cross]; ring

/-! ## 5. The flat-seam data of a clip with exactly one flat seam corner -/

/-- **A clip with exactly one flat seam corner carries a Meisters ear avoiding
the clip diagonal.**

Let `a :: b :: c :: rest` be a simple, cyclically non-degenerate polygon whose
clip `M = a :: c :: rest` is simple, and suppose *exactly one* of the two seam
corners of `M` — at `a`, measured by `cross (c - a) (p - a)` with `p` the last
vertex of `rest`, and at `c`, measured by `cross (c - a) (q - a)` with `q` the
head of `rest` — is flat.  Then `M` carries `FlatSeamData M a c`, and the
flat-seam recursion produces an ear of `M` avoiding both `a` and `c`.

This is exactly the recursion input that `empty_branch_good_lift` obtains from
`IH2` when the clip happens to be non-degenerate.  NOT a dead branch: it is the
single-flat half of `empty_branch_flat_clip_lift`. -/
lemma clip_single_flat_ear (a b c p q : ℂ) (rest : List ℂ) (hrest2 : 2 ≤ rest.length)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hsimple : PolygonSimple (a :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hone : (HexArea.cross (c - a) (p - a) = 0 ∧ HexArea.cross (c - a) (q - a) ≠ 0) ∨
            (HexArea.cross (c - a) (p - a) ≠ 0 ∧ HexArea.cross (c - a) (q - a) = 0))
    (IH : ∀ M : List ℂ, M.length < (a :: c :: rest).length → 4 ≤ M.length → PolygonSimple M →
       polyCycNondeg M → ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge M w1 w2) →
       EmptyCornerData2 M w1 w2) :
    EmptyCornerData2 (a :: c :: rest) a c := by
  have h4 : 4 ≤ (a :: c :: rest).length := by simp; omega
  refine flatSeam_EmptyCornerData2_of_data (a :: c :: rest) hsimple h4 a c ?_ IH
  rcases hone with ⟨hfa, hnc⟩ | ⟨hna, hfc⟩
  · -- **the corner at `a` is the flat one**: delete `a`, leaving `c :: rest`
    obtain ⟨s, rfl⟩ := List.getLast?_eq_some_iff.mp hp
    have hslen : 1 ≤ s.length := by simpa using hrest2
    obtain ⟨p₂, t, rfl⟩ : ∃ p₂ t, s = t ++ [p₂] := by
      obtain ⟨y, hy⟩ : ∃ y, s.getLast? = some y := by
        cases hcase : s.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hcase) (by
            intro h; rw [h] at hslen; simp at hslen)
        | some y => exact ⟨y, rfl⟩
      obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp hy
      exact ⟨y, t, ht⟩
    have hrw : t ++ [p₂] ++ [p] = t ++ [p₂, p] := by simp
    rw [hrw] at hsimple hnd hq ⊢
    -- the rotation of the clip exhibiting the flat corner in the middle
    have hrot : (a :: c :: (t ++ [p₂, p])).rotate (t.length + 3)
        = p :: a :: c :: (t ++ [p₂]) := by
      rw [List.rotate_eq_drop_append_take (by simp)]
      rw [show t ++ [p₂, p] = (t ++ [p₂]) ++ [p] by simp]
      rw [show a :: c :: ((t ++ [p₂]) ++ [p]) = (a :: c :: (t ++ [p₂])) ++ [p] by simp]
      rw [List.drop_append_of_le_length (by simp), List.take_append_of_le_length (by simp)]
      simp
    have hRotSimple : PolygonSimple (p :: a :: c :: (t ++ [p₂])) := by
      rw [← hrot]
      exact (PolygonSimple_rotate _ _).mpr hsimple
    obtain ⟨σ, hσ0, hσ1, hσ⟩ :=
      flat_between_of_cross_zero p a c (t ++ [p₂]) (by simp) hRotSimple
        (by rw [cross_seam_a]; exact hfa)
    have hseg : a ∈ segment ℝ p c :=
      mem_segment_of_param p c σ (le_of_lt hσ0) (le_of_lt hσ1) a hσ
    have hMnd : polyCycNondeg (c :: (t ++ [p₂, p])) :=
      clip_delete_a_nondeg a b c p q p₂ t hnd hq (by rw [cross_seam_c]; exact hnc) hseg
    have hlast : (c :: (t ++ [p₂, p])).getLast? = some p := by
      rw [show c :: (t ++ [p₂, p]) = (c :: (t ++ [p₂])) ++ [p] by simp]
      exact List.getLast?_concat
    exact ⟨0, c :: (t ++ [p₂, p]), a, c, p, c, σ, Or.inl ⟨rfl, rfl⟩, by simp, rfl, hlast,
      Or.inr rfl, hσ0, hσ1, hσ, hMnd⟩
  · -- **the corner at `c` is the flat one**: delete `c`, leaving `rest ++ [a]`
    obtain ⟨rest', rfl⟩ := List.head?_eq_some_iff.mp hq
    have hr'len : 1 ≤ rest'.length := by simpa using hrest2
    have hrest'ne : rest' ≠ [] := by
      intro h; rw [h] at hr'len; simp at hr'len
    obtain ⟨q₂, hq₂⟩ : ∃ y, rest'.head? = some y := by
      cases hcase : rest'.head? with
      | none => exact absurd (List.head?_eq_none_iff.mp hcase) hrest'ne
      | some y => exact ⟨y, rfl⟩
    have hp' : rest'.getLast? = some p := by
      cases rest' with
      | nil => exact absurd rfl hrest'ne
      | cons u s => simpa using hp
    obtain ⟨σ, hσ0, hσ1, hσ⟩ :=
      flat_between_of_cross_zero a c q rest' hrest'ne hsimple
        (by rw [cross_seam_c]; exact hfc)
    have hseg : c ∈ segment ℝ a q :=
      mem_segment_of_param a q σ (le_of_lt hσ0) (le_of_lt hσ1) c hσ
    have hMnd : polyCycNondeg ((q :: rest') ++ [a]) :=
      clip_delete_c_nondeg a b c p q q₂ rest' hnd hq₂ hp'
        (by rw [cross_seam_a]; exact hna) hseg
    have hrot : (a :: c :: (q :: rest')).rotate 1 = c :: ((q :: rest') ++ [a]) := by
      simp [List.rotate_cons_succ]
    exact ⟨1, (q :: rest') ++ [a], c, a, a, q, σ, Or.inr ⟨rfl, rfl⟩, hrot, by simp,
      List.getLast?_concat, Or.inl rfl, hσ0, hσ1, hσ, hMnd⟩

/-! ## 6. Both seam corners flat -/

/-- **Chaining two flat parameters.**  If `a` lies strictly between `p` and `c`
and `c` lies strictly between `a` and `q`, then `p, a, c, q` occur in that order
on their common line: both `a` and `c` lie strictly between `p` and `q`, with
parameters `α < γ`. -/
lemma flat_chain_params (p a c q : ℂ) (σ τ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (h1 : a - p = (σ : ℂ) * (c - p)) (h2 : c - a = (τ : ℂ) * (q - a)) :
    ∃ α γ : ℝ, 0 < α ∧ α < γ ∧ γ < 1 ∧
      a - p = (α : ℂ) * (q - p) ∧ c - p = (γ : ℂ) * (q - p) := by
  set D : ℝ := 1 - σ + σ * τ with hDdef
  have hD : 0 < D := by rw [hDdef]; nlinarith
  have hDne : (D : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hD)
  have key1 : (D : ℂ) * (a - p) = ((σ * τ : ℝ) : ℂ) * (q - p) := by
    rw [hDdef]; push_cast; linear_combination h1 + (σ : ℂ) * h2
  have key2 : (D : ℂ) * (c - p) = ((τ : ℝ) : ℂ) * (q - p) := by
    rw [hDdef]; push_cast; linear_combination ((1 : ℂ) - (τ : ℂ)) * h1 + h2
  refine ⟨σ * τ / D, τ / D, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_div_iff_of_pos_right hD]; nlinarith
  · rw [div_lt_one hD, hDdef]; nlinarith
  · rw [show ((σ * τ / D : ℝ) : ℂ) = ((σ * τ : ℝ) : ℂ) / (D : ℂ) by push_cast; ring]
    field_simp
    linear_combination key1
  · rw [show ((τ / D : ℝ) : ℂ) = ((τ : ℝ) : ℂ) / (D : ℂ) by push_cast; ring]
    field_simp
    linear_combination key2

/-- **Deleting both flat seam vertices keeps the tail simple.**  If `a` and `c`
both lie on the closed edge `[p, q]` of the clip `a :: c :: rest`, they are flat
vertices of it, and removing them one at a time preserves planar simplicity. -/
lemma clip_both_flat_delete_simple (a c p q : ℂ) (rest' s' : List ℂ)
    (hrest' : rest' = s' ++ [p])
    (hsimple : PolygonSimple (a :: c :: (q :: rest')))
    (hsegc_aq : c ∈ segment ℝ a q) (hsega_pq : a ∈ segment ℝ p q) :
    PolygonSimple (q :: rest') := by
  subst hrest'
  have h1 : PolygonSimple (a :: q :: (s' ++ [p])) :=
    PolygonSimple_remove_flat_second a c q (s' ++ [p]) hsimple hsegc_aq
  have hrot : (a :: q :: (s' ++ [p])).rotate (s'.length + 2) = p :: a :: q :: s' := by
    rw [List.rotate_eq_drop_append_take (by simp)]
    rw [show a :: q :: (s' ++ [p]) = (a :: q :: s') ++ [p] by simp]
    rw [List.drop_append_of_le_length (by simp), List.take_append_of_le_length (by simp)]
    simp
  have h2 : PolygonSimple (p :: a :: q :: s') := by
    rw [← hrot]; exact (PolygonSimple_rotate _ _).mpr h1
  have h3 : PolygonSimple (p :: q :: s') :=
    PolygonSimple_remove_flat_second p a q s' h2 hsega_pq
  have hrot2 : (p :: q :: s').rotate 1 = q :: (s' ++ [p]) := by simp [List.rotate_cons_succ]
  rw [← hrot2]
  exact (PolygonSimple_rotate _ _).mpr h3

/-- **Deleting both flat seam vertices leaves a cyclically non-degenerate
tail.**  Every corner of `rest` other than the two at `p` and `q` is a corner of
the polygon itself; the corners at `p` and `q` are the original ones with the
neighbour `a` (resp. `c`) replaced by `q` (resp. `p`), and those replacements
rescale the relevant difference vector by a positive factor. -/
lemma clip_both_flat_delete_nondeg (a b c p q p₂ q₂ : ℂ) (rest' s' : List ℂ)
    (hrest' : rest' = s' ++ [p])
    (hq₂ : s'.head? = some q₂) (hp₂ : s'.getLast? = some p₂)
    (hnd : polyCycNondeg (a :: b :: c :: (q :: rest')))
    (hsega_pq : a ∈ segment ℝ p q) (hsegc_pq : c ∈ segment ℝ p q)
    (hsega_pc : a ∈ segment ℝ p c) :
    polyCycNondeg (q :: rest') := by
  subst hrest'
  have hclosed : polyNondeg (a :: b :: c :: q :: (s' ++ [p]) ++ [a, b]) := by
    have h := hnd
    rw [polyCycNondeg_def] at h
    simpa using h
  have h1 : polyNondeg (c :: q :: (s' ++ [p]) ++ [a, b]) := by
    have := HexArea.polyNondeg_drop _ 2 hclosed
    simpa using this
  -- the corner of the polygon at `q`
  have hcorner_q : HexArea.cross (q - c) (q₂ - q) ≠ 0 := by
    obtain ⟨u, rfl⟩ := List.head?_eq_some_iff.mp hq₂
    exact h1.1
  -- the corner of the polygon at `p`
  have hcorner_p : HexArea.cross (p - p₂) (a - p) ≠ 0 := by
    have hd := HexArea.polyNondeg_drop _ (s'.length + 1) h1
    have he : (c :: q :: (s' ++ [p]) ++ [a, b]).drop (s'.length + 1) = [p₂, p, a, b] := by
      obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hp₂
      rw [show c :: q :: ((u ++ [p₂]) ++ [p]) ++ [a, b]
            = (c :: q :: u) ++ [p₂, p, a, b] by simp,
        show (u ++ [p₂]).length + 1 = (c :: q :: u).length by simp,
        List.drop_left]
    rw [he] at hd
    exact hd.1
  have hpa : HexArea.cross (p - p₂) (q - p) ≠ 0 :=
    cross_pred_corner_remove_flat p₂ p q a hsega_pq hcorner_p
  have hcq : HexArea.cross (q - p) (q₂ - q) ≠ 0 :=
    cross_succ_corner_remove_flat q₂ p q c hsegc_pq hcorner_q
  have hpc : HexArea.cross (p - p₂) (c - p) ≠ 0 :=
    cross_pred_corner_remove_flat p₂ p c a hsega_pc hcorner_p
  -- the chain of all corners of the clip other than the one at `c`
  have hchain : polyNondeg (c :: q :: s' ++ [p, c]) := by
    have h2 := polyNondeg_dropLast _ h1
    have he : (c :: q :: (s' ++ [p]) ++ [a, b]).dropLast = (c :: q :: s') ++ [p, a] := by
      rw [show c :: q :: (s' ++ [p]) ++ [a, b] = ((c :: q :: s') ++ [p, a]) ++ [b] by simp,
        List.dropLast_concat]
    rw [he] at h2
    have hlast : (c :: q :: s').getLast? = some p₂ := by
      obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hp₂
      exact List.getLast?_concat (l := c :: q :: u)
    have := polyNondeg_replace_last (c :: q :: s') p₂ p c a hlast h2 hpc
    simpa using this
  have hres := polyCycNondeg_clip_weak p c q p₂ q₂ s' hq₂ hp₂ (by simpa using hchain) hpa hcq
  have hs'ne : s' ≠ [] := by
    intro h; rw [h] at hq₂; simp at hq₂
  have hrot2 : (p :: q :: s').rotate 1 = q :: (s' ++ [p]) := by simp [List.rotate_cons_succ]
  have hfin := (polyCycNondeg_rotate (p :: q :: s') 1
    (by have h := List.length_pos_of_ne_nil hs'ne; simp only [List.length_cons]; omega)).mpr hres
  rwa [hrot2] at hfin

/-- **The pentagon base case of the double insertion.**

`[a, c, q, x, p]` is a simple pentagon in which the two vertices `a` and `c` lie
on the open segment `(p, q)`, in the cyclic order `p, a, c, q` (parameters
`0 < α < γ < 1`).  Geometrically it is the triangle `p, q, x` with two extra
flat vertices inserted on the side `[p, q]`, so the corner at `q` — the triple
`(c, q, x)` — is an ear avoiding both `a` and `c`.

This is the analogue of `flatSeam_quad_ear` one size up, and it is needed for the
same reason: when the tail `rest` is a triangle no ear of it is available from
the recursion hypothesis, so the pentagon has to be handled by hand. -/
lemma flat_pent_ear (a c q x p : ℂ) (α γ : ℝ)
    (hsimple : PolygonSimple [a, c, q, x, p])
    (hα : 0 < α) (hαγ : α < γ) (hγ : γ < 1)
    (hea : a - p = (α : ℂ) * (q - p)) (hec : c - p = (γ : ℂ) * (q - p)) :
    EmptyCornerData2 [a, c, q, x, p] a c := by
  have ha : a = p + (α : ℂ) * (q - p) := by linear_combination hea
  have hc : c = p + (γ : ℂ) * (q - p) := by linear_combination hec
  have hnd : ([a, c, q, x, p] : List ℂ).Nodup := hsimple.1
  have hqa : q ≠ a := by simp at hnd; tauto
  have hqc : q ≠ c := by simp at hnd; tauto
  have hqp : q ≠ p := by simp at hnd; tauto
  have hqp' : q - p ≠ 0 := sub_ne_zero.mpr hqp
  -- the apex `x` is off the line carrying the four collinear vertices
  have hK : HexArea.cross (q - p) (x - p) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := exists_real_of_cross_zero (q - p) (x - p) hqp' h
    refine not_collinear_of_simple [a, c, q, x, p] (by simp) hsimple p (q - p) hqp' ?_
    intro y hy
    simp at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact ⟨α, ha⟩
    · exact ⟨γ, hc⟩
    · exact ⟨1, by push_cast; ring⟩
    · exact ⟨t, by linear_combination ht⟩
    · exact ⟨0, by push_cast; ring⟩
  have c1 : HexArea.cross (q - c) (p - c) = 0 := by
    rw [hc]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c2 : HexArea.cross (q - c) (a - c) = 0 := by
    rw [ha, hc]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c3 : HexArea.cross (x - c) (p - c) = γ * HexArea.cross (q - p) (x - p) := by
    rw [hc]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have c4 : HexArea.cross (x - c) (a - c) = (γ - α) * HexArea.cross (q - p) (x - p) := by
    rw [ha, hc]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have e1 : HexArea.shoelace2 [c, q, x] = (1 - γ) * HexArea.cross (q - p) (x - p) := by
    rw [hc, shoelace2_triple_eq_cross]; simp [HexArea.cross, Complex.mul_re, Complex.mul_im]; ring
  have e2 : HexArea.shoelace2 [c, x, p, a] = γ * HexArea.cross (q - p) (x - p) := by
    rw [ha, hc]
    simp [HexArea.shoelace2, HexArea.shoelaceOpen, HexArea.cross, Complex.mul_re, Complex.mul_im]
    ring
  have hrot1 : ([a, c, q, x, p] : List ℂ).rotate 1 = c :: q :: x :: [p, a] := by
    rw [List.rotate_eq_drop_append_take (by simp)]; simp
  refine ⟨1, c, q, x, a, p, [p, a], hrot1, hqa, hqc, by simp, by simp, ?_, ?_, ?_⟩
  · intro y hy hin
    have hcase : y = p ∨ y = a := by simpa using hy
    rcases hcase with rfl | rfl
    · rcases hin with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> rw [c1] at h1 <;> simp at h1
    · rcases hin with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> rw [c2] at h1 <;> simp at h1
  · intro y hy hmem
    have hcase : y = p ∨ y = a := by simpa using hy
    rcases hcase with rfl | rfl
    · have hz := HexArea.cross_eq_zero_of_mem_segment c x y hmem
      rw [c3] at hz
      rcases mul_eq_zero.mp hz with h | h
      · linarith
      · exact hK h
    · have hz := HexArea.cross_eq_zero_of_mem_segment c x y hmem
      rw [c4] at hz
      rcases mul_eq_zero.mp hz with h | h
      · linarith
      · exact hK h
  · rw [e1, e2]; exact flatSeam_pos_iff _ _ _ (by linarith) (by linarith)

/-- **Re-inserting two flat seam vertices into an ear of the tail.**

When both seam corners of the clip `M = a :: c :: rest` are flat, the two clip
vertices `a` and `c` are interior points of the cyclic edge `(p, q)` of the tail
`rest`, occurring in the order `p, a, c, q` (parameters `0 < α < γ < 1`).  The
tail is a strictly shorter simple, cyclically non-degenerate polygon, so the
recursion hypothesis `IH` supplies an ear of `rest` avoiding the seam edge
`{p, q}`; re-inserting `a` and `c` into its tail produces the required ear of
`M`.

The geometric content — that the inserted vertices miss the ear triangle — is
`flatSeam_avoids_ear` (`RequestProject.SAWUmlaufFlatSeamLift`) applied twice with
`L := rest`, which *is* cyclically non-degenerate; the orientation clause follows
from `flatSeam_shoelace2_insert` applied twice.  The list surgery of the double
insertion is `flatSeam_insert_rotation` applied twice (first to `rest`, then to
`c :: rest`), and the `rest.length = 3` base case — where no ear of `rest` is
available from the recursion — is `flat_pent_ear`.

**Status: proved.**  Consumed by `clip_both_flat_ear`. -/
lemma clip_double_insert_ear (a c p q : ℂ) (rest : List ℂ) (h3 : 3 ≤ rest.length)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hMs : PolygonSimple (a :: c :: rest))
    (hRs : PolygonSimple rest) (hRnd : polyCycNondeg rest)
    (α γ : ℝ) (hα : 0 < α) (hαγ : α < γ) (hγ : γ < 1)
    (hea : a - p = (α : ℂ) * (q - p)) (hec : c - p = (γ : ℂ) * (q - p))
    (IH : ∀ M : List ℂ, M.length < rest.length + 3 → 4 ≤ M.length → PolygonSimple M →
       polyCycNondeg M → ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge M w1 w2) →
       EmptyCornerData2 M w1 w2) :
    EmptyCornerData2 (a :: c :: rest) a c := by
  have hane : a ∉ rest := by
    have h := hMs.1; rw [List.nodup_cons] at h
    intro hcon; exact h.1 (by simp [hcon])
  have hcne : c ∉ rest := by
    have h := hMs.1; rw [List.nodup_cons, List.nodup_cons] at h
    exact h.2.1
  rcases Nat.lt_or_ge rest.length 4 with hlt | h4
  · -- the pentagon base case
    have h3' : rest.length = 3 := by omega
    obtain ⟨q0, x0, p0, hR3⟩ : ∃ q0 x0 p0, rest = [q0, x0, p0] :=
      List.length_eq_three.mp h3'
    have hq0 : q0 = q := by rw [hR3] at hq; simpa using hq
    have hp0 : p0 = p := by rw [hR3] at hp; simpa using hp
    rw [hR3, hq0, hp0] at hMs ⊢
    exact flat_pent_ear a c q x0 p α γ hMs hα hαγ hγ hea hec
  -- the generic case: recurse on `rest` and re-insert `a` and `c`
  have hedge : IsCycEdge rest p q := by
    refine Or.inl ?_
    rw [HexArea.closedEdges_eq_pathEdges rest q p hq hp]
    simp
  obtain ⟨r, a', b', c', p₁, q₁, rest', hrot, hb1, hb2, hpp, hqq, hempty, hdiag, horient⟩ :=
    IH rest (by omega) h4 hRs hRnd p q (Or.inr hedge)
  obtain ⟨ρ, hρ, hrotρ⟩ := flatSeam_ear_index rest p q hq hp r a' b' c' rest' hrot hb2 hb1
  obtain ⟨hdrop, hrest, hrotN⟩ := flatSeam_insert_rotation c rest ρ a' b' c' rest' hρ hrotρ
  have hρ' : (ρ + 1) + 3 ≤ (c :: rest).length := by simp; omega
  obtain ⟨-, -, hrotM⟩ := flatSeam_insert_rotation a (c :: rest) (ρ + 1) a' b' c'
    (rest.drop (ρ + 3) ++ c :: rest.take ρ) hρ' hrotN
  have hTeq : (c :: rest).drop (ρ + 1 + 3) ++ a :: (c :: rest).take (ρ + 1)
      = rest.drop (ρ + 3) ++ a :: c :: rest.take ρ := by
    rw [show ρ + 1 + 3 = (ρ + 3) + 1 by omega, List.drop_succ_cons, List.take_succ_cons]
  rw [hTeq] at hrotM
  set T := rest.drop (ρ + 3) ++ a :: c :: rest.take ρ with hT
  obtain ⟨p₂, hp₂⟩ : ∃ y, T.getLast? = some y := by
    cases hcase : T.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hcase) (by simp [hT])
    | some y => exact ⟨y, rfl⟩
  obtain ⟨q₂, hq₂⟩ : ∃ y, T.head? = some y := by
    cases hcase : T.head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hcase) (by simp [hT])
    | some y => exact ⟨y, rfl⟩
  have hmem : ∀ y ∈ T, y = a ∨ y = c ∨ y ∈ rest' := by
    intro y hy
    rw [hT] at hy
    simp at hy
    rw [hrest]
    simp
    tauto
  have hb'rest : b' ∈ rest := (List.mem_rotate (n := ρ)).mp (by rw [hrotρ]; simp)
  have hgeoa := flatSeam_avoids_ear a rest p q α h4 hq hp hRs hRnd hα (by linarith) hea
    ρ a' b' c' rest' hrotρ hb1 hb2 hempty hdiag
  have hgeoc := flatSeam_avoids_ear c rest p q γ h4 hq hp hRs hRnd (by linarith) hγ hec
    ρ a' b' c' rest' hrotρ hb1 hb2 hempty hdiag
  -- the four seam conditions of the two shoelace insertions
  have hA : rest.drop (ρ + 3) ≠ [] → (rest.drop (ρ + 3)).getLast? = some p := by
    intro hAne
    have h := List.getLast?_append_of_ne_nil (rest.take (ρ + 3)) (l₂ := rest.drop (ρ + 3)) hAne
    rw [List.take_append_drop] at h
    rw [← h]; exact hp
  have hAe : rest.drop (ρ + 3) = [] → c' = p := by
    intro hAnil
    have hdrop3 : rest.drop ρ = [a', b', c'] := by rw [hdrop, hAnil]
    have h := List.getLast?_append_of_ne_nil (rest.take ρ) (l₂ := rest.drop ρ)
      (by rw [hdrop3]; simp)
    rw [List.take_append_drop, hdrop3] at h
    rw [hp] at h
    simp at h
    exact h.symm
  have hB : rest.take ρ ≠ [] → (rest.take ρ).head? = some q := by
    intro hBne
    have h := List.head?_append_of_ne_nil (l₂ := rest.drop ρ) (rest.take ρ) hBne
    rw [List.take_append_drop] at h
    rw [← h]; exact hq
  have hBe : rest.take ρ = [] → a' = q := by
    intro hBnil
    have hρ0 : ρ = 0 := by
      by_contra hcon
      have h0 : (rest.take ρ).length = 0 := by rw [hBnil]; rfl
      rw [List.length_take] at h0
      omega
    have hLeq : rest = a' :: b' :: c' :: rest.drop (ρ + 3) := by
      rw [← hdrop, hρ0]; simp
    rw [hLeq] at hq
    simp at hq
    exact hq
  have hγ0 : (γ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; linarith
  have hflat2 : a - p = ((α / γ : ℝ) : ℂ) * (c - p) := by
    rw [hea, hec, ← mul_assoc]
    congr 1
    push_cast
    field_simp
  have hshoe : HexArea.shoelace2 (a' :: c' :: T) = HexArea.shoelace2 (a' :: c' :: rest') := by
    rw [hT, hrest]
    have s2 := flatSeam_shoelace2_insert a' c' a p c (rest.drop (ρ + 3)) (c :: rest.take ρ)
      (α / γ) hflat2 hA hAe (by intro _; simp) (by simp)
    have s1 := flatSeam_shoelace2_insert a' c' c p q (rest.drop (ρ + 3)) (rest.take ρ)
      γ hec hA hAe hB hBe
    rw [s2, s1]
  refine ⟨ρ + 1 + 1, a', b', c', p₂, q₂, T, hrotM, ?_, ?_, hp₂, hq₂, ?_, ?_, ?_⟩
  · intro h; exact hane (h ▸ hb'rest)
  · intro h; exact hcne (h ▸ hb'rest)
  · intro y hy
    rcases hmem y hy with rfl | rfl | hy'
    · exact hgeoa.1
    · exact hgeoc.1
    · exact hempty y hy'
  · intro y hy
    rcases hmem y hy with rfl | rfl | hy'
    · exact hgeoa.2
    · exact hgeoc.2
    · exact hdiag y hy'
  · rw [hshoe]; exact horient

/-- **A clip whose *two* seam corners are both flat.**

When `cross (c - a) (p - a) = 0` and `cross (c - a) (q - a) = 0` the four
vertices `p, a, c, q` are collinear, and — because a vertex of a simple polygon
cannot lie in the interior of a non-incident edge — they occur in exactly that
order on their common line: `a` strictly between `p` and `c`, and `c` strictly
between `a` and `q`.  Both seam corners of the clip `M = a :: c :: rest` are then
flat and *two* successive deletions are needed before the recursion hypothesis
applies: delete `a` from `M` (leaving `c :: rest`, still flat at `c`), then
delete `c` (leaving `rest`, now cyclically non-degenerate by the same
positive-rescaling argument as in `clip_delete_a_nondeg`).

The configuration is genuinely realisable, so this is not a vacuous case.  A
concrete witness (with the tip `b` lexicographically minimal, as it is in the
Meisters search, and with an empty, base-clear corner at `b`):

    V = [(1,1), (0,3/2), (1,2), (1,3), (3,3), (3,0), (1,0)]

with `a = (1,1)`, `b = (0,3/2)`, `c = (1,2)`, `q = (1,3)`, `p = (1,0)`; the four
points `p, a, c, q` all lie on the line `x = 1`.

What is missing to close it is a version of `flatSeam_ear_lift`
(`RequestProject.SAWUmlaufFlatSeamLift`) that does not require the deletion to be
cyclically non-degenerate: its hypothesis `polyCycNondeg L` is used only to know
that the *ear corner* returned by the recursion is non-flat (through
`ear_edge_interior_not_strict` / `ear_edge_interior_not_base`).  Strengthening
`EmptyCornerData2` with that corner clause and threading it through the two lifts
is the remaining work.

**Status: reduced to `clip_double_insert_ear`.**  NOT a dead branch: consumed by
`clip_flat_ear`. -/
lemma clip_both_flat_ear (a b c p q : ℂ) (rest : List ℂ) (hrest2 : 2 ≤ rest.length)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hsimple : PolygonSimple (a :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (hfa : HexArea.cross (c - a) (p - a) = 0)
    (hfc : HexArea.cross (c - a) (q - a) = 0)
    (IH : ∀ M : List ℂ, M.length < rest.length + 3 → 4 ≤ M.length → PolygonSimple M →
       polyCycNondeg M → ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge M w1 w2) →
       EmptyCornerData2 M w1 w2) :
    EmptyCornerData2 (a :: c :: rest) a c := by
  classical
  obtain ⟨rest', rfl⟩ := List.head?_eq_some_iff.mp hq
  have hrest'ne : rest' ≠ [] := by
    intro h; rw [h] at hrest2; simp at hrest2
  have hp' : rest'.getLast? = some p := by
    cases rest' with
    | nil => exact absurd rfl hrest'ne
    | cons u s => simpa using hp
  -- `c` lies strictly between `a` and `q`
  obtain ⟨τ, hτ0, hτ1, hτ⟩ :=
    flat_between_of_cross_zero a c q rest' hrest'ne hsimple (by rw [cross_seam_c]; exact hfc)
  -- `a` lies strictly between `p` and `c`
  obtain ⟨s, hs⟩ := List.getLast?_eq_some_iff.mp hp
  have hrest'len : 1 ≤ rest'.length := List.length_pos_iff.mpr hrest'ne
  have hlen_s : s.length = rest'.length := by
    have h := congrArg List.length hs
    simp at h
    omega
  have hslen : 1 ≤ s.length := by omega
  obtain ⟨p₂, t, hst⟩ : ∃ p₂ t, s = t ++ [p₂] := by
    obtain ⟨y, hy⟩ : ∃ y, s.getLast? = some y := by
      cases hcase : s.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hcase) (by
          intro h; rw [h] at hslen; simp at hslen)
      | some y => exact ⟨y, rfl⟩
    obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp hy
    exact ⟨y, t, ht⟩
  have hreq : q :: rest' = t ++ [p₂, p] := by rw [hs, hst]; simp
  have hrot : (a :: c :: (q :: rest')).rotate (t.length + 3)
      = p :: a :: c :: (t ++ [p₂]) := by
    rw [hreq]
    rw [List.rotate_eq_drop_append_take (by simp)]
    rw [show t ++ [p₂, p] = (t ++ [p₂]) ++ [p] by simp]
    rw [show a :: c :: ((t ++ [p₂]) ++ [p]) = (a :: c :: (t ++ [p₂])) ++ [p] by simp]
    rw [List.drop_append_of_le_length (by simp), List.take_append_of_le_length (by simp)]
    simp
  have hRotSimple : PolygonSimple (p :: a :: c :: (t ++ [p₂])) := by
    rw [← hrot]
    exact (PolygonSimple_rotate _ _).mpr hsimple
  obtain ⟨σ, hσ0, hσ1, hσ⟩ :=
    flat_between_of_cross_zero p a c (t ++ [p₂]) (by simp) hRotSimple
      (by rw [cross_seam_a]; exact hfa)
  -- both are strictly between `p` and `q`, in the order `p, a, c, q`
  obtain ⟨α, γ, hα, hαγ, hγ, hea, hec⟩ :=
    flat_chain_params p a c q σ τ hσ0 hσ1 hτ0 hτ1 hσ hτ
  have hsega : a ∈ segment ℝ p q :=
    mem_segment_of_param p q α (le_of_lt hα) (by linarith) a hea
  have hsegc : c ∈ segment ℝ p q :=
    mem_segment_of_param p q γ (by linarith) (le_of_lt hγ) c hec
  -- with four collinear vertices the tail cannot be a single edge
  have h3 : 3 ≤ (q :: rest').length := by
    by_contra hcon
    simp at hcon
    have hlen2 : rest'.length = 1 := by omega
    obtain ⟨p', hp''⟩ : ∃ y, rest' = [y] := List.length_eq_one_iff.mp hlen2
    have hpp : p' = p := by rw [hp''] at hp'; simpa using hp'
    rw [hpp] at hp''
    rw [hp''] at hsimple
    have hnodup := hsimple.1
    simp [List.nodup_cons] at hnodup
    have hqp : q - p ≠ 0 := by
      refine sub_ne_zero.mpr (fun h => ?_)
      exact hnodup.2.2 h
    refine not_collinear_of_simple [a, c, q, p] (by simp) hsimple p (q - p) hqp ?_
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨α, by linear_combination hea⟩
    · exact ⟨γ, by linear_combination hec⟩
    · exact ⟨1, by push_cast; ring⟩
    · exact ⟨0, by push_cast; ring⟩
  -- decompose the tail as `s' ++ [p]` with `s'` non-empty
  obtain ⟨s', hs'⟩ := List.getLast?_eq_some_iff.mp hp'
  have hs'len : 1 ≤ s'.length := by
    have h := congrArg List.length hs'
    simp at h
    simp at h3
    omega
  have hs'ne : s' ≠ [] := by
    intro h; rw [h] at hs'len; simp at hs'len
  obtain ⟨q₂, hq₂⟩ : ∃ y, s'.head? = some y := by
    cases hcase : s'.head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hcase) hs'ne
    | some y => exact ⟨y, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ y, s'.getLast? = some y := by
    cases hcase : s'.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hcase) hs'ne
    | some y => exact ⟨y, rfl⟩
  have hsega_pc : a ∈ segment ℝ p c :=
    mem_segment_of_param p c σ (le_of_lt hσ0) (le_of_lt hσ1) a hσ
  have hsegc_aq : c ∈ segment ℝ a q :=
    mem_segment_of_param a q τ (le_of_lt hτ0) (le_of_lt hτ1) c hτ
  have hRs : PolygonSimple (q :: rest') :=
    clip_both_flat_delete_simple a c p q rest' s' hs' hsimple hsegc_aq hsega
  have hRnd : polyCycNondeg (q :: rest') :=
    clip_both_flat_delete_nondeg a b c p q p₂ q₂ rest' s' hs' hq₂ hp₂ hnd hsega hsegc hsega_pc
  exact clip_double_insert_ear a c p q (q :: rest') h3 hp hq hsimple hRs hRnd
    α γ hα hαγ hγ hea hec IH

/-! ## 7. The clip always carries an ear avoiding its diagonal -/

/-- **The clip of an empty, base-clear corner always carries a Meisters ear
avoiding the clip diagonal `{a, c}`**, whether or not its seam corners are flat.

Three cases: no flat seam corner (the clip is cyclically non-degenerate, by
`polyCycNondeg_clip`, and the recursion hypothesis applies directly), exactly one
(`clip_single_flat_ear`), or both (`clip_both_flat_ear`, still open).

NOT a dead branch: consumed by `empty_branch_flat_clip_lift`
(`RequestProject.SAWUmlaufPolyMeisters`). -/
lemma clip_flat_ear (a b c p q : ℂ) (rest : List ℂ) (hrest2 : 2 ≤ rest.length)
    (hp : rest.getLast? = some p) (hq : rest.head? = some q)
    (hsimple : PolygonSimple (a :: c :: rest))
    (hnd : polyCycNondeg (a :: b :: c :: rest))
    (IH : ∀ M : List ℂ, M.length < rest.length + 3 → 4 ≤ M.length → PolygonSimple M →
       polyCycNondeg M → ∀ w1 w2 : ℂ, (w1 = w2 ∨ IsCycEdge M w1 w2) →
       EmptyCornerData2 M w1 w2) :
    EmptyCornerData2 (a :: c :: rest) a c := by
  have hMlen : (a :: c :: rest).length = rest.length + 2 := by simp
  have hadjM : IsCycEdge (a :: c :: rest) a c := by
    unfold IsCycEdge; simp +decide [closedEdges]
  have IH' : ∀ M : List ℂ, M.length < (a :: c :: rest).length → 4 ≤ M.length →
      PolygonSimple M → polyCycNondeg M → ∀ w1 w2 : ℂ,
      (w1 = w2 ∨ IsCycEdge M w1 w2) → EmptyCornerData2 M w1 w2 := by
    intro M hM
    exact IH M (by rw [hMlen] at hM; omega)
  by_cases hfa : HexArea.cross (c - a) (p - a) = 0 <;>
    by_cases hfc : HexArea.cross (c - a) (q - a) = 0
  · exact clip_both_flat_ear a b c p q rest hrest2 hp hq hsimple hnd hfa hfc IH
  · exact clip_single_flat_ear a b c p q rest hrest2 hp hq hsimple hnd (Or.inl ⟨hfa, hfc⟩) IH'
  · exact clip_single_flat_ear a b c p q rest hrest2 hp hq hsimple hnd (Or.inr ⟨hfa, hfc⟩) IH'
  · -- no flat seam corner: the clip is cyclically non-degenerate
    have hMnd : polyCycNondeg (a :: c :: rest) :=
      polyCycNondeg_clip a b c p q rest hq hp hnd
        (by rw [cross_seam_a]; exact hfa) (by rw [cross_seam_c]; exact hfc)
    exact IH (a :: c :: rest) (by rw [hMlen]; omega) (by simp; omega) hsimple hMnd a c
      (Or.inr hadjM)

end
