/-
# Point-winding infrastructure toward Jordan separation (`ptWind` cont.)

This file continues the development of the **winding number of a closed polygon
around a base point** `ptWind` (defined in `RequestProject.SAWUmlaufPtWind`)
with the structural, non-self-intersection-free lemmas needed to turn `ptWind`
into the point-in-polygon separator that discharges the single irreducible
Jordan-separation gap `chord_ear_empty_other` of the discrete Hopf Umlaufsatz
(`RequestProject.SAWUmlaufPolygon`).

## Contents (all independent of `PolygonSimple`, so they live *below*
`SAWUmlaufPtWind` and *above* `SAWUmlaufPolygon` in the import graph)

* `exp_I_ptTurn` — the telescoping identity
  `exp (I · ptTurn x L) = (last-x)/(head-x) / ‖…‖` for an open chain whose
  vertices all avoid `x` (the product of the sweep unit ratios telescopes).
* `ptWind_int` — for a closed polygon `V` all of whose vertices avoid `x`, the
  winding number `ptWind x V` is an **integer multiple of `2π`** (the closed
  product telescopes to `1`, so `exp (I · ptWind) = 1`).
* `ptWind_rotate1`, `ptWind_rotate` — **rotation invariance**: `ptWind` of a
  cyclic rotation of the vertex list equals `ptWind` of the original (the sum
  ranges over the same cyclic set of directed edges).
* `ptWind_diagonal_split` — **diagonal-cut additivity**: cutting the closed
  polygon `V` along the diagonal `V[0]–V[k]` into `chordLeft V k` /
  `chordRight V k` splits the winding number additively, provided `x` is off the
  (open) diagonal segment (the two closing edges of the pieces are the diagonal
  traversed in opposite directions and cancel).  This is the `ptWind` analogue
  of `HexArea.shoelace2_chord_split`.

## Downstream use (NOT a dead branch)

This file is imported by `RequestProject.SAWUmlaufPolygon`, feeding the
Jordan-separation keystone `chord_ear_empty_other`: with `ptWind_diagonal_split`
the winding of the whole polygon around a vertex `x` of one chord piece splits as
`ptWind x P + ptWind x Q`; combined with the point-in-polygon behaviour of
`ptWind` (target of future rounds) this pins the winding of a piece around a
vertex of the *other* piece to `0`, separating the two pieces.
-/

import Mathlib
import RequestProject.SAWUmlaufPtWind
import RequestProject.SAWUmlaufEarSplit

open Real Complex

noncomputable section

namespace HexArea

set_option maxHeartbeats 4000000

/-- **Concatenation telescoping of `ptTurn`.**  Splitting an open chain at an
    interior vertex `b` inserts exactly one seam sweep angle: the sweep from the
    last vertex of the first part to `b`.  This is the additivity backbone of
    both the rotation invariance and the diagonal-cut additivity below. -/
lemma ptTurn_append (x b : ℂ) :
    ∀ (a : ℂ) (L M : List ℂ),
      ptTurn x (a :: L ++ b :: M)
        = ptTurn x (a :: L)
            + Complex.arg ((b - x) / (((a :: L).getLastD a) - x))
            + ptTurn x (b :: M) := by
  intro a L
  induction L generalizing a with
  | nil => intro M; simp [ptTurn_cons_cons]
  | cons c L' ih =>
      intro M
      have := ih c M
      simp only [List.cons_append, ptTurn_cons_cons, List.getLastD_cons] at *
      rw [this]; ring

/-
**Telescoping of the sweep-angle exponential.**  For an open chain `L` whose
    vertices all avoid the base point `x`, the exponential of `I · ptTurn x L`
    telescopes: the product of the unit sweep ratios `((next-x)/(cur-x))/‖…‖`
    collapses to the endpoint ratio `((last-x)/(head-x)) / ‖(last-x)/(head-x)‖`.

    Stated for a non-empty chain `a :: L`, with `getLastD` supplying the last
    vertex (default irrelevant since the chain is non-empty).
-/
lemma exp_I_ptTurn (x : ℂ) :
    ∀ (a : ℂ) (L : List ℂ), (∀ v ∈ (a :: L), v ≠ x) →
      Complex.exp (Complex.I * ptTurn x (a :: L))
        = ((a :: L).getLastD a - x) / (a - x)
            / (‖((a :: L).getLastD a - x) / (a - x)‖ : ℂ) := by
  intro a L hL
  induction' L with b L ih generalizing a;
  · simp_all +decide [ sub_ne_zero ];
  · -- Apply the definition of `ptTurn` to split the list into the first element and the rest.
    have h_ptTurn : ptTurn x (a :: b :: L) = Complex.arg ((b - x) / (a - x)) + ptTurn x (b :: L) := by
      grind +suggestions;
    simp_all +decide [ Complex.exp_add, mul_add, add_mul, Complex.exp_add ];
    have h_exp_arg : Complex.exp (I * Complex.arg ((b - x) / (a - x))) = ((b - x) / (a - x)) / ‖((b - x) / (a - x))‖ := by
      have := Complex.norm_mul_exp_arg_mul_I ( ( b - x ) / ( a - x ) ) ; simp_all +decide [ mul_comm ] ;
      exact eq_div_of_mul_eq ( div_ne_zero ( Complex.ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr <| sub_ne_zero.mpr hL.2.1 ) ( Complex.ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr <| sub_ne_zero.mpr hL.1 ) ) this;
    simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, sub_eq_iff_eq_add ];
    cases L <;> aesop

/-
**The winding number of a closed polygon is an integer multiple of `2π`.**
    If every vertex of `V` avoids the base point `x`, then the closed product of
    sweep ratios telescopes to `1`, so `exp (I · ptWind x V) = 1`, forcing
    `ptWind x V ∈ 2π·ℤ`.  This is the discreteness backbone of the
    point-in-polygon argument (a winding number that is continuous in `x` off the
    polygon and integer-valued is locally constant).
-/
lemma ptWind_int (x : ℂ) (V : List ℂ) (h : ∀ v ∈ V, v ≠ x) :
    ∃ n : ℤ, ptWind x V = 2 * Real.pi * n := by
  have h_exp_eq_one : Complex.exp (Complex.I * ptWind x V) = 1 := by
    by_cases hV : V = [];
    · simp [hV, ptWind];
    · obtain ⟨a, t, rfl⟩ : ∃ a t, V = a :: t := by
        exact List.exists_cons_of_ne_nil hV;
      have h_exp : Complex.exp (Complex.I * ptTurn x (a :: (t ++ [a]))) = ((a - x) / (a - x)) / ‖(a - x) / (a - x)‖ := by
        convert exp_I_ptTurn x a ( t ++ [ a ] ) _ using 1;
        · simp +decide [ List.getLastD ];
        · grind;
      simp_all +decide [ sub_ne_zero ];
      unfold ptWind; aesop;
  rw [ Complex.exp_eq_one_iff ] at h_exp_eq_one; obtain ⟨ n, hn ⟩ := h_exp_eq_one; exact ⟨ n, by norm_num [ Complex.ext_iff ] at *; linarith ⟩ ;

/-
**Rotation invariance of the point-winding (single step).**  Moving the first
    vertex of the cycle to the end does not change the winding number: both sides
    sum the sweep angles over the same cyclic set of directed edges.
-/
lemma ptWind_rotate1 (x : ℂ) (V : List ℂ) :
    ptWind x (V.rotate 1) = ptWind x V := by
  rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ List.rotate ];
  unfold ptWind; simp +decide [ ptTurn ] ;
  grind +suggestions

/-- **Rotation invariance of the point-winding.**  A cyclic rotation of the
    vertex list leaves the winding number unchanged. -/
lemma ptWind_rotate (x : ℂ) (V : List ℂ) (s : ℕ) :
    ptWind x (V.rotate s) = ptWind x V := by
  induction s with
  | zero => simp
  | succ n ih =>
      rw [← List.rotate_rotate, ptWind_rotate1, ih]

/-
**Diagonal-cut additivity of the point-winding** (the `ptWind` analogue of
    `HexArea.shoelace2_chord_split`).  Cutting the closed polygon `V` along the
    diagonal `V[0]–V[k]` (`1 ≤ k < V.length`) into the two chord pieces
    `chordLeft V k` and `chordRight V k` splits the winding number about `x`
    additively, provided `x` does not lie on the (closed) diagonal segment
    `[V[0], V[k]]`.  The two pieces each close along the diagonal, traversed in
    opposite directions; those two contributions cancel (their sweep angles are
    negatives, since `x` is off the diagonal), and the remaining open sweeps
    reassemble the closed sweep of `V`.
-/
lemma ptWind_diagonal_split (x : ℂ) (V : List ℂ) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k < V.length) (hx : x ∉ segment ℝ (V[0]!) (V[k]!)) :
    ptWind x (chordLeft V k) + ptWind x (chordRight V k) = ptWind x V := by
  obtain ⟨a, L, hL⟩ : ∃ a L, V.take k = a :: L ∧ L.length = k - 1 := by
    rcases k with ( _ | k ) <;> simp_all +decide [ List.length_take ];
    rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ List.take ];
    · contradiction;
    · grind;
    · grind;
  obtain ⟨b, M, hM⟩ : ∃ b M, V.drop k = b :: M ∧ M.length = V.length - k - 1 := by
    rcases h : List.drop k V with ( _ | ⟨ b, M ⟩ ) <;> simp_all +decide [ List.length_drop ];
    · linarith;
    · replace h := congr_arg List.length h; simp_all +decide [ Nat.sub_sub ] ;
  simp_all +decide [ chordLeft, chordRight ];
  rw [ show List.take ( k + 1 ) V = a :: L ++ [ b ] from ?_, show V = a :: L ++ b :: M from ?_ ];
  · have h_arg_sum : Complex.arg ((a - x) / (b - x)) + Complex.arg ((b - x) / (a - x)) = 0 := by
      rw [ ← inv_div, Complex.arg_inv ];
      split_ifs <;> simp_all +decide [ Complex.arg_eq_pi_iff ];
      have h_arg_neg : ∃ t : ℝ, t < 0 ∧ (b - x) / (a - x) = t := by
        exact ⟨ ( ( b - x ) / ( a - x ) |> Complex.re ), by linarith, by simpa [ Complex.ext_iff ] using by linarith ⟩;
      obtain ⟨ t, ht, ht' ⟩ := h_arg_neg; rw [ ht' ] ; norm_num [ Complex.arg_ofReal_of_neg ht ] ;
      have h_arg_neg : x ∈ segment ℝ a b := by
        rw [ div_eq_iff ] at ht';
        · rw [ segment_eq_image ];
          use 1 / (1 - t);
          norm_num [ Complex.ext_iff ] at *;
          norm_num [ Complex.normSq ];
          exact ⟨ ⟨ by linarith, inv_le_one_of_one_le₀ <| by linarith ⟩, by nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 - t ) ≠ 0 ) ( a.re ), inv_mul_cancel_left₀ ( by linarith : ( 1 - t ) ≠ 0 ) ( b.re ) ], by nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( 1 - t ) ≠ 0 ) ( a.im ), inv_mul_cancel_left₀ ( by linarith : ( 1 - t ) ≠ 0 ) ( b.im ) ] ⟩;
        · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have h_arg_neg : a = V[0]! ∧ b = V[k]! := by
        have h_arg_neg : a = V[0]! := by
          rcases V with ( _ | ⟨ a, _ | ⟨ b, V ⟩ ⟩ ) <;> simp_all +decide [ List.take ];
          · grind;
          · cases k <;> aesop
        have h_arg_neg' : b = V[k]! := by
          replace hM := congr_arg List.head? hM.1; aesop;
        exact ⟨h_arg_neg, h_arg_neg'⟩;
      aesop;
    simp_all +decide [ ptWind, ptTurn_append ];
    grind +suggestions;
  · rw [ ← hL.1, ← hM.1, List.take_append_drop ];
  · grind

/-- **Ear-split of the point-winding around an interior point of the ear.**
    If `(a', b', c')` is a consecutive triple of the cyclic polygon `P` (via a
    rotation) and `x` lies strictly inside the ear triangle `a', b', c'`, then
    the winding of `P` around `x` is the winding of the ear-clipped polygon
    `a' :: c' :: tlP` plus the (nonzero) triangle winding `±2π`.  This composes
    `ptWind_rotate`, `ptWind_ear_clip`, and `ptWind_triangle`, reducing the
    "inside-ear ⟹ winding ≠ 0" point-in-polygon direction to the winding of the
    smaller clipped polygon around the (now exterior) point `x`.  The
    off-diagonal hypothesis `hac : x ∉ segment ℝ a' c'` is automatic from `hin`
    (a strict interior point is off every edge line), but is kept explicit so
    the lemma can be used before that derivation. -/
lemma ptWind_ear_split (x a' b' c' : ℂ) (P : List ℂ) (s : ℕ) (tlP : List ℂ)
    (hrot : P.rotate s = a' :: b' :: c' :: tlP)
    (hac : x ∉ segment ℝ a' c')
    (hin : inTriangleStrict a' b' c' x) :
    ptWind x P
      = ptWind x (a' :: c' :: tlP)
          + 2 * Real.pi * (if 0 < shoelace2 [a', b', c'] then 1 else -1) := by
  rw [← ptWind_rotate x P s, hrot, ptWind_ear_clip a' b' c' x tlP hac,
    ptWind_triangle a' b' c' x hin]

end HexArea

end