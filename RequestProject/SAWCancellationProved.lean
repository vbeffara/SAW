/-
# Cancellation Identity — Key Lemmas

Proves key helper lemmas for the vertex relation (Lemma 1) of
Duminil-Copin & Smirnov (2012).

## Main results

* `direction_ratio_clockwise` — direction ratio for clockwise extension
* `direction_ratio_counterclockwise` — direction ratio for counterclockwise extension
* `turning_angle_clockwise` — turning angle at v for clockwise extension is -π/3
* `turning_angle_counterclockwise` — turning angle for counterclockwise extension is +π/3
* `triplet_algebraic_zero` — concrete triplet sum at a vertex is zero
-/

import Mathlib
import RequestProject.SAWCancellationIdentity

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Turning angle computations

The direction ratio at v when going from n_idx through v to n_k equals
  (embed(n_k) - embed(v)) / (embed(v) - embed(n_idx))
= midEdgeDir v k / (-midEdgeDir v idx)
= -midEdgeDir v k / midEdgeDir v idx

By the j-relation:
  midEdgeDir v k = j^{f(k)} * midEdgeDir v 0
This ratio simplifies to -j^{f(k)-f(idx)}.

For k = (fin3_other idx).1: ratio = -j, arg = -π/3.
For k = (fin3_other idx).2: ratio = -conj(j), arg = π/3.
-/

/-
The direction ratio from n_idx through v to n_k, for the clockwise case.
    (fin3_other idx).1 is the clockwise neighbor.
-/
lemma direction_ratio_clockwise (v : HexVertex) (idx : Fin 3) :
    (correctHexEmbed (hexNeighbors3 v (fin3_other idx).1) - correctHexEmbed v) /
    (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v idx)) = -(j : ℂ) := by
  fin_cases idx <;> simp +decide [ Fin.forall_fin_succ ];
  · unfold hexNeighbors3;
    unfold fin3_other;
    split_ifs <;> simp +decide [ *, j ];
    · unfold correctHexEmbed; norm_num [ trueNeighbors ] ; ring; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, mul_div ] ;
      rcases v with ⟨ x, y, b ⟩ ; rcases b with ( _ | _ ) <;> norm_num [ Complex.normSq ] <;> ring_nf <;> norm_num [ mul_div ] ;
      · contradiction;
      · norm_num [ show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring ];
    · unfold correctHexEmbed falseNeighbors; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
      rcases v with ⟨ x, y, b ⟩ ; rcases b with ( _ | _ ) <;> norm_num [ Complex.normSq ] ; ring ; norm_num;
      contradiction;
  · obtain ⟨ x, y, b ⟩ := v;
    cases b <;> simp +decide [ correctHexEmbed, hexNeighbors3 ];
    · unfold falseNeighbors;
      unfold fin3_other; norm_num [ Complex.ext_iff, j ] ; ring;
      norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
    · unfold trueNeighbors;
      unfold fin3_other; norm_num [ Complex.ext_iff, j ] ; ring;
      norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
  · rcases v with ⟨ x, y, b ⟩;
    unfold correctHexEmbed hexNeighbors3 fin3_other j; simp +decide [ Complex.ext_iff ] ; ring;
    cases b <;> simp +decide [ trueNeighbors, falseNeighbors ] <;> ring_nf <;> norm_num [ Complex.exp_re, Complex.exp_im, mul_div ]; all_goals norm_num [ Complex.normSq, show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num

/-
The direction ratio for the counterclockwise case.
-/
lemma direction_ratio_counterclockwise (v : HexVertex) (idx : Fin 3) :
    (correctHexEmbed (hexNeighbors3 v (fin3_other idx).2) - correctHexEmbed v) /
    (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v idx)) = -(conj (j : ℂ)) := by
  by_cases h : correctHexEmbed v - correctHexEmbed ( hexNeighbors3 v idx ) = 0 <;> simp_all +decide [ div_eq_iff, mul_assoc ];
  · fin_cases idx <;> simp_all +decide [ sub_eq_zero ];
    · unfold correctHexEmbed at h; unfold hexNeighbors3 at h;
      rcases v with ⟨ x, y, b ⟩ ; simp +decide [ trueNeighbors, falseNeighbors ] at h ⊢;
      cases b <;> simp +decide [ trueNeighbors, falseNeighbors ] at h;
    · unfold correctHexEmbed at h; rcases v with ⟨ x, y, b ⟩ ; simp_all +decide [ hexNeighbors3 ] ;
      cases b <;> simp_all +decide [ trueNeighbors, falseNeighbors ];
      linarith;
    · unfold correctHexEmbed at h;
      unfold hexNeighbors3 at h; rcases v with ⟨ x, y, b ⟩ ; norm_num [ Complex.ext_iff ] at h;
      cases b <;> norm_num [ trueNeighbors, falseNeighbors ] at h ; ring_nf at h ; norm_num at h;
  · fin_cases idx <;> simp +decide [ *, hexNeighbors3 ];
    · unfold fin3_other; split_ifs <;> simp_all +decide [ trueNeighbors, falseNeighbors ] ;
      · grind +suggestions;
      · unfold correctHexEmbed; simp +decide [ *, j ] ; ring;
        erw [ show ( v : HexVertex ) = ( v.1, v.2.1, false ) by cases v; aesop ] ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring;
        norm_num;
    · split_ifs <;> simp_all +decide [ trueNeighbors, falseNeighbors, fin3_other ];
      · grind +suggestions;
      · unfold correctHexEmbed j; simp +decide [ *, Complex.ext_iff ] ; ring;
        rw [ show v = ( v.1, v.2.1, false ) by cases v; aesop ] ; norm_num [ Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
    · unfold fin3_other; simp +decide [ *, trueNeighbors, falseNeighbors ] ; ring;
      split_ifs <;> simp +decide [ *, trueNeighbors, falseNeighbors ] <;> ring!;
      · unfold correctHexEmbed; simp +decide [ *, Complex.ext_iff ] ; ring;
        rcases v with ⟨ x, y, b ⟩ ; rcases b with ( _ | _ | b ) <;> norm_num [ j ] <;> ring_nf <;> norm_num;
        · contradiction;
        · norm_num [ Complex.exp_re, Complex.exp_im, show Real.pi * ( 2 / 3 ) = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
      · grind +suggestions

/-- The turning angle at v going from n_idx to the clockwise neighbor is -π/3. -/
lemma turning_angle_clockwise (v : HexVertex) (idx : Fin 3) :
    Complex.arg ((correctHexEmbed (hexNeighbors3 v (fin3_other idx).1) - correctHexEmbed v) /
                 (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v idx))) =
    -(Real.pi / 3) := by
  rw [direction_ratio_clockwise]
  convert arg_neg_j using 1
  ring

/-- The turning angle at v going from n_idx to the counterclockwise neighbor is +π/3. -/
lemma turning_angle_counterclockwise (v : HexVertex) (idx : Fin 3) :
    Complex.arg ((correctHexEmbed (hexNeighbors3 v (fin3_other idx).2) - correctHexEmbed v) /
                 (correctHexEmbed v - correctHexEmbed (hexNeighbors3 v idx))) =
    Real.pi / 3 := by
  rw [direction_ratio_counterclockwise]
  exact arg_neg_conj_j

/-! ## The triplet algebraic identity at a vertex -/

/-- The triplet algebraic cancellation at any vertex. -/
theorem triplet_algebraic_zero (v : HexVertex) (idx : Fin 3) (W : ℝ) (ℓ : ℕ) :
    midEdgeDir v idx * walkWeight W ℓ xc sigma +
    midEdgeDir v (fin3_other idx).1 * walkWeight (W - Real.pi / 3) (ℓ + 1) xc sigma +
    midEdgeDir v (fin3_other idx).2 * walkWeight (W + Real.pi / 3) (ℓ + 1) xc sigma = 0 := by
  have h := strip_triplet_zero v idx W ℓ
  simp only [stripTrailContrib] at h
  exact h

end