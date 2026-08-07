/-
# Pair Cancellation for the Vertex Relation (Lemma 1)

Proves that the pair part of the vertex sum vanishes, completing the
proof of the cancellation identity.

## Key results
* `pair_winding_relation` — the winding relation for loop-reversed pairs
  (sorry: the geometric route to it is under construction in
  `RequestProject.SAWPairLoopWinding` / `RequestProject.SAWPairLoopOrientation`,
  which this file imports)
* `pair_contrib_cancels` — each pair's contribution to the vertex sum is zero
  (proved from pair_winding_relation)
* `freshVertexSum_pair_part_zero_proof` — the pair part of the vertex sum vanishes
  (proved from pair_contrib_cancels + involution structure)

The *definitions* of the involution (`pairExitIdx`, `pairInner`, `pairPrefix`,
`pairInvol`, …) now live in `RequestProject.SAWPairInvolDefs`.
-/

import Mathlib
import RequestProject.SAWPairLoopOrientation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000


/-! ## Pair winding relation

**The key geometric fact**: For a FreshIncomingPair γ at k, the walk
decomposes as prefix + loop. The loop-reversed paired walk has winding
that satisfies the pair algebraic identity.

This encapsulates the turning number theorem for simple closed curves
on the hexagonal lattice: a simple closed trail has total exterior
angle ±2π.

It is now **derived** from `pair_winding_relation_geom`
(`RequestProject.SAWPairLoopWinding`), which decomposes the walk as
prefix + closed loop, applies the discrete Umlaufsatz
`hex_closed_trail_turning_number` to the loop, and adds the local angle
bookkeeping at `v`.  The remaining gaps are the ones listed there. -/

/-- The winding relation for pairs (corrected: allows both orderings).

    The disjunction covers both loop orientations (clockwise/counterclockwise).
    In each case, the algebraic pair cancellation identity applies.
    Proved from `pair_winding_relation_geom`. -/
lemma pair_winding_relation {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∃ (W_common : ℝ) (j : Fin 3),
      ((k = (fin3_other j).1 ∧ pairExitIdx hv_ne γ = (fin3_other j).2 ∧
        γ.1.winding = W_common - 4 * Real.pi / 3 ∧
        (pairInvol hv hv_ne γ).1.winding = W_common + 4 * Real.pi / 3) ∨
       (k = (fin3_other j).2 ∧ pairExitIdx hv_ne γ = (fin3_other j).1 ∧
        γ.1.winding = W_common + 4 * Real.pi / 3 ∧
        (pairInvol hv hv_ne γ).1.winding = W_common - 4 * Real.pi / 3)) ∧
      (pairInvol hv hv_ne γ).1.len = γ.1.len :=
  pair_winding_relation_geom hv hv_ne γ

/-! ## Algebraic helpers for pair_exp_cancellation

These lemmas connect the winding relation from pair_winding_relation
to the algebraic pair_cancellation identity. -/

/-- For each j_idx, the midEdgeDirs at the fin3_other indices cancel
    with conj(λ)⁴ and λ⁴ weights. Proved from pair_cancellation by
    fin_cases on j_idx. -/
private lemma fin3_other_pair_cancel (v : HexVertex) (j_idx : Fin 3) :
    midEdgeDir v (fin3_other j_idx).1 * conj lam ^ 4 +
    midEdgeDir v (fin3_other j_idx).2 * lam ^ 4 = 0 := by
  fin_cases j_idx <;> simp +decide [ * ] <;> ring_nf <;> norm_num [ Complex.ext_iff, sq ] at *;
  · simp +decide [ fin3_other, midEdgeDir_j_relation ] at * ; ring_nf at * ;
    have := pair_cancellation; simp_all +decide [ Complex.ext_iff, pow_succ ] ; ring_nf at * ; norm_num at *;
    norm_num [ show lam ^ 4 = lam ^ 2 * lam ^ 2 by ring, show ( starRingEnd ℂ lam ) ^ 4 = ( starRingEnd ℂ lam ) ^ 2 * ( starRingEnd ℂ lam ) ^ 2 by ring, pow_two ] at * ; ring_nf at * ;
    exact ⟨ by linear_combination' this * ( midEdgeDir v 0 |> Complex.re ), by linear_combination' this * ( midEdgeDir v 0 |> Complex.im ) ⟩;
  · unfold fin3_other; simp +decide [ *, midEdgeDir_j_relation ] ; ring_nf ;
    unfold j lam; norm_num [ pow_succ ] ; ring_nf ;
    erw [ show ( starRingEnd ℂ ( Complex.exp ( Complex.I * Real.pi * ( -5 / 24 ) ) ) ) ^ 4 = ( starRingEnd ℂ ( Complex.exp ( Complex.I * Real.pi * ( -5 / 24 ) ) ^ 4 ) ) by simp +decide [ map_pow ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ] ; ring_nf ; norm_num [ mul_div ] ;
    norm_num [ show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring, show Real.pi * 5 / 6 = Real.pi - Real.pi / 6 by ring ] ; ring ; norm_num;
    constructor <;> ring;
  · unfold fin3_other; simp +decide [ midEdgeDir_j_relation, j_cube_eq_one', j_sq_eq_conj' ] ; ring_nf;
    unfold lam j; norm_num [ pow_succ ] ; ring_nf; norm_num;
    erw [ show ( starRingEnd ℂ ) ( Complex.exp ( - ( Complex.I * Real.pi * ( 5 / 24 ) ) ) ) ^ 4 = ( starRingEnd ℂ ) ( Complex.exp ( - ( Complex.I * Real.pi * ( 5 / 24 ) ) ) ^ 4 ) by rw [ map_pow ] ] ; norm_num [ Complex.exp_re, Complex.exp_im, ← Complex.exp_nat_mul ] ; ring_nf ; norm_num [ mul_div ] ;
    norm_num [ show Real.pi * 5 / 6 = Real.pi - Real.pi / 6 by ring, show Real.pi * 2 / 3 = Real.pi - Real.pi / 3 by ring ] ; ring ; norm_num;
    constructor <;> ring

private lemma exp_shift_minus' (W : ℝ) :
    Complex.exp (-Complex.I * ↑sigma * ↑(W - 4 * Real.pi / 3)) =
    Complex.exp (-Complex.I * ↑sigma * ↑W) * conj lam ^ 4 := by
  rw [ show lam = Complex.exp ( -I * ( 5 * Real.pi / 24 ) ) from rfl ] ; rw [ ← Complex.exp_conj ] ; rw [ ← Complex.exp_nat_mul ] ; rw [ ← Complex.exp_add ] ; push_cast [ sigma ] ; ring;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ; ring;
  norm_num [ Complex.normSq, Complex.inv_re, Complex.inv_im, Complex.conj_ofReal ] ; ring ; norm_num

private lemma exp_shift_plus' (W : ℝ) :
    Complex.exp (-Complex.I * ↑sigma * ↑(W + 4 * Real.pi / 3)) =
    Complex.exp (-Complex.I * ↑sigma * ↑W) * lam ^ 4 := by
  unfold lam
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]; norm_num [sigma]; ring

/-- The exp constraint for pair cancellation.

    **Proved** from pair_winding_relation + algebraic lemmas.
    The only remaining sorry in the chain is pair_winding_relation
    (the discrete turning number theorem for hex lattice loops).
    Handles both orderings of the pair indices. -/
lemma pair_exp_cancellation {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    midEdgeDir v k * Complex.exp (-Complex.I * ↑sigma * ↑γ.1.winding) +
    midEdgeDir v (pairExitIdx hv_ne γ) *
      Complex.exp (-Complex.I * ↑sigma * ↑(pairInvol hv hv_ne γ).1.winding) = 0 := by
  obtain ⟨W_common, j_idx, h_cases, _⟩ := pair_winding_relation hv hv_ne γ
  have h := fin3_other_pair_cancel v j_idx
  rcases h_cases with ⟨hk, hexit, hw1, hw2⟩ | ⟨hk, hexit, hw1, hw2⟩ <;>
    simp only [hw1, hw2, hk, hexit, exp_shift_minus', exp_shift_plus'] <;>
    linear_combination Complex.exp (-Complex.I * ↑sigma * ↑W_common) * h

/-! ## Pair contribution cancels

Using the winding relation and the algebraic pair identity
  j · conj(λ)⁴ + conj(j) · λ⁴ = 0
the contribution of each pair to the vertex sum is zero. -/

/-- Each pair's contribution to the vertex sum is zero.

    Uses `pair_exp_cancellation` (the clean geometric sorry)
    rather than `pair_winding_relation`. The proof factors out xc^ℓ
    and uses the exp constraint directly. -/
lemma pair_contrib_cancels {T L : ℕ} (v : HexVertex) {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    midEdgeDir v k * γ.1.weight +
    midEdgeDir v (pairExitIdx hv_ne γ) * (pairInvol hv hv_ne γ).1.weight = 0 := by
  have h_len := pairInvol_length hv hv_ne γ
  have h_exp := pair_exp_cancellation hv hv_ne γ
  unfold FreshTrail.weight walkWeight
  rw [h_len]
  -- Factor out (↑xc)^ℓ
  have : midEdgeDir v k * (Complex.exp (-Complex.I * ↑sigma * ↑γ.1.winding) * ↑xc ^ γ.1.len) +
      midEdgeDir v (pairExitIdx hv_ne γ) *
        (Complex.exp (-Complex.I * ↑sigma * ↑(pairInvol hv hv_ne γ).1.winding) * ↑xc ^ γ.1.len) =
      (midEdgeDir v k * Complex.exp (-Complex.I * ↑sigma * ↑γ.1.winding) +
       midEdgeDir v (pairExitIdx hv_ne γ) *
        Complex.exp (-Complex.I * ↑sigma * ↑(pairInvol hv hv_ne γ).1.winding)) * ↑xc ^ γ.1.len := by
    ring
  rw [this, h_exp, zero_mul]

/-! ## The pair part of the vertex sum vanishes

The pair part of the vertex sum vanishes by the S = -S argument using
the pair involution. This is proved as `freshVertexSum_pair_part_zero_proved`
in SAWPairInvolutionProof.lean (which imports this file). The proof uses
`pairSigmaInvol_injective` + `pairSigmaContrib_neg` from the involution
infrastructure. -/

end