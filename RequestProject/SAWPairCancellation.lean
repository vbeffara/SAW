/-
# Pair Cancellation for the Vertex Relation (Lemma 1)

Proves that the pair part of the vertex sum vanishes, completing the
proof of the cancellation identity.

## Key results
* `pair_winding_relation` — the winding relation for loop-reversed pairs
  (sorry: requires turning number theorem for hex lattice loops)
* `pair_contrib_cancels` — each pair's contribution to the vertex sum is zero
  (proved from pair_winding_relation)
* `freshVertexSum_pair_part_zero_proof` — the pair part of the vertex sum vanishes
  (proved from pair_contrib_cancels + involution structure)
-/

import Mathlib
import RequestProject.SAWPairWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## The pair involution on FreshIncomingPair -/

/-- The exit index of a FreshIncomingPair walk. -/
noncomputable def pairExitIdx {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) : Fin 3 :=
  (pair_exit_neighbor γ hv_ne).choose

/-- The exit index is not k. -/
lemma pairExitIdx_ne {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    pairExitIdx hv_ne γ ≠ k :=
  (pair_exit_neighbor γ hv_ne).choose_spec.choose

/-- The inner walk of a FreshIncomingPair. -/
noncomputable def pairInner {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexGraph.Walk (hexNeighbors3 v (pairExitIdx hv_ne γ)) (hexNeighbors3 v k) :=
  (pair_exit_neighbor γ hv_ne).choose_spec.choose_spec.choose

/-- The suffix decomposition. -/
lemma pairSuffix_spec {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    γ.1.walk.dropUntil v (pair_walk_v_in_support γ hv_ne) =
    .cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ)) (pairInner hv_ne γ) :=
  (pair_exit_neighbor γ hv_ne).choose_spec.choose_spec.choose_spec

/-- The prefix walk. -/
noncomputable def pairPrefix {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexGraph.Walk paperStart v :=
  γ.1.walk.takeUntil v (pair_walk_v_in_support γ hv_ne)

/-- The original walk is prefix ++ suffix. -/
lemma pairDecomp {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    γ.1.walk = (pairPrefix hv_ne γ).append
      (.cons (hexNeighbors3_adj v (pairExitIdx hv_ne γ)) (pairInner hv_ne γ)) := by
  unfold pairPrefix
  rw [← pairSuffix_spec hv_ne γ]
  exact (SimpleGraph.Walk.take_spec γ.1.walk (pair_walk_v_in_support γ hv_ne)).symm

/-- Construct the paired walk. -/
noncomputable def pairInvolWalk {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexGraph.Walk paperStart (hexNeighbors3 v (pairExitIdx hv_ne γ)) :=
  mkPairedWalk v k (pairExitIdx hv_ne γ) (pairPrefix hv_ne γ) (pairInner hv_ne γ)

/-- The paired walk is a trail. -/
lemma pairInvolWalk_is_trail {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvolWalk hv_ne γ).IsTrail := by
  apply mkPairedWalk_is_trail
  · rw [← pairDecomp hv_ne γ]; exact γ.1.is_trail
  · rw [← pairDecomp hv_ne γ]; exact γ.1.fresh
  · exact hv_ne

/-- The paired walk has the right fresh edge. -/
lemma pairInvolWalk_fresh {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    s(hexNeighbors3 v (pairExitIdx hv_ne γ), v) ∉ (pairInvolWalk hv_ne γ).edges := by
  apply mkPairedWalk_fresh
  · rw [← pairDecomp hv_ne γ]; exact γ.1.fresh
  · rw [← pairDecomp hv_ne γ]; exact γ.1.is_trail

/-- The paired walk stays in strip. -/
lemma pairInvolWalk_in_strip {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ∀ u ∈ (pairInvolWalk hv_ne γ).support, PaperFinStrip T L u := by
  apply mkPairedWalk_in_strip
  rw [← pairDecomp hv_ne γ]; exact γ.1.in_strip

/-- The paired walk has 2 v-edges. -/
lemma pairInvolWalk_two_v {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    vEdgeCount v (pairInvolWalk hv_ne γ) = 2 := by
  apply mkPairedWalk_two_v_edges
  rw [← pairDecomp hv_ne γ]; exact γ.2

/-- The FreshIncomingPair at exit_idx. -/
noncomputable def pairInvol {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    FreshIncomingPair T L v (pairExitIdx hv_ne γ) :=
  ⟨⟨pairInvolWalk hv_ne γ,
    pairInvolWalk_is_trail hv_ne γ,
    (hexNeighbors3_adj v (pairExitIdx hv_ne γ)).symm,
    pairInvolWalk_fresh hv_ne γ,
    pairInvolWalk_in_strip hv_ne γ⟩,
   pairInvolWalk_two_v hv_ne γ⟩

/-- The paired walk has the same length. -/
lemma pairInvol_length {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvol hv hv_ne γ).1.len = γ.1.len := by
  simp only [pairInvol, FreshTrail.len, pairInvolWalk]
  rw [mkPairedWalk_length]
  have := pairDecomp hv_ne γ
  have h_len := congr_arg SimpleGraph.Walk.length this
  simp [SimpleGraph.Walk.length_append] at h_len
  omega

/-! ## Pair winding relation

**The key geometric fact**: For a FreshIncomingPair γ at k, the walk
decomposes as prefix + loop. The loop-reversed paired walk has winding
that satisfies the pair algebraic identity.

This encapsulates the turning number theorem for simple closed curves
on the hexagonal lattice: a simple closed trail has total exterior
angle ±2π.

**Sorry**: This requires formalizing the discrete turning number theorem
for simple closed curves on the hex lattice. The key steps would be:
1. A simple closed trail on the hex lattice encloses a region
2. The signed area of the region determines the winding number (±1)
3. Each turn is ±π/3, so the total exterior angle is ±2π
4. Combined with the specific geometry at v, this determines the
   suffix winding to be ±4π/3 -/

/-- The winding relation for pairs (corrected: allows both orderings).
    **Sorry**: requires the discrete turning number theorem for
    simple closed trails on the hexagonal lattice.

    The disjunction covers both loop orientations (clockwise/counterclockwise).
    In each case, the algebraic pair cancellation identity applies. -/
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
      (pairInvol hv hv_ne γ).1.len = γ.1.len := by
  sorry

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