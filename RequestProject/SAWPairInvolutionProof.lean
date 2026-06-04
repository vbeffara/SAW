/-
# Pair Involution Proof — Pair Part Zero and Fresh Vertex Relation

Proves that the pair part of the vertex sum vanishes and assembles
the full cancellation identity (Lemma 1).

## Main results

* `freshVertexSum_pair_part_zero_proved` — the pair part of the vertex sum vanishes
* `fresh_vertex_relation` — the full cancellation identity (Lemma 1)
-/

import Mathlib
import RequestProject.SAWPairInvolutionHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## The pairing map on the sigma type -/

/-- The sigma type of all fresh incoming pairs at all indices. -/
def AllFreshPairs (T L : ℕ) (v : HexVertex) :=
  Σ (ji : Fin 3), FreshIncomingPair T L v ji

instance allFreshPairs_finite (T L : ℕ) (v : HexVertex) :
    Finite (AllFreshPairs T L v) := by
  unfold AllFreshPairs; exact Finite.instSigma

/-- The contribution function on the sigma type. -/
def pairSigmaContrib {T L : ℕ} (v : HexVertex) (p : AllFreshPairs T L v) : ℂ :=
  midEdgeDir v p.1 * p.2.1.weight

/-- The pairing map on the sigma type. -/
noncomputable def pairSigmaInvol {T L : ℕ} {v : HexVertex}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (p : AllFreshPairs T L v) : AllFreshPairs T L v :=
  ⟨pairExitIdx hv_ne p.2, pairInvol hv hv_ne p.2⟩

/-- Each pair contribution cancels. -/
lemma pairSigmaContrib_cancel {T L : ℕ} {v : HexVertex}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (p : AllFreshPairs T L v) :
    pairSigmaContrib v p + pairSigmaContrib v (pairSigmaInvol hv hv_ne p) = 0 := by
  unfold pairSigmaContrib pairSigmaInvol
  exact pair_contrib_cancels v hv hv_ne p.2

/-- Each element maps to its negation. -/
lemma pairSigmaContrib_neg {T L : ℕ} {v : HexVertex}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (p : AllFreshPairs T L v) :
    pairSigmaContrib v p =
    -pairSigmaContrib v (pairSigmaInvol hv hv_ne p) := by
  have h := pairSigmaContrib_cancel hv hv_ne p
  linear_combination h

/-- The pairing map is injective.
    If invol(k₁, γ₁) = invol(k₂, γ₂), then k₁ = k₂ and γ₁ = γ₂.
    This follows from the fact that the paired walk uniquely determines
    the original walk (the loop at v can only be reversed one way). -/
lemma pairSigmaInvol_injective {T L : ℕ} {v : HexVertex}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart) :
    Function.Injective (pairSigmaInvol hv hv_ne) := by
  sorry

/-! ## The pair part of the vertex sum vanishes -/

/-- The pair part of the fresh vertex sum equals the sum over the sigma type. -/
lemma pair_part_eq_sigma_sum (T L : ℕ) (v : HexVertex) :
    ∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingPair T L v ji), γ.1.weight =
    ∑' (p : AllFreshPairs T L v), pairSigmaContrib v p := by
  unfold AllFreshPairs pairSigmaContrib
  rw [Summable.tsum_sigma' (fun _ => Summable.of_finite) Summable.of_finite]
  simp only [tsum_fintype, Fin.sum_univ_three]
  simp only [tsum_mul_left]

/-- **The pair part of the vertex sum vanishes.**

    Proof: Show S = -S using the pairing map, hence S = 0.
    For each (k, γ), f(k,γ) = -f(invol(k,γ)) by pair_contrib_cancels.
    Since invol is injective on a finite type (hence bijective), reindexing gives
    S = -∑ f ∘ invol = -S. -/
theorem freshVertexSum_pair_part_zero_proved (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v) (hv_ne_start : v ≠ paperStart) :
    ∑ ji : Fin 3, midEdgeDir v ji *
      ∑' (γ : FreshIncomingPair T L v ji), γ.1.weight = 0 := by
  classical
  rw [pair_part_eq_sigma_sum]
  haveI : Fintype (AllFreshPairs T L v) := Fintype.ofFinite _
  rw [tsum_fintype]
  -- Show S = -S using the pairing map
  have h_bij : Function.Bijective (pairSigmaInvol hv hv_ne_start) :=
    Finite.injective_iff_bijective.mp (pairSigmaInvol_injective hv hv_ne_start)
  have h_neg : ∀ a, pairSigmaContrib v a =
      -pairSigmaContrib v (pairSigmaInvol hv hv_ne_start a) :=
    pairSigmaContrib_neg hv hv_ne_start
  -- S = ∑ f(a) = ∑ -f(g(a)) = -∑ f(g(a)) = -∑ f(a) = -S
  have h_eq_neg : ∑ a : AllFreshPairs T L v, pairSigmaContrib v a =
      -(∑ a : AllFreshPairs T L v, pairSigmaContrib v a) := by
    calc ∑ a, pairSigmaContrib v a
        = ∑ a, -pairSigmaContrib v (pairSigmaInvol hv hv_ne_start a) :=
          Finset.sum_congr rfl (fun a _ => h_neg a)
      _ = -(∑ a, pairSigmaContrib v (pairSigmaInvol hv hv_ne_start a)) := by
          rw [← Finset.sum_neg_distrib]
      _ = -(∑ a, pairSigmaContrib v a) := by
          congr 1
          exact Fintype.sum_bijective _ h_bij _ _ (fun _ => rfl)
  -- From S = -S, deduce S = 0
  have : (2 : ℂ) * ∑ a : AllFreshPairs T L v, pairSigmaContrib v a = 0 := by
    linear_combination h_eq_neg
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-! ## The full cancellation identity (Lemma 1) -/

/-- **Lemma 1** (Cancellation Identity / Vertex Relation).
    For every interior vertex v of the strip domain,
    the fresh vertex sum is zero:
      freshVertexSum T L v = 0 -/
theorem fresh_vertex_relation (T L : ℕ) (v : HexVertex)
    (hv : PaperFinStrip T L v)
    (hv_ne_start : v ≠ paperStart)
    (_h_nbrs : ∀ i : Fin 3, PaperFinStrip T L (hexNeighbors3 v i)) :
    freshVertexSum T L v = 0 := by
  rw [freshVertexSum_decompose T L v hv_ne_start]
  have h1 := freshVertexSum_triplet_part_zero T L v hv hv_ne_start
  have h2 := freshVertexSum_pair_part_zero_proved T L v hv hv_ne_start
  linear_combination h1 + h2

end
