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

/-
The inner reverse support starts with hexNeighbors3 v k.
-/
lemma inner_rev_support_head {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInner hv_ne γ).reverse.support.head? = some (hexNeighbors3 v k) := by
  have h_support : ∀ {u w : HexVertex} {p : hexGraph.Walk u w}, p.support.reverse.head? = some w := by
    intros u w p; induction p <;> aesop;
  convert h_support using 1;
  rw [ SimpleGraph.Walk.support_reverse ]

/-
The paired walk support has a specific structure.
-/
lemma pairInvolWalk_support_structure {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    (pairInvolWalk hv_ne γ).support =
    (pairPrefix hv_ne γ).support ++ (pairInner hv_ne γ).reverse.support := by
  convert mkPairedWalk_support' v k ( pairExitIdx hv_ne γ ) ( pairPrefix hv_ne γ ) ( pairInner hv_ne γ ) using 1

/-
Equal paired walk supports imply equal k indices.
-/
lemma paired_walk_determines_k {T L : ℕ} {v : HexVertex} {k₁ k₂ : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ₁ : FreshIncomingPair T L v k₁) (γ₂ : FreshIncomingPair T L v k₂)
    (h_support : (pairInvolWalk hv_ne γ₁).support = (pairInvolWalk hv_ne γ₂).support) :
    k₁ = k₂ := by
  apply hexNeighbors3_injective v;
  rw [ pairInvolWalk_support_structure, pairInvolWalk_support_structure ] at h_support;
  have h_eq : (pairPrefix hv_ne γ₁).support = (pairPrefix hv_ne γ₂).support ∧ (pairInner hv_ne γ₁).reverse.support = (pairInner hv_ne γ₂).reverse.support := by
    apply list_append_cancel_at_unique' v h_support (prefix_support_ne_nil hv_ne γ₁) (prefix_support_ne_nil hv_ne γ₂) (prefix_support_getLast hv_ne γ₁) (prefix_support_getLast hv_ne γ₂) (v_not_in_inner_rev_support hv_ne γ₁) (v_not_in_inner_rev_support hv_ne γ₂);
    convert v_count_one_in_pairInvolWalk hv_ne γ₁ using 1;
    rw [ pairInvolWalk_support_structure ];
    convert rfl;
  have := inner_rev_support_head hv_ne γ₁; have := inner_rev_support_head hv_ne γ₂; aesop;

/-
Equal paired walk supports (at same k) imply equal originals.
-/
lemma paired_walk_determines_original {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart)
    (γ₁ γ₂ : FreshIncomingPair T L v k)
    (h_exit : pairExitIdx hv_ne γ₁ = pairExitIdx hv_ne γ₂)
    (h_support : (pairInvolWalk hv_ne γ₁).support = (pairInvolWalk hv_ne γ₂).support) :
    γ₁ = γ₂ := by
  -- Apply the lemma that states if the supports are equal, then the prefixes and suffixes are equal.
  have h_prefix_suffix : (pairPrefix hv_ne γ₁).support = (pairPrefix hv_ne γ₂).support ∧ (pairInner hv_ne γ₁).reverse.support = (pairInner hv_ne γ₂).reverse.support := by
    apply list_append_cancel_at_unique' v;
    any_goals exact prefix_support_ne_nil hv_ne _;
    any_goals exact v_not_in_inner_rev_support hv_ne _;
    · rw [ ← pairInvolWalk_support_structure hv_ne γ₁, ← pairInvolWalk_support_structure hv_ne γ₂, h_support ];
    · exact prefix_support_getLast hv_ne γ₁;
    · exact?;
    · convert v_count_one_in_pairInvolWalk hv_ne γ₁ using 1;
      rw [ pairInvolWalk_support_structure ];
      convert rfl;
  apply Subtype.ext; exact (by
  apply Eq.symm; exact (by
    have := pairDecomp hv_ne γ₂
    have := pairDecomp hv_ne γ₁; simp_all +decide [ pairInvolWalk ] ;
    apply Eq.symm; exact (by
      have h_walk_eq : (γ₁.1.walk) = (γ₂.1.walk) := by
        apply SimpleGraph.Walk.ext_support;
        simp_all +decide [ SimpleGraph.Walk.support_append ]
      cases h : γ₁.1 ; cases h' : γ₂.1 ; aesop ( simp_config := { singlePass := true } ) ;
    )
  ));

/-
The pairing map is injective.
-/
lemma pairSigmaInvol_injective {T L : ℕ} {v : HexVertex}
    (hv : PaperFinStrip T L v) (hv_ne : v ≠ paperStart) :
    Function.Injective (pairSigmaInvol hv hv_ne) := by
  intro p q hpq;
  -- Extract the exit indices from the equality of the pairedb walks.
  have h_exit : p.1 = q.1 := by
    apply paired_walk_determines_k hv_ne p.2 q.2;
    convert congr_arg ( fun x : AllFreshPairs T L v => ( x.2.1.walk.support ) ) hpq using 1;
  cases p ; cases q ; simp_all +decide [ pairSigmaInvol ];
  rename_i k₁ γ₁ k₂ γ₂;
  subst h_exit;
  have := paired_walk_determines_original hv hv_ne γ₁ γ₂ ( by injection hpq ) ( by
    have := congr_arg ( fun x : AllFreshPairs T L v => x.2.1.walk.support ) hpq; aesop; ) ; aesop;

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