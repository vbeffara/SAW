/-
# Z(xc) Divergence from Bridge Lower Bound
-/

import RequestProject.SAWFiniteStrip

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Bridge-to-SAW conversion -/

/-- Rewrite a path's start vertex. -/
def pathCastStart {v₁ v₂ w : HexVertex} (h : v₁ = v₂) (p : hexGraph.Path v₁ w) :
    hexGraph.Path v₂ w := h ▸ p

@[simp] lemma pathCastStart_length {v₁ v₂ w : HexVertex} (h : v₁ = v₂)
    (p : hexGraph.Path v₁ w) :
    (pathCastStart h p).1.length = p.1.length := by subst h; rfl

/-- Convert an origin bridge to a SAW from hexOrigin. -/
def bridgeToSAW (T : ℕ) (b : OriginBridge T) :
    SAW hexOrigin b.1.walk.1.length :=
  ⟨b.1.end_v, pathCastStart b.2 b.1.walk, pathCastStart_length b.2 b.1.walk⟩

/-
PROBLEM
bridgeToSAW is injective.

PROVIDED SOLUTION
If bridgeToSAW T b₁ = bridgeToSAW T b₂ at the sigma level, then their lengths match and their SAWs match.

The SAW has fields w (endpoint) and p (path). If the SAWs match, then b₁.1.end_v = b₂.1.end_v and pathCastStart b₁.2 b₁.1.walk = pathCastStart b₂.2 b₂.1.walk.

Since pathCastStart just does a subst, if b₁.2 and b₂.2 are both proofs that the start is hexOrigin, then pathCastStart h p = p (after subst). So the walks are equal.

Two bridges with the same endpoint and same walk are equal (since Bridge is a structure). And two subtypes with the same val are equal.

Use Sigma.mk.inj_iff and SAW extensionality.
-/
lemma bridgeToSAW_injective (T : ℕ) :
    Function.Injective (fun b : OriginBridge T =>
      (⟨b.1.walk.1.length, bridgeToSAW T b⟩ : (n : ℕ) × SAW hexOrigin n)) := by
  intro b₁ b₂ h_eq;
  rcases b₁ with ⟨ ⟨ v₁, w₁, p₁, h₁, h₂, h₃ ⟩, hb₁ ⟩ ; rcases b₂ with ⟨ ⟨ v₂, w₂, p₂, h₄, h₅, h₆ ⟩, hb₂ ⟩ ; simp_all +decide [ Sigma.ext_iff ] ;
  grind +locals

/-
PROBLEM
For a finite set of origin bridges, the number with length n is at most saw_count n.

PROVIDED SOLUTION
Define an injection from the filtered finset to SAW hexOrigin n.

For b in F.filter(length = n), construct SAW hexOrigin n:
- w := b.1.end_v
- p := pathCastStart b.2 b.1.walk
- l : (pathCastStart b.2 b.1.walk).1.length = n, which follows from pathCastStart_length and the filter condition.

This map is injective: if two bridges map to the same SAW, their endpoints and paths match, so the bridges are equal.

Use Finset.card_le_card_of_injOn mapping to Finset.univ (of SAW hexOrigin n), or use Fintype.card_le_of_injective after converting the finset card to a type card.
-/
lemma bridge_filter_card_le (T : ℕ) (F : Finset (OriginBridge T)) (n : ℕ) :
    (F.filter (fun b => b.1.walk.1.length = n)).card ≤ saw_count n := by
  -- Let's denote the set of origin bridges in $F$ of length $n$ by $F_n$.
  set F_n := F.filter (fun b => b.1.walk.1.length = n) with hF_n_def;
  -- Define an injection from the set of origin bridges of length $n$ to the set of SAWs of length $n$.
  have h_inj : Function.Injective (fun b : F_n => ⟨b.val.1.walk.1.length, bridgeToSAW T b.val⟩ : F_n → (n : ℕ) × SAW hexOrigin n) := by
    intro b₁ b₂ h_eq; simp_all
    have := bridgeToSAW_injective T; aesop;
  have h_card_le : F_n.card ≤ Finset.card (Finset.image (fun b : F_n => ⟨b.val.1.walk.1.length, bridgeToSAW T b.val⟩ : F_n → (n : ℕ) × SAW hexOrigin n) Finset.univ) := by
    rw [ Finset.card_image_of_injective _ h_inj ] ; aesop;
  refine le_trans h_card_le ?_;
  refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
  exact Finset.image ( fun s : SAW hexOrigin n => ⟨ n, s ⟩ ) Finset.univ;
  · grind;
  · rw [ Finset.card_image_of_injective _ fun x y hxy => by injection hxy ] ; aesop

/-- Finite partial sum of bridge weights ≤ Z(x). -/
lemma origin_bridge_finite_sum_le_Z (T : ℕ) {x : ℝ} (hx : 0 < x)
    (hZ : Summable (fun n => (saw_count n : ℝ) * x ^ n))
    (F : Finset (OriginBridge T)) :
    ∑ b ∈ F, x ^ b.1.walk.1.length ≤ ∑' n, (saw_count n : ℝ) * x ^ n := by
  have h_group : ∑ b ∈ F, x ^ (b.1.walk.1.length) = ∑ n ∈ F.image (fun b => b.1.walk.1.length), (∑ b ∈ F.filter (fun b => b.1.walk.1.length = n), x ^ n) := by
    rw [ Finset.sum_image' ]
    exact fun i hi => Finset.sum_congr rfl fun j hj => by aesop
  have h_bound : ∀ n ∈ F.image (fun b => b.1.walk.1.length), (∑ b ∈ F.filter (fun b => b.1.walk.1.length = n), x ^ n) ≤ (saw_count n : ℝ) * x ^ n := by
    simp +zetaDelta at *
    exact fun b hb => mul_le_mul_of_nonneg_right ( mod_cast bridge_filter_card_le T F _ ) ( by positivity )
  exact h_group.symm ▸ le_trans ( Finset.sum_le_sum h_bound ) ( Summable.sum_le_tsum _ ( fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) hZ )

/-- B_T^x ≤ Z(x) for summable Z. -/
lemma origin_bridge_partition_le_Z (T : ℕ) {x : ℝ} (hx : 0 < x)
    (hZ : Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    origin_bridge_partition T x ≤ ∑' n, (saw_count n : ℝ) * x ^ n :=
  Real.tsum_le_of_sum_le (fun _ => pow_nonneg hx.le _)
    (fun F => origin_bridge_finite_sum_le_Z T hx hZ F)

/-
PROBLEM
Z(xc) diverges from origin_bridge_lower_bound.

PROVIDED SOLUTION
By contradiction. Assume h_summable : Summable (fun n => c_n * xc^n).

From origin_bridge_lower_bound, get c > 0 with c/T ≤ B_T for all T ≥ 1, hence c/(T+1) ≤ B_{T+1} for all T.

The harmonic series ∑ c/(T+1) diverges (by not_summable_of_lower_bound).

So it suffices to show ∑ B_{T+1} is summable (for contradiction via comparison).

By origin_bridge_partition_le_Z, for each T, B_{T+1} ≤ Z(xc) = ∑' n, c_n * xc^n.

But B_{T+1} ≤ constant doesn't give summability. We need the DISJOINT injection.

Actually, let me use a different argument. For each N, the partial sum:
∑_{T=0}^{N-1} B_{T+1} ≤ Z(xc)

This is because bridges of widths 1, ..., N are DISJOINT SAWs (a bridge of width T ends at x=T, different widths → different endpoints → different SAWs). So the total weight of bridges of widths 1,...,N is at most Z(xc).

More precisely: for each N, the finite sum ∑_{T=0}^{N-1} ∑_{b:OriginBridge(T+1)} xc^{b.length} can be bounded by Z(xc) because the bridges form a subset of all SAWs from hexOrigin (with different widths giving disjoint SAWs).

Then by summable_of_sum_range_le (with the bound Z(xc) for all N), the series is summable.

Use summable_of_sum_range_le with the bound ∑' n, c_n * xc^n. Need to show:
∀ N, ∑ T in range N, B_{T+1} ≤ ∑' n, c_n * xc^n

For each N, ∑ T in range N, B_{T+1} = ∑ T in range N, ∑'(b:OriginBridge(T+1)), xc^{b.length}

If each B_{T+1} is the tsum, and these tsums sum to at most Z(xc), then we're done.

But showing the partial sum of tsums is bounded requires the disjoint injection.

Alternatively: for each N, we can bound the finite sum by showing that the map from ⊔_{T=1}^N OriginBridge(T) → (Σ n, SAW hexOrigin n) is injective. Two bridges of different widths end at different x-coordinates, hence give different SAWs.

For each T in the range and each finite partial sum over bridges, we have ∑_{b in F_T} xc^{b.length} ≤ Z(xc) (by origin_bridge_finite_sum_le_Z). But we need the SUM over T.

This is getting complex. Let me try a simpler approach: use the fact that for each T, B_{T+1} ≤ Z(xc), and then use summable_of_sum_range_le with the bound (N+1) * Z(xc), which grows linearly. But that doesn't give summability.

Actually, the RIGHT approach is:
∀ N, ∑_{T=0}^{N-1} B_{T+1} ≤ Z(xc)

This follows from: for each finite collection of bridges from different widths, they inject into SAWs. So for each N, pick all bridges from widths 1,...,N. Their total weight ≤ Z(xc). Taking the sup over all finite subsets gives ∑ B_{T+1} ≤ Z(xc).

But we need to formalize this disjoint injection. Let me try with summable_of_sum_range_le and the bound Z(xc). For each N:

∑_{T=0}^{N-1} B_{T+1} ≤ Z(xc)?

This requires: the sum of the bridge partitions for widths 1,...,N is at most Z(xc).

We can prove: for any finite subset F of the disjoint union ⊔_{T=1}^N OriginBridge(T), the sum ∑_{b∈F} xc^{b.length} ≤ Z(xc).

This follows from origin_bridge_finite_sum_le_Z applied to each width separately, and the disjointness.

Actually, we can combine:
∑_{T=0}^{N-1} B_{T+1} = ∑_{T=0}^{N-1} tsum_{b:OriginBridge(T+1)} xc^{b.length}

For each T, B_{T+1} ≤ Z(xc) by origin_bridge_partition_le_Z. So ∑ B_{T+1} ≤ N * Z(xc). But N * Z(xc) grows, so this doesn't give summability.

The key insight that makes this work is that bridges of DIFFERENT widths are DISJOINT contributions to Z(xc). The total contribution of ALL bridges (of all widths) to Z(xc) is at most Z(xc). So ∑_T B_T ≤ Z(xc).

To formalize this, I think I need a lemma saying that the map ⊔_T OriginBridge(T) → Σ_n SAW(n) is injective, and then use a comparison argument for tsums of tsums.
-/
theorem Z_xc_diverges_from_lower_bound :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := origin_bridge_lower_bound
  intro h_summable
  have h_lower : ∀ T : ℕ, c / ((T : ℝ) + 1) ≤
      origin_bridge_partition (T + 1) xc := by
    intro T; have := hc_bound (T + 1) (by omega); push_cast at this ⊢; linarith
  -- Need: Summable (fun T => B_{T+1})
  -- Follows from disjoint bridge injection: bridges of different widths
  -- are different SAWs, so ∑_T B_T ≤ Z(xc).
  have h_bridge_summable : Summable (fun T : ℕ =>
      origin_bridge_partition (T + 1) xc) := by sorry
  exact absurd
    (Summable.of_nonneg_of_le (fun T => by positivity) h_lower h_bridge_summable)
    (not_summable_of_lower_bound hc_pos (fun n => le_refl _))

end
