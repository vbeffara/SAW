/-
# Hammersley-Welsh Bridge Decomposition: Key Helper Lemmas

Helper lemmas for the bridge decomposition injection, connecting
bridge partition functions to SAW counting functions.

## Reference

Section 3 of: Hugo Duminil-Copin and Stanislav Smirnov,
"The connective constant of the honeycomb lattice equals √(2+√2)",
Annals of Mathematics, 175(3), 1653--1665, 2012.
-/

import Mathlib
import RequestProject.SAWHWInject

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- Superseded by Z_xc_diverges_corrected in SAWPaperChain.lean. -/
private theorem Z_xc_diverges :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  sorry

/-! ## Bridge-to-SAW injection

Each origin bridge of width T determines a unique SAW from hexOrigin
of the same length. -/

/-- An origin bridge of width T gives a SAW from hexOrigin. -/
def bridgeToSAW {T : ℕ} (b : OriginBridge T) :
    SAW hexOrigin b.1.walk.1.length :=
  match b with
  | ⟨⟨_, ev, walk, _, _, _⟩, rfl⟩ => ⟨ev, walk, rfl⟩

/-
PROBLEM
The bridge-to-SAW map is injective.

PROVIDED SOLUTION
Two origin bridges b₁, b₂ map to the same sigma type element if they have the same walk length and the same SAW. The SAW determines the walk (path) and endpoint. Since b₁.1.start_v = b₂.1.start_v = hexOrigin and the walks are the same, the bridges are equal. Use Subtype.ext and Bridge structure ext.
-/
lemma bridgeToSAW_injective (T : ℕ) :
    Function.Injective (fun b : OriginBridge T =>
      (⟨b.1.walk.1.length, bridgeToSAW b⟩ : Σ n, SAW hexOrigin n)) := by
  intro b₁ b₂ h_eq;
  unfold bridgeToSAW at h_eq;
  grind

/-
PROBLEM
For any finite set F of origin bridges, the number with length exactly n
    is at most saw_count n.

PROVIDED SOLUTION
The bridges in F with length n inject into SAW hexOrigin n (via bridgeToSAW). Since SAW hexOrigin n is a Fintype with card = saw_count n, the filter has at most saw_count n elements. Use Finset.card_le_card_of_injOn or similar.
-/
lemma bridge_filter_card_le (T n : ℕ) (F : Finset (OriginBridge T)) :
    (F.filter (fun b => b.1.walk.1.length = n)).card ≤ saw_count n := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.filter ( fun b => ( b.1.walk.1.length : ℕ ) = n ) F;
  · aesop_cat;
  · have h_inj : Function.Injective (fun b : OriginBridge T => (⟨b.1.walk.1.length, bridgeToSAW b⟩ : Σ n, SAW hexOrigin n)) := by
      exact bridgeToSAW_injective T;
    have h_card_le : Finset.card (Finset.image (fun b : OriginBridge T => (⟨b.1.walk.1.length, bridgeToSAW b⟩ : Σ n, SAW hexOrigin n)) (Finset.filter (fun b : OriginBridge T => (b.1.walk.1.length : ℕ) = n) F)) ≤ Fintype.card (SAW hexOrigin n) := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun s : SAW hexOrigin n => ⟨ n, s ⟩ ) Finset.univ;
      · intro; aesop;
      · exact Finset.card_image_le.trans ( by simp +decide );
    rwa [ Finset.card_image_of_injective _ h_inj ] at h_card_le

/-! ## Weight bounds -/

/-
PROBLEM
x_c < 1

PROVIDED SOLUTION
xc = 1/√(2+√2). We need 1/√(2+√2) < 1, i.e., 1 < √(2+√2), i.e., 1 < 2+√2 (squaring both sides since both are positive, and √2 > 0 so 2+√2 > 2 > 1). So √(2+√2) > 1, hence 1/√(2+√2) < 1.
-/
lemma xc_lt_one : xc < 1 := by
  rw [ show xc = 1 / Real.sqrt ( 2 + Real.sqrt 2 ) by rfl ] ; exact by rw [ div_lt_one ( Real.sqrt_pos.mpr <| by positivity ) ] ; exact Real.lt_sqrt_of_sq_lt <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;

/-! ## Finite partial sums -/

/-
PROBLEM
For a finite set of origin bridges, their total weight
    is bounded by a sum of c_n * x^n values.

PROVIDED SOLUTION
Group bridges by length. For each length n, there are at most saw_count n bridges (by bridge_filter_card_le). So:
∑_{b∈F} x^{b.length} = ∑_n (∑_{b∈F, b.length=n} x^n) = ∑_n |{b∈F : b.length=n}| * x^n ≤ ∑_n c_n * x^n.
The sum over n goes up to the max length in F, which is ≤ F.sup(length).

Use Finset.sum_comp or partition F by length values, using bridge_filter_card_le for each fiber.
-/
lemma origin_bridge_finite_sum_le_saw (T : ℕ) {x : ℝ} (hx : 0 < x)
    (F : Finset (OriginBridge T)) :
    ∑ b ∈ F, x ^ b.1.walk.1.length ≤
    ∑ n ∈ Finset.range (F.sup (fun b => b.1.walk.1.length) + 1),
      (saw_count n : ℝ) * x ^ n := by
  have h_sum : ∑ b ∈ F, x ^ (b.1.walk.1.length : ℕ) = ∑ n ∈ Finset.image (fun b => b.1.walk.1.length) F, (∑ b ∈ F.filter (fun b => b.1.walk.1.length = n), x ^ n) := by
    simp
    rw [ Finset.sum_image' ];
    exact fun i hi => by rw [ Finset.sum_congr rfl fun j hj => by rw [ Finset.mem_filter.mp hj |>.2 ] ] ; simp +decide [ mul_comm ] ;
  have h_card : ∀ n ∈ Finset.image (fun b => b.1.walk.1.length) F, (∑ b ∈ F.filter (fun b => b.1.walk.1.length = n), x ^ n) ≤ (saw_count n : ℝ) * x ^ n := by
    intros n hn
    have h_card : (F.filter (fun b => b.1.walk.1.length = n)).card ≤ saw_count n := by
      convert bridge_filter_card_le T n _ using 1;
    simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr h_card ) ( pow_nonneg hx.le n );
  exact h_sum.symm ▸ le_trans ( Finset.sum_le_sum h_card ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.image_subset_iff.mpr fun b hb => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Finset.le_sup ( f := fun b : OriginBridge T => ( b.1.walk.1.length : ℕ ) ) hb ) ) ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) )

/-
PROBLEM
B_T^x ≤ Z(x) when Z(x) converges.

PROVIDED SOLUTION
origin_bridge_partition T x = ∑' b, x^{b.length}. If not summable, this is 0 ≤ Z(x) since Z(x) ≥ 0 (all terms nonneg). If summable, use origin_bridge_finite_sum_le_saw for each finite partial sum: for any F, ∑_{b∈F} x^b.length ≤ ∑_n c_n x^n (finite sum) ≤ Z(x) = ∑' c_n x^n. Then by tsum_le_of_sum_le or Real.tsum_le_of_sum_le, the tsum over origin bridges ≤ Z(x).
-/
lemma origin_bridge_partition_le_Z (T : ℕ) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    origin_bridge_partition T x ≤ ∑' n, (saw_count n : ℝ) * x ^ n := by
  have h_finite_sum : ∀ F : Finset (OriginBridge T), ∑ b ∈ F, x ^ (b.1.walk.1.length) ≤ ∑' n : ℕ, (saw_count n : ℝ) * x ^ n := by
    intro F
    have h_sum_le : ∑ b ∈ F, x ^ b.1.walk.1.length ≤ ∑ n ∈ Finset.range (F.sup (fun b => b.1.walk.1.length) + 1), (saw_count n : ℝ) * x ^ n := by
      exact origin_bridge_finite_sum_le_saw T hx F;
    exact h_sum_le.trans ( Summable.sum_le_tsum ( Finset.range _ ) ( fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx.le _ ) ) hsum );
  convert tsum_le_of_sum_le _ _;
  · exact fun _ => pow_nonneg hx.le _;
  · convert h_finite_sum using 1

/-! ## Disjoint bridge injection -/

/-- Bridges of different widths give different SAW endpoints. -/
lemma disjoint_bridge_widths {T₁ T₂ : ℕ} (hT : T₁ ≠ T₂)
    (b₁ : OriginBridge T₁) (b₂ : OriginBridge T₂) :
    b₁.1.end_v ≠ b₂.1.end_v := by
  intro h
  have h1 := b₁.1.end_right
  have h2 := b₂.1.end_right
  rw [h] at h1; omega

/-
PROBLEM
Bridges of different widths, when mapped to SAWs, give different
    sigma-type elements. This combined with bridgeToSAW_injective gives
    the full disjoint injection.

PROVIDED SOLUTION
Intro (T₁, b₁) (T₂, b₂) and assume their SAW images are equal as sigma types. The SAW image of (T, b) has endpoint b.1.end_v. Since b₁.1.end_right : b₁.1.end_v.1 = T₁ and b₂.1.end_right : b₂.1.end_v.1 = T₂, and the SAW endpoints must match, we get T₁ = T₂. Then subst and use bridgeToSAW_injective T₁ to conclude b₁ = b₂.
-/
lemma bridge_sigma_injective :
    Function.Injective (fun (p : (T : ℕ) × OriginBridge T) =>
      (⟨p.2.1.walk.1.length, bridgeToSAW p.2⟩ : (n : ℕ) × SAW hexOrigin n)) := by
  intro p q h_eq; simp_all
  have h_eq' : p.1 = q.1 := by
    have h_eq' : p.snd.1.end_v.1 = p.1 ∧ q.snd.1.end_v.1 = q.1 := by
      exact ⟨ p.2.1.end_right, q.2.1.end_right ⟩
    generalize_proofs at *; (
    have h_eq'' : p.snd.1.end_v = q.snd.1.end_v := by
      have h_eq'' : (bridgeToSAW p.snd).w = (bridgeToSAW q.snd).w := by
        have := h_eq.right
        grind
      generalize_proofs at *; (
      convert h_eq'' using 1 <;> unfold bridgeToSAW <;> aesop ( simp_config := { singlePass := true } ) ;)
    generalize_proofs at *; (
    grind +ring));
  have := bridgeToSAW_injective p.1 ; aesop

/-
PROBLEM
Combined finite sum of bridge weights across multiple widths
    is bounded by Z(x). Key: bridges of different widths end at
    different x-coordinates, so they give distinct SAWs.

PROVIDED SOLUTION
The LHS is a finite sum over Fin N of finite sums over F T. Combine everything into a single finite sum over the sigma type {(T, b) | T : Fin N, b ∈ F T}. Use bridge_sigma_injective to map each (T, b) to a SAW (b.1.walk.1.length, bridgeToSAW b). This is an injection into Σ n, SAW hexOrigin n. For each n, the number of bridges mapping to SAW hexOrigin n is at most saw_count n (by Finset.card_le_card into Finset.univ). So the total sum ≤ ∑' n, c_n * x^n by grouping by length and using saw_count as the bound, then sum_le_tsum.
-/
lemma combined_bridge_finite_sum_le_Z {x : ℝ} (hx : 0 < x)
    (hZ : Summable (fun n => (saw_count n : ℝ) * x ^ n))
    (N : ℕ) (F : (T : Fin N) → Finset (OriginBridge (T.1 + 1))) :
    ∑ T : Fin N, ∑ b ∈ F T, x ^ b.1.walk.1.length ≤
    ∑' n, (saw_count n : ℝ) * x ^ n := by
  -- By definition of $bridgeToSAW$, we know that the bridges in $F$ are mapped injectively to SAWs.
  have h_inj : Function.Injective (fun (p : (T : Fin N) × OriginBridge (T + 1)) =>
    (⟨p.2.1.walk.1.length, bridgeToSAW p.2⟩ : (n : ℕ) × SAW hexOrigin n)) := by
      convert bridge_sigma_injective using 1;
      constructor <;> intro h <;> intro p₁ p₂ h_eq;
      · have := @bridge_sigma_injective p₁ p₂ ; aesop;
      · injection h_eq with h₁ h₂;
        convert h _;
        rotate_left;
        exact ⟨ p₁.1 + 1, p₁.2 ⟩;
        exact ⟨ p₂.1 + 1, p₂.2 ⟩;
        · aesop;
        · aesop;
  have h_card_le : ∀ n : ℕ, (∑ T : Fin N, ∑ b ∈ F T, (if b.1.walk.1.length = n then 1 else 0)) ≤ saw_count n := by
    intro n
    have h_card_le : (∑ T : Fin N, ∑ b ∈ F T, (if b.1.walk.1.length = n then 1 else 0)) ≤ Finset.card (Finset.image (fun (p : (T : Fin N) × OriginBridge (T + 1)) => (⟨p.2.1.walk.1.length, bridgeToSAW p.2⟩ : (n : ℕ) × SAW hexOrigin n)) (Finset.filter (fun p => p.2.1.walk.1.length = n) (Finset.sigma Finset.univ F))) := by
      rw [ Finset.card_image_of_injective _ h_inj ];
      rw [ Finset.card_filter ];
      rw [ Finset.sum_sigma ];
    refine le_trans h_card_le ?_;
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun s : SAW hexOrigin n => ⟨ n, s ⟩ ) Finset.univ;
    · grind;
    · rw [ Finset.card_image_of_injective _ fun a b h => by injection h ] ; simp +decide [ saw_count ] ;
  have h_sum_le : ∑ T : Fin N, ∑ b ∈ F T, x ^ (b.1.walk.1.length) ≤ ∑' n, (∑ T : Fin N, ∑ b ∈ F T, (if b.1.walk.1.length = n then 1 else 0)) * x ^ n := by
    have h_sum_le : ∑ T : Fin N, ∑ b ∈ F T, x ^ (b.1.walk.1.length) = ∑' n, (∑ T : Fin N, ∑ b ∈ F T, (if b.1.walk.1.length = n then x ^ n else 0)) := by
      rw [ tsum_eq_sum ];
      any_goals exact Finset.biUnion ( Finset.univ : Finset ( Fin N ) ) fun T => Finset.image ( fun b : OriginBridge ( T + 1 ) => ( b.1.walk.1.length : ℕ ) ) ( F T );
      · rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        intro T hT; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
        rw [ Finset.sum_filter_of_ne ] ; aesop;
      · simp +contextual
    simp_all +decide [ Finset.sum_ite, Finset.sum_mul ];
  exact h_sum_le.trans ( Summable.tsum_le_tsum ( fun n => mul_le_mul_of_nonneg_right ( mod_cast h_card_le n ) ( pow_nonneg hx.le _ ) ) ( by exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity ) ( pow_nonneg hx.le _ ) ) ( fun n => mul_le_mul_of_nonneg_right ( mod_cast h_card_le n ) ( pow_nonneg hx.le _ ) ) hZ ) ( by exact hZ ) )

/-
PROBLEM
For finitely many widths, the sum of bridge partition values
    is bounded by Z(x).
    Uses the disjoint injection: bridges of different widths give
    different SAWs (they end at different x-coordinates).

PROVIDED SOLUTION
Each origin_bridge_partition (T+1) x is a tsum. The finite sum ∑ T ∈ range N, B_{T+1} can be bounded by: for any epsilon > 0, choose finite sets F_T such that B_{T+1} - epsilon/N ≤ ∑_{b ∈ F_T} x^{b.length}. Then the total finite sum ≤ combined_bridge_finite_sum_le_Z. Alternatively: use the approach of showing each finite partial sum is bounded by Z(x). Since origin_bridge_partition is a tsum of nonneg terms, and each partial sum (across all widths) is bounded by Z(x) via combined_bridge_finite_sum_le_Z, the sum of the tsums is bounded by Z(x). Use Finset.sum_le_sum with origin_bridge_partition_le_Z for each T individually... wait that gives N*Z(x). Instead, use the combined lemma: convert the sum of tsums into a tsum-like bound using combined_bridge_finite_sum_le_Z applied to all finite partial sums.
-/
lemma bridge_sum_le_Z (N : ℕ) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    ∑ T ∈ Finset.range N, origin_bridge_partition (T + 1) x ≤
    ∑' n, (saw_count n : ℝ) * x ^ n := by
  by_contra h_contra;
  -- Since the origin bridge partitions are non-negative, their sum up to N is bounded by the sum of the infinite series. Use this fact.
  have h_sum_finite : ∀ ε > 0, ∃ F : (T : Fin N) → Finset (OriginBridge (T.1 + 1)), (∑ T : Fin N, ∑ b ∈ F T, x ^ b.1.walk.1.length) > (∑ T ∈ Finset.range N, origin_bridge_partition (T + 1) x) - ε := by
    intro ε hε_pos
    have h_sum_finite : ∀ T : Fin N, ∃ F : Finset (OriginBridge (T.1 + 1)), (∑ b ∈ F, x ^ b.1.walk.1.length) > origin_bridge_partition (T.1 + 1) x - ε / N := by
      intro T
      have h_sum_finite : Filter.Tendsto (fun F : Finset (OriginBridge (T.1 + 1)) => ∑ b ∈ F, x ^ b.1.walk.1.length) (Filter.atTop : Filter (Finset (OriginBridge (T.1 + 1)))) (nhds (origin_bridge_partition (T.1 + 1) x)) := by
        convert Summable.hasSum _ |> fun h => h.comp _;
        any_goals tauto;
        · rfl;
        · convert origin_bridge_summable_le_xc' ( T + 1 ) ( by linarith [ Fin.is_lt T ] ) hx ( show x ≤ xc from ?_ ) using 1;
          by_cases hx_le_xc : x ≤ xc;
          · exact hx_le_xc;
          · have := @Z_xc_diverges;
            exact False.elim <| this <| Summable.of_nonneg_of_le ( fun n => mul_nonneg ( Nat.cast_nonneg _ ) <| pow_nonneg ( by exact div_nonneg zero_le_one <| Real.sqrt_nonneg _ ) _ ) ( fun n => mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact div_nonneg zero_le_one <| Real.sqrt_nonneg _ ) ( le_of_not_ge hx_le_xc ) _ ) <| Nat.cast_nonneg _ ) hsum;
      have := h_sum_finite.eventually ( lt_mem_nhds <| show origin_bridge_partition ( T + 1 ) x - ε / N < origin_bridge_partition ( T + 1 ) x from sub_lt_self _ <| div_pos hε_pos <| Nat.cast_pos.mpr <| pos_of_gt T.2 ) ; have := this.exists; aesop;
    choose F hF using h_sum_finite;
    use F; simp_all +decide [ Finset.sum_range ] ;
    rcases N with ( _ | N ) <;> norm_num at *;
    · linarith;
    · exact lt_of_le_of_lt ( by simp +decide [ Finset.sum_sub_distrib, mul_div_cancel₀ _ ( by positivity : ( N : ℝ ) + 1 ≠ 0 ) ] ) ( Finset.sum_lt_sum_of_nonempty ( Finset.univ_nonempty ) fun i _ => hF i );
  obtain ⟨ F, hF ⟩ := h_sum_finite ( ( ∑ T ∈ Finset.range N, origin_bridge_partition ( T + 1 ) x - ∑' n : ℕ, ( saw_count n : ℝ ) * x ^ n ) / 2 ) ( half_pos ( sub_pos.mpr ( lt_of_not_ge h_contra ) ) ) ; ( have := combined_bridge_finite_sum_le_Z hx hsum N F ; linarith; )

end
