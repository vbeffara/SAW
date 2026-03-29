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
      exact?;
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
    simp +decide [ Finset.sum_image' ];
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
      exact?;
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

/-- For finitely many widths, the sum of bridge partition values
    is bounded by Z(x).
    Uses the disjoint injection: bridges of different widths give
    different SAWs (they end at different x-coordinates). -/
lemma bridge_sum_le_Z (N : ℕ) {x : ℝ} (hx : 0 < x)
    (hsum : Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    ∑ T ∈ Finset.range N, origin_bridge_partition (T + 1) x ≤
    ∑' n, (saw_count n : ℝ) * x ^ n := by
  sorry

end