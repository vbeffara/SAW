/-
# Corrected Bridge Chain using Paper (Diagonal) Bridges

## Sorry status

Three sorry's remain on the path to the main theorem:
1. `strip_identity_genuine` (in SAWStripIdentityCorrect.lean) — the genuine
   strip identity (Lemma 2 of the paper). B_paper_le_one_obs is now PROVED
   from this lemma via bridge_bound_of_strip_identity.
2. `paper_bridge_recurrence` (this file) — quadratic recurrence for bridges,
   depends on the infinite-strip identity + cutting argument
3. `paper_bridge_decomp_injection` (this file) — Hammersley-Welsh decomposition,
   independent of #1

## Proved in this session
- `B_paper_le_one_direct` is now proved from `strip_identity_paper`
- `paper_bridge_lower_bound` is now proved from `paper_bridge_recurrence`
  via `quadratic_recurrence_lower_bound`
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## PaperBridge to SAW injection -/

def paperBridge_toSAW {T : ℕ} (b : PaperBridge T) :
    SAW paperStart b.walk.1.length :=
  ⟨b.end_v, b.walk, rfl⟩

lemma paperBridge_toSAW_sigma_injective (T : ℕ) :
    Function.Injective (fun b : PaperBridge T =>
      (⟨b.walk.1.length, paperBridge_toSAW b⟩ : Σ n, SAW paperStart n)) := by
  intro b₁ b₂ h; cases b₁; cases b₂
  unfold paperBridge_toSAW at h; grind

lemma saw_count_paperStart (n : ℕ) :
    Fintype.card (SAW paperStart n) = saw_count n :=
  saw_count_vertex_independent paperStart n

-- paper_bridge_lower_bound and paper_bridge_recurrence are stated after
-- paper_bridge_partition_one_pos (which they depend on).

/-! ## Bridge sum ≤ Z -/

lemma paper_bridge_filter_card_le (T n : ℕ) (F : Finset (PaperBridge T)) :
    (F.filter (fun b => b.walk.1.length = n)).card ≤ saw_count n := by
  have h_inj := paperBridge_toSAW_sigma_injective T
  have h_image : Finset.image (fun b : PaperBridge T =>
      (⟨b.walk.1.length, paperBridge_toSAW b⟩ : Σ n, SAW paperStart n))
      (Finset.filter (fun b : PaperBridge T => b.walk.1.length = n) F) ⊆
      Finset.image (fun s : SAW paperStart n => ⟨n, s⟩)
      (Finset.univ : Finset (SAW paperStart n)) := by
    intro x hx; aesop
  convert Finset.card_le_card h_image using 1
  · rw [Finset.card_image_of_injective _ h_inj]
  · rw [Finset.card_image_of_injective _ fun a b h => by aesop]
    norm_num [saw_count, saw_count_paperStart]

/-
For a finite set of bridges, the total weight is at most Z(xc).
-/
lemma paper_bridge_finite_sum_le (F : Finset (Σ T : ℕ, PaperBridge (T + 1)))
    (hsum : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    ∑ b ∈ F, xc ^ (b.2.walk.1.length) ≤
    ∑' n, (saw_count n : ℝ) * xc ^ n := by
  -- Since each bridge in F useful for our purpose to our every path .1 gives an exact every variety that every path is exact every path that group That exact every path every count of each走上, ensure like was the overall would exactly sum
  let f : (Σ T, PaperBridge (T + 1)) → Σ n, SAW paperStart n := fun p ↦
    ⟨p.snd.walk.1.length, paperBridge_toSAW p.snd⟩;
  -- By definition of $f$, we know that it is injective on $F$.
  have h_inj : Function.Injective f := by
    -- To prove injectivity, assume $f(p1) = f(p2)$ and show $p1 = p2$.
    intro p1 p2 h_eq
    have h_T : p1.fst = p2.fst := by
      have h_endpoints : p1.snd.end_v.1 + p1.snd.end_v.2.1 = -(p1.fst + 1 : ℤ) ∧ p2.snd.end_v.1 + p2.snd.end_v.2.1 = -(p2.fst + 1 : ℤ) := by
        exact ⟨ p1.snd.end_right.1, p2.snd.end_right.1 ⟩;
      grind +locals;
    have := paperBridge_toSAW_sigma_injective ( p1.fst + 1 ) ; aesop;
  have h_sum_le : ∑ b ∈ F, xc ^ (b.snd.walk.1.length) ≤ ∑ n ∈ (Finset.image (fun b => b.snd.walk.1.length) F), (Finset.filter (fun b => b.snd.walk.1.length = n) F).card * xc ^ n := by
    rw [ Finset.sum_image' ];
    intro i hi; rw [ Finset.sum_congr rfl fun j hj => by rw [ Finset.mem_filter.mp hj |>.2 ] ] ; simp +decide [ mul_comm ] ;
  have h_sum_le : ∑ n ∈ (Finset.image (fun b => b.snd.walk.1.length) F), (Finset.filter (fun b => b.snd.walk.1.length = n) F).card * xc ^ n ≤ ∑ n ∈ (Finset.image (fun b => b.snd.walk.1.length) F), (saw_count n : ℝ) * xc ^ n := by
    gcongr;
    · exact pow_nonneg ( by rw [ xc ] ; positivity ) _;
    · have h_card_le : (Finset.filter (fun b => b.snd.walk.1.length = ‹_›) F).card ≤ (Finset.image (fun b => f b) (Finset.filter (fun b => b.snd.walk.1.length = ‹_›) F)).card := by
        rw [ Finset.card_image_of_injective _ h_inj ];
      refine le_trans h_card_le ?_;
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun s => ⟨ _, s ⟩ ) ( Finset.univ : Finset ( SAW paperStart ‹_› ) );
      · grind;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by injection hxy ] ; simp +decide [ saw_count_paperStart ];
  exact le_trans ‹_› ( h_sum_le.trans ( Summable.sum_le_tsum _ ( fun _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg ( show 0 ≤ xc by exact div_nonneg zero_le_one ( Real.sqrt_nonneg _ ) ) _ ) ) hsum ) )

/-- Each individual paper_bridge_partition is summable (partial sums bounded by 1/xc). -/
lemma paper_bridge_summable (T : ℕ) (hT : 1 ≤ T) :
    Summable (fun b : PaperBridge T => xc ^ b.walk.1.length) := by
  exact summable_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => paper_bridge_partial_sum_le T hT F)

/-! ## Paper bridge positivity -/

/-- An explicit bridge of width 1: paperStart → (-1, 0, false). -/
noncomputable def paperBridge_width1 : PaperBridge 1 where
  end_v := (-1, 0, false)
  walk := ⟨SimpleGraph.Walk.cons (by decide : hexGraph.Adj paperStart (-1, 0, false)) .nil,
           by simp [SimpleGraph.Walk.cons_isPath_iff, paperStart]⟩
  end_right := by constructor <;> decide
  in_strip := by intro v hv; simp at hv; rcases hv with rfl | rfl <;> decide

/-- paper_bridge_partition 1 xc > 0: there exists at least one bridge of width 1. -/
lemma paper_bridge_partition_one_pos : 0 < paper_bridge_partition 1 xc := by
  exact lt_of_lt_of_le (pow_pos xc_pos _)
    (Summable.le_tsum (paper_bridge_summable 1 (by norm_num))
      paperBridge_width1 (fun b _ => pow_nonneg xc_pos.le _))

/-! ## Bridge recurrence and lower bound -/

/-- The paper bridge partition function satisfies a quadratic recurrence.
    This follows from the strip identity for the infinite strip
    combined with the cutting argument and monotonicity of E.
    **Status: sorry.** -/
lemma paper_bridge_recurrence :
    ∃ α > 0, ∀ T : ℕ,
      paper_bridge_partition T xc ≤ α * paper_bridge_partition (T + 1) xc ^ 2 +
        paper_bridge_partition (T + 1) xc := by
  sorry

/-- Paper bridge lower bound: ∃ c > 0, paper_bridge_partition T xc ≥ c/T.
    Uses the quadratic recurrence and positivity of bridges. -/
theorem paper_bridge_lower_bound :
    ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ paper_bridge_partition T xc := by
  obtain ⟨α, hα_pos, hrecur⟩ := paper_bridge_recurrence
  have hB_nn : ∀ T, 0 ≤ paper_bridge_partition T xc :=
    fun T => tsum_nonneg fun _ => pow_nonneg xc_pos.le _
  have hB1 := paper_bridge_partition_one_pos
  exact ⟨min (paper_bridge_partition 1 xc) (1 / α),
    lt_min hB1 (div_pos one_pos hα_pos),
    quadratic_recurrence_lower_bound hα_pos hB_nn hrecur hB1⟩

/-
paper_bridge_partition T xc > 0 for all T ≥ 1.
    Bridges exist: constructed by extending a width-1 bridge step by step.
-/
lemma paper_bridge_partition_pos (T : ℕ) (hT : 1 ≤ T) :
    0 < paper_bridge_partition T xc := by
  -- By definition of $paper_bridge_partition$, there exists at least one bridge of width $T$.
  obtain ⟨b, hb⟩ : ∃ b : PaperBridge T, True := by
    induction' hT with T hT ih <;> norm_num at *;
    · exact ⟨ paperBridge_width1 ⟩;
    · obtain ⟨ b, hb ⟩ := ih;
      refine' ⟨ ⟨ _, _, _, _ ⟩ ⟩ <;> norm_num [ PaperInfStrip ] at *;
      exact ( b.1 - 1, b.2.1, false );
      refine' ⟨ hb.1.append ( SimpleGraph.Walk.cons ( show hexGraph.Adj b ( b.1, b.2.1, true ) from _ ) ( SimpleGraph.Walk.cons ( show hexGraph.Adj ( b.1, b.2.1, true ) ( b.1 - 1, b.2.1, false ) from _ ) SimpleGraph.Walk.nil ) ), _ ⟩ <;> simp_all +decide [ hexGraph ];
      all_goals norm_num [ SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append ] at *;
      · simp_all +decide [ List.nodup_append, List.nodup_cons ];
        intro a a_1; constructor <;> intro h₁ h₂ h₃ <;> simp_all +decide [ PaperInfStrip ] ;
        · grind;
        · grind +ring;
      · linarith;
      · intro a a_1; constructor <;> intro h <;> rcases h with ( h | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ PaperInfStrip ] ;
        · linarith [ ( ‹∀ a a_2 : ℤ, ( ( a, a_2, false ) ∈ ( hb : SimpleGraph.Walk hexGraph paperStart b ).support → -↑T ≤ a + a_2 ∧ a + a_2 ≤ -1 ) ∧ ( ( a, a_2, true ) ∈ ( hb : SimpleGraph.Walk hexGraph paperStart b ).support → 1 ≤ a + a_2 + ↑T ∧ a + a_2 ≤ 0 ) › a a_1 ) |>.1 h ];
        · constructor <;> linarith;
        · grind +ring;
  refine' lt_of_lt_of_le _ ( Summable.le_tsum _ b _ );
  · exact pow_pos ( by rw [ show xc = 1 / ( Real.sqrt ( 2 + Real.sqrt 2 ) ) by rfl ] ; positivity ) _;
  · convert paper_bridge_summable T hT using 1;
  · exact fun _ _ => pow_nonneg xc_pos.le _

lemma paper_bridge_sum_le_Z (N : ℕ) (_hx : 0 < xc)
    (hsum : Summable (fun n => (saw_count n : ℝ) * xc ^ n)) :
    ∑ T ∈ Finset.range N, paper_bridge_partition (T + 1) xc ≤
    ∑' n, (saw_count n : ℝ) * xc ^ n := by
  have h_finite_sum : ∀ T ∈ Finset.range N, ∀ ε > 0, ∃ F : Finset (PaperBridge (T + 1)), ∑ b ∈ F, xc ^ (b.walk.1.length) ≥ paper_bridge_partition (T + 1) xc - ε / (N + 1) := by
    intros T hT ε hε_pos
    have h_finite_sum : Filter.Tendsto (fun F : Finset (PaperBridge (T + 1)) => ∑ b ∈ F, xc ^ (b.walk.1.length)) (Filter.atTop : Filter (Finset (PaperBridge (T + 1)))) (nhds (paper_bridge_partition (T + 1) xc)) := by
      exact Summable.hasSum ( paper_bridge_summable _ <| Nat.succ_pos _ ) |> fun h => h.comp <| Filter.tendsto_atTop_atTop.mpr fun F => ⟨ F, fun G hG => Finset.le_iff_subset.mpr hG ⟩;
    exact Filter.Eventually.exists ( h_finite_sum.eventually ( le_mem_nhds <| sub_lt_self _ <| by positivity ) );
  choose! F hF using h_finite_sum;
  have h_combined : ∀ ε > 0, ∑ T ∈ Finset.range N, (paper_bridge_partition (T + 1) xc - ε / (N + 1)) ≤ ∑' n, (saw_count n : ℝ) * xc ^ n := by
    intros ε hε_pos
    have h_combined : ∑ T ∈ Finset.range N, ∑ b ∈ F T ε, xc ^ (b.walk.1.length) ≤ ∑' n, (saw_count n : ℝ) * xc ^ n := by
      convert paper_bridge_finite_sum_le _ hsum using 1;
      rw [ Finset.sum_sigma' ];
    exact le_trans ( Finset.sum_le_sum fun T hT => hF T hT ε hε_pos ) h_combined;
  have h_combined : Filter.Tendsto (fun ε : ℝ => ∑ T ∈ Finset.range N, (paper_bridge_partition (T + 1) xc - ε / (N + 1))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑ T ∈ Finset.range N, paper_bridge_partition (T + 1) xc)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
  exact le_of_tendsto h_combined ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by aesop )

/-! ## Z(xc) diverges -/

theorem Z_xc_diverges_corrected :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := paper_bridge_lower_bound
  intro h_summable
  have h_bridge_summable : Summable (fun T : ℕ =>
      paper_bridge_partition (T + 1) xc) :=
    summable_of_sum_range_le
      (fun T => tsum_nonneg fun _ => pow_nonneg xc_pos.le _)
      (fun N => paper_bridge_sum_le_Z N xc_pos h_summable)
  have h_lower : ∀ T : ℕ, c / ((T : ℝ) + 1) ≤
      paper_bridge_partition (T + 1) xc := by
    intro T; have := hc_bound (T + 1) (by omega); push_cast at this ⊢; linarith
  exact absurd
    (Summable.of_nonneg_of_le (fun T => by positivity) h_lower h_bridge_summable)
    (not_summable_of_lower_bound hc_pos (fun n => le_refl _))

/-! ## Bridge decay -/

/-- Paper bridge decay: paper_bridge_partition T x ≤ (x/xc)^T / xc.
    Uses partial sum bounds only (no circular dependency). -/
theorem paper_bridge_decay {T : ℕ} (hT : 1 ≤ T) {x : ℝ}
    (hx : 0 < x) (hxc : x < xc) :
    paper_bridge_partition T x ≤ (x / xc) ^ T / xc := by
  apply Real.tsum_le_of_sum_le (fun b => pow_nonneg hx.le _)
  intro F
  have h_pw : ∀ b ∈ F, x ^ b.walk.1.length ≤
      (x / xc) ^ T * xc ^ b.walk.1.length := by
    intro b _
    have hlen := paper_bridge_length_ge T b
    rw [show x ^ b.walk.1.length =
        (x / xc) ^ b.walk.1.length * xc ^ b.walk.1.length from
      by rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt xc_pos)]]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (div_nonneg hx.le xc_pos.le)
        ((div_le_one xc_pos).mpr hxc.le) hlen)
      (pow_nonneg xc_pos.le _)
  have h1 : ∑ b ∈ F, x ^ b.walk.1.length ≤
      ∑ b ∈ F, ((x / xc) ^ T * xc ^ b.walk.1.length) :=
    Finset.sum_le_sum h_pw
  have h2 : ∑ b ∈ F, ((x / xc) ^ T * xc ^ b.walk.1.length) =
      (x / xc) ^ T * ∑ b ∈ F, xc ^ b.walk.1.length := by
    rw [← Finset.mul_sum]
  have h3 : ∑ b ∈ F, xc ^ b.walk.1.length ≤ 1 / xc :=
    paper_bridge_partial_sum_le T hT F
  have h4 := mul_le_mul_of_nonneg_left h3
    (pow_nonneg (div_nonneg hx.le xc_pos.le) T)
  have h5 : (x / xc) ^ T * (1 / xc) = (x / xc) ^ T / xc := by ring
  nlinarith

lemma paper_bridge_partition_nonneg (T : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ paper_bridge_partition T x :=
  tsum_nonneg fun _ => pow_nonneg hx.le _

/-! ## Hammersley-Welsh decomposition and summability -/

/-- Bridge decomposition injection (paper bridges).
    **Status: sorry.** This is the Hammersley-Welsh decomposition. -/
theorem paper_bridge_decomp_injection {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

/-
Hammersley-Welsh summability: Z(x) < ∞ for 0 < x < xc.
    Proved from paper_bridge_decomp_injection + paper_bridge_decay +
    geometric product convergence. No circular dependency on
    hammersley_welsh_injection.
-/
theorem hw_summable_corrected {x : ℝ} (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  -- Use decay + decomposition (NOT hammersley_welsh_injection from SAWBridgeFix)
  set r := x / xc with hr_def
  have hr0 : 0 ≤ r := div_nonneg hx.le xc_pos.le
  have hr1 : r < 1 := (div_lt_one xc_pos).mpr hxc
  have h_decay : ∀ T : ℕ, paper_bridge_partition (T + 1) x ≤
      (1 / xc) * r ^ (T + 1) := by
    intro T
    have h := @paper_bridge_decay (T + 1) (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero T)) x hx hxc
    simp only [hr_def] at h ⊢
    linarith [show (x / xc) ^ (T + 1) / xc = 1 / xc * (x / xc) ^ (T + 1) from by ring]
  -- Uniform bound on partial sums via the decomposition
  have h_summ_geo : Summable (fun T : ℕ => r ^ (T + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  set M := 2 * Real.exp (2 / xc * ∑' T : ℕ, r ^ (T + 1)) with hM_def
  suffices hbound : ∀ N, ∑ n ∈ Finset.range N, (saw_count n : ℝ) * x ^ n ≤ M from
    summable_of_sum_range_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le n))
      hbound
  intro N
  rcases N with _ | N
  · simp; positivity
  calc ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n
      ≤ 2 * (∑ S ∈ (Finset.range N).powerset,
          ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 :=
        paper_bridge_decomp_injection hx hxc N
    _ ≤ M := by
        -- Apply the decay bound to each term in the sum.
        have h_sum_bound : ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, paper_bridge_partition (T + 1) x ≤ ∏ T ∈ Finset.range N, (1 + (1 / xc) * r ^ (T + 1)) := by
          simp +decide [ add_comm, Finset.prod_add ];
          exact Finset.sum_le_sum fun s hs => Finset.prod_le_prod ( fun _ _ => by exact ( by apply_rules [ tsum_nonneg ] ; intros; exact pow_nonneg ( by positivity ) _ ) ) fun _ _ => by simpa using h_decay _;
        -- Apply the exponential bound to the product.
        have h_exp_bound : ∏ T ∈ Finset.range N, (1 + (1 / xc) * r ^ (T + 1)) ≤ Real.exp ((1 / xc) * ∑' T : ℕ, r ^ (T + 1)) := by
          have h_exp_bound : ∏ T ∈ Finset.range N, (1 + (1 / xc) * r ^ (T + 1)) ≤ Real.exp ((1 / xc) * ∑ T ∈ Finset.range N, r ^ (T + 1)) := by
            rw [ Finset.mul_sum _ _ _, Real.exp_sum ];
            exact Finset.prod_le_prod ( fun _ _ => add_nonneg zero_le_one <| mul_nonneg ( one_div_nonneg.mpr <| by linarith ) <| pow_nonneg hr0 _ ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _;
          exact h_exp_bound.trans ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left ( Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => by positivity ) h_summ_geo ) <| by exact one_div_nonneg.mpr <| by linarith [ show 0 ≤ xc by exact div_nonneg zero_le_one <| Real.sqrt_nonneg _ ] );
        convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => ?_ ) ( h_sum_bound.trans h_exp_bound ) 2 ) zero_le_two using 1 ; ring;
        · rw [ ← Real.exp_nat_mul ] ; ring!;
        · exact paper_bridge_partition_nonneg (_ + 1) x hx

/-! ## Main theorem -/

/-- **Main Theorem** (Duminil-Copin & Smirnov, 2012, corrected):
    μ = √(2+√2). -/
theorem connective_constant_eq_corrected :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) :=
  connective_constant_eq_from_bounds
    Z_xc_diverges_corrected
    (fun x hx hxc => hw_summable_corrected hx hxc)

end