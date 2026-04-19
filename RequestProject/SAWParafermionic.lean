/-
# Walk reconstruction and cutting map infrastructure

Proves `extra_walk_sum_le_proved`: the sum over extra walks is bounded by xc · B².
-/

import Mathlib
import RequestProject.SAWCutting
import RequestProject.SAWCuttingHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Walk equality from support equality -/

/-- On a simple graph, walks with the same support are equal. -/
def walk_eq_of_support {G : SimpleGraph V} [DecidableEq V]
    {v w : V} : (p q : G.Walk v w) → p.support = q.support → p = q
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by exfalso; have := congr_arg List.length h; simp at this
  | .cons _ _, .nil, h => by exfalso; have := congr_arg List.length h; simp at this
  | @SimpleGraph.Walk.cons _ _ u v₁ w hadj p', @SimpleGraph.Walk.cons _ _ _ v₂ _ hadj' q', h => by
    have hsup : p'.support = q'.support := List.tail_eq_of_cons_eq h
    have hv : v₁ = v₂ := by
      rw [SimpleGraph.Walk.support_eq_cons p', SimpleGraph.Walk.support_eq_cons q'] at hsup
      exact List.head_eq_of_cons_eq hsup
    subst hv; exact congr_arg _ (walk_eq_of_support p' q' hsup)

/-- Path equality from walk support equality. -/
lemma path_eq_of_support {G : SimpleGraph V} [DecidableEq V]
    {v w : V} (p q : G.Path v w) (h : p.1.support = q.1.support) :
    p = q := Subtype.ext (walk_eq_of_support p.1 q.1 h)

/-! ## Walk reconstruction from parts -/

lemma path_determined_by_parts {v w : HexVertex}
    (p₁ p₂ : hexGraph.Path v w)
    (u : HexVertex) (hu₁ : u ∈ p₁.1.support) (hu₂ : u ∈ p₂.1.support)
    (h_take : p₁.1.takeUntil u hu₁ = p₂.1.takeUntil u hu₂)
    (h_drop : p₁.1.dropUntil u hu₁ = p₂.1.dropUntil u hu₂) :
    p₁ = p₂ := by
  have h1 := (SimpleGraph.Walk.take_spec p₁.1 hu₁).symm
  have h2 := (SimpleGraph.Walk.take_spec p₂.1 hu₂).symm
  ext; rw [h1, h2, h_take, h_drop]

/-! ## Suffix bridge construction -/

noncomputable def mkSuffixBridge {T : ℕ}
    (end_v cut_v : HexVertex)
    (h_end_diag : end_v.1 + end_v.2.1 = 0) (h_end_true : end_v.2.2 = true)
    (h_cut_diag : cut_v.1 + cut_v.2.1 = -(T + 1 : ℤ)) (h_cut_false : cut_v.2.2 = false)
    (q : hexGraph.Walk cut_v end_v) (hq : q.IsPath)
    (h_strip : ∀ u ∈ q.support, PaperInfStrip (T + 1) u) :
    PaperBridge (T + 1) :=
  let dx := -end_v.1
  let dy := -end_v.2.1
  let hsum : dx + dy = 0 := by omega
  let hstart : hexShift dx dy end_v = paperStart := by
    show (end_v.1 + dx, end_v.2.1 + dy, end_v.2.2) = (0, 0, true)
    simp [h_end_true]; omega
  ⟨hexShift dx dy cut_v,
   ⟨(shiftWalk dx dy q.reverse).copy hstart rfl,
    by rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_copy,
           ← SimpleGraph.Walk.isPath_def]
       exact shiftWalk_isPath dx dy q.reverse hq.reverse⟩,
   ⟨by show (cut_v.1 + dx) + (cut_v.2.1 + dy) = -(↑(T+1) : ℤ); push_cast; omega,
    h_cut_false⟩,
   fun u hu => by
     have : u ∈ (shiftWalk dx dy q.reverse).support := by
       rw [← SimpleGraph.Walk.support_copy _ hstart (rfl : hexShift dx dy cut_v = _)]
       exact hu
     rw [shiftWalk_support] at this
     obtain ⟨u', hu', rfl⟩ := List.mem_map.mp this
     exact hexShift_preserves_strip hsum (h_strip u' (by
       rw [SimpleGraph.Walk.support_reverse] at hu'
       exact List.mem_reverse.mp hu'))⟩

@[simp] lemma mkSuffixBridge_walk_length {T : ℕ}
    (end_v cut_v : HexVertex)
    (h1 : end_v.1 + end_v.2.1 = 0) (h2 : end_v.2.2 = true)
    (h3 : cut_v.1 + cut_v.2.1 = -(T + 1 : ℤ)) (h4 : cut_v.2.2 = false)
    (q : hexGraph.Walk cut_v end_v) (hq : q.IsPath)
    (hs : ∀ u ∈ q.support, PaperInfStrip (T + 1) u) :
    (mkSuffixBridge end_v cut_v h1 h2 h3 h4 q hq hs).walk.1.length = q.length := by
  simp [mkSuffixBridge, SimpleGraph.Walk.length_copy, shiftWalk_length,
        SimpleGraph.Walk.length_reverse]

/-! ## Cutting map definitions -/

noncomputable def extraWalkCutVertex {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    {v : HexVertex // v ∈ s.walk.1.support ∧
      v.1 + v.2.1 = -(T + 1 : ℤ) ∧ v.2.2 = false} :=
  let h := A_inf_diff_reaches_boundary hT s h_not
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

noncomputable def extraWalkB1 {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    PaperBridge (T + 1) :=
  let d := extraWalkCutVertex hT s h_not
  ⟨d.1,
   ⟨s.walk.1.takeUntil d.1 d.2.1, s.walk.2.takeUntil d.2.1⟩,
   ⟨by have := d.2.2.1; omega, d.2.2.2⟩,
   fun u hu => s.in_strip u (s.walk.1.support_takeUntil_subset d.2.1 hu)⟩

noncomputable def extraWalkB2 {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    PaperBridge (T + 1) :=
  let d := extraWalkCutVertex hT s h_not
  mkSuffixBridge s.end_v d.1
    s.end_left.1 s.end_left.2.1
    d.2.2.1 d.2.2.2
    (s.walk.1.dropUntil d.1 d.2.1)
    (s.walk.2.dropUntil d.2.1)
    (fun u hu => s.in_strip u (s.walk.1.support_dropUntil_subset d.2.1 hu))

lemma extraWalk_length_rel {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not : ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    s.walk.1.length = (extraWalkB1 hT s h_not).walk.1.length +
                       (extraWalkB2 hT s h_not).walk.1.length := by
  simp only [extraWalkB1, extraWalkB2]
  rw [mkSuffixBridge_walk_length]
  exact (walk_split_lengths s.walk.1 (extraWalkCutVertex hT s h_not).2.1).symm

/-! ## Injectivity of the cutting map -/

set_option maxHeartbeats 3200000

/-
The cutting map s ↦ (b1(s), b2(s)) is injective.
-/
lemma extraWalk_cut_injective {T : ℕ} (hT : 0 < T)
    {s₁ s₂ : PaperSAW_A_inf (T + 1)}
    {h₁ : ¬∀ v ∈ s₁.walk.1.support, PaperInfStrip T v}
    {h₂ : ¬∀ v ∈ s₂.walk.1.support, PaperInfStrip T v}
    (hb1 : extraWalkB1 hT s₁ h₁ = extraWalkB1 hT s₂ h₂)
    (hb2 : extraWalkB2 hT s₁ h₁ = extraWalkB2 hT s₂ h₂) :
    s₁ = s₂ := by
  -- Step 1: Equal cut vertices
  have hcut : (extraWalkCutVertex hT s₁ h₁).1 = (extraWalkCutVertex hT s₂ h₂).1 := by
    have := congr_arg PaperBridge.end_v hb1; simpa [extraWalkB1]
  -- Step 2: Equal end_v
  have hend : s₁.end_v = s₂.end_v := by
    have hev1 := show (extraWalkB2 hT s₁ h₁).end_v = hexShift (-s₁.end_v.1) (-s₁.end_v.2.1) (extraWalkCutVertex hT s₁ h₁).1 by simp [extraWalkB2, mkSuffixBridge]
    have hev2 := show (extraWalkB2 hT s₂ h₂).end_v = hexShift (-s₂.end_v.1) (-s₂.end_v.2.1) (extraWalkCutVertex hT s₂ h₂).1 by simp [extraWalkB2, mkSuffixBridge]
    have hev := show _ = _ from congr_arg PaperBridge.end_v hb2
    rw [hev1, hev2] at hev
    have h1 := congr_arg (·.1) hev; have h2 := congr_arg (·.2.1) hev; simp [hexShift] at h1 h2
    have hc1 := congr_arg (·.1) hcut; have hc2 := congr_arg (·.2.1) hcut
    exact Prod.ext (by linarith) (Prod.ext (by linarith) (by rw [s₁.end_left.2.1, s₂.end_left.2.1]))
  -- Step 3: Equal walks via support equality
  cases s₁ with | mk e₁ w₁ el₁ is₁ =>
  cases s₂ with | mk e₂ w₂ el₂ is₂ =>
  simp only at hend; subst hend; congr 1
  -- Goal: w₁ = w₂ (hexGraph.Path paperStart e₁)
  -- Strategy: show support equality, then use path_eq_of_support
  apply path_eq_of_support;
  have h_take_eq : (w₁.1.takeUntil (extraWalkCutVertex hT ⟨e₁, w₁, el₁, is₁⟩ h₁).1 (extraWalkCutVertex hT ⟨e₁, w₁, el₁, is₁⟩ h₁).2.1).support = (w₂.1.takeUntil (extraWalkCutVertex hT ⟨e₁, w₂, el₂, is₂⟩ h₂).1 (extraWalkCutVertex hT ⟨e₁, w₂, el₂, is₂⟩ h₂).2.1).support := by
    exact congr_arg ( fun x : PaperBridge ( T + 1 ) => x.walk.1.support ) hb1;
  have h_drop_eq : (w₁.1.dropUntil (extraWalkCutVertex hT ⟨e₁, w₁, el₁, is₁⟩ h₁).1 (extraWalkCutVertex hT ⟨e₁, w₁, el₁, is₁⟩ h₁).2.1).support = (w₂.1.dropUntil (extraWalkCutVertex hT ⟨e₁, w₂, el₂, is₂⟩ h₂).1 (extraWalkCutVertex hT ⟨e₁, w₂, el₂, is₂⟩ h₂).2.1).support := by
    replace hb2 := congr_arg ( fun b : PaperBridge ( T + 1 ) => b.walk.1.support ) hb2 ; simp_all +decide [ extraWalkB2 ] ;
    unfold mkSuffixBridge at hb2; simp_all +decide [ SimpleGraph.Walk.support_reverse ] ;
    simp_all +decide [ shiftWalk_support ];
    exact List.map_injective_iff.mpr ( hexShift_injective _ _ ) hb2;
  have h_support_eq : ∀ (p : hexGraph.Walk paperStart e₁) (u : HexVertex) (hu : u ∈ p.support), p.support = (p.takeUntil u hu).support ++ (p.dropUntil u hu).support.tail := by
    intros p u hu; exact (by
    have h_support_eq : p.support = (p.takeUntil u hu).support ++ (p.dropUntil u hu).support.tail := by
      have h_take_drop : p = (p.takeUntil u hu).append (p.dropUntil u hu) := by
        grind +suggestions
      conv_lhs => rw [ h_take_drop ];
      exact?;
    exact h_support_eq);
  rw [ h_support_eq _ _ ( extraWalkCutVertex hT ⟨ e₁, w₁, el₁, is₁ ⟩ h₁ |>.2.1 ), h_support_eq _ _ ( extraWalkCutVertex hT ⟨ e₁, w₂, el₂, is₂ ⟩ h₂ |>.2.1 ), h_take_eq, h_drop_eq ]

/-! ## The sum bound -/

/-
Bridge pair summability.
-/
lemma bridge_pair_summable (T : ℕ) (hT : 1 ≤ T) :
    Summable (fun p : PaperBridge (T + 1) × PaperBridge (T + 1) =>
      xc ^ p.1.walk.1.length * xc ^ p.2.walk.1.length) := by
  have h_summable : Summable (fun b : PaperBridge (T + 1) => xc ^ b.walk.1.length) := by
    refine' summable_of_sum_le _ _;
    exact?;
    · exact fun _ => pow_nonneg ( by exact le_of_lt ( by exact xc_pos ) ) _;
    · intro u;
      -- By definition of $paper_bridge_partition$, we know that
      have h_paper_bridge_partition : ∑ x ∈ u, xc ^ (x.walk.1.length) ≤ 1 / xc := by
        convert paper_bridge_partial_sum_le ( T + 1 ) ( by linarith ) u using 1;
      refine' le_trans h_paper_bridge_partition _;
      rw [ div_le_iff₀ ] <;> norm_num [ xc ];
      · rw [ ← div_eq_mul_inv, one_le_div ] <;> nlinarith [ Real.pi_gt_three, Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 2 + Real.sqrt 2 ), Real.sq_sqrt ( show 0 ≤ 2 by norm_num ), Real.sq_sqrt ( show 0 ≤ 2 + Real.sqrt 2 by positivity ), mul_pos ( Real.sqrt_pos.mpr ( show 0 < 2 by norm_num ) ) ( Real.sqrt_pos.mpr ( show 0 < 2 + Real.sqrt 2 by positivity ) ) ];
      · positivity;
  exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.norm ) ( h_summable.norm ) ;

/-
Product of bridge tsums equals B².
-/
lemma bridge_tsum_prod_eq_sq (T : ℕ) (hT : 1 ≤ T) :
    ∑' (p : PaperBridge (T + 1) × PaperBridge (T + 1)),
      xc ^ p.1.walk.1.length * xc ^ p.2.walk.1.length =
    paper_bridge_partition (T + 1) xc ^ 2 := by
  -- By tsum_mul_tsum_of_summable_norm (from Mathlib.Analysis.Normed.Ring.InfiniteSum), the product of two summable series is equal to the sum of the products of their terms.
  have h_tsum_mul_tsum : (∑' b₁ : PaperBridge (T + 1), xc ^ (b₁.walk.1.length : ℕ)) * (∑' b₂ : PaperBridge (T + 1), xc ^ (b₂.walk.1.length : ℕ)) = ∑' p : PaperBridge (T + 1) × PaperBridge (T + 1), xc ^ (p.1.walk.1.length : ℕ) * xc ^ (p.2.walk.1.length : ℕ) := by
    rw [ Summable.tsum_prod ];
    · simp +decide only [tsum_mul_left, tsum_mul_right];
    · convert bridge_pair_summable T hT using 1;
  rw [ ← h_tsum_mul_tsum, sq ];
  rfl

set_option maxHeartbeats 6400000 in
/-- The sum over extra walks is bounded by xc · B². -/
theorem extra_walk_sum_le_proved {T : ℕ} (hT : 1 ≤ T)
    (F : Finset (PaperSAW_A_inf (T + 1)))
    (hF : ∀ s ∈ F, ¬∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    ∑ s ∈ F, xc ^ (s.walk.1.length + 1) ≤
    xc * paper_bridge_partition (T + 1) xc ^ 2 := by
  classical
  have hT' : 0 < T := by omega
  rw [← Finset.sum_attach]
  set φ : {s // s ∈ F} → PaperBridge (T + 1) × PaperBridge (T + 1) :=
    fun s => (extraWalkB1 hT' s.1 (hF s.1 s.2), extraWalkB2 hT' s.1 (hF s.1 s.2))
  set f : PaperBridge (T + 1) × PaperBridge (T + 1) → ℝ :=
    fun p => xc ^ p.1.walk.1.length * xc ^ p.2.walk.1.length
  have h_eq : ∀ s : {s // s ∈ F},
      xc ^ (s.1.walk.1.length + 1) = xc * f (φ s) := by
    intro ⟨s, hs⟩; simp only [φ, f]
    rw [extraWalk_length_rel hT' s (hF s hs)]; ring
  simp_rw [h_eq, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ xc_pos.le
  rw [← bridge_tsum_prod_eq_sq T hT]
  have hφ_inj : Function.Injective φ := by
    intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ h
    exact Subtype.ext (extraWalk_cut_injective hT' (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2)
  calc ∑ s ∈ Finset.univ, f (φ s)
      = ∑ p ∈ Finset.univ.image φ, f p :=
        (Finset.sum_image (fun a _ b _ h => hφ_inj h)).symm
    _ ≤ ∑' p, f p :=
        Summable.sum_le_tsum _ (fun _ _ => mul_nonneg (pow_nonneg xc_pos.le _) (pow_nonneg xc_pos.le _))
          (bridge_pair_summable T hT)

end