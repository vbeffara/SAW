/-
# Bridge decomposition and partition function analysis

From Section 3 of Duminil-Copin & Smirnov (2012).

## Content

1. **Partition function** Z(x) = Σ c_n x^n
2. **Radius of convergence** equals 1/μ
3. **Bridge definitions** and bridge partition function
4. **Elementary SAW bounds** (degree, step count, upper bound)
5. **Reduction**: μ = √(2+√2) from partition function bounds
-/

import RequestProject.SAWMain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Partition function -/

/-- The partition function Z(x) = Σ c_n · x^n. -/
def Z (x : ℝ) : ℝ := ∑' n, (saw_count n : ℝ) * x ^ n

/-! ## Abstract radius of convergence -/

/-- c_n ≥ μ^n for all n ≥ 1, since μ = inf c_n^{1/n}. -/
lemma saw_count_ge_cc_pow (n : ℕ) (hn : 1 ≤ n) :
    connective_constant ^ n ≤ (saw_count n : ℝ) := by
  have h_le : connective_constant ≤ (saw_count n : ℝ) ^ (1 / (n : ℝ)) :=
    csInf_le ⟨ 0, Set.forall_mem_image.2 fun n hn => by positivity ⟩ ⟨ n, hn, rfl ⟩
  exact le_trans (pow_le_pow_left₀ (by exact Real.sInf_nonneg <| by rintro x ⟨ m, hm, rfl ⟩; positivity) h_le _)
    (by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel (by positivity), Real.rpow_one])

/-- Z(x) diverges for x > 1/μ. -/
theorem partition_diverges_above_inv_cc {x : ℝ} (hx : 0 < x)
    (hxcc : connective_constant⁻¹ < x) :
    ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  have h_bound : ∀ n ≥ 1, (saw_count n : ℝ) ≥ connective_constant ^ n :=
    fun n a => saw_count_ge_cc_pow n a
  have hcc_ge_one : connective_constant ≥ 1 := by
    refine' le_csInf _ _ <;> norm_num
    exact fun n hn => Real.one_le_rpow (mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| saw_count_pos n) <| by positivity
  have hcc_pos : 0 < connective_constant := lt_of_lt_of_le (by norm_num) hcc_ge_one
  have h_exp_growth : ∀ n ≥ 1, (connective_constant * x) ^ n ≥ 1 :=
    fun n hn => one_le_pow₀ (by nlinarith [inv_mul_cancel₀ (ne_of_gt hcc_pos)])
  have h_series_growth : ∀ n ≥ 1, (saw_count n : ℝ) * x ^ n ≥ 1 :=
    fun n hn => le_trans (h_exp_growth n hn) (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (h_bound n hn) (pow_nonneg hx.le _))
  exact fun h => absurd (h.tendsto_atTop_zero) fun H =>
    absurd (le_of_tendsto_of_tendsto tendsto_const_nhds H <|
      Filter.eventually_atTop.mpr ⟨1, fun n hn => h_series_growth n hn⟩) (by norm_num)

/-- Z(x) converges for 0 < x < 1/μ, by comparison with geometric series. -/
theorem partition_converges_below_inv_cc {x : ℝ} (hx : 0 < x)
    (hxcc : x < connective_constant⁻¹) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  have hccx : connective_constant * x < 1 := by
    rw [mul_comm]; rwa [inv_eq_one_div, lt_div_iff₀ connective_constant_pos'] at hxcc
  set r := (1 + connective_constant * x) / 2
  have hr_lt : r < 1 := by simp only [r]; linarith
  have hr_pos : 0 < r := by simp only [r]; nlinarith [mul_pos connective_constant_pos' hx]
  have hrx : connective_constant < r / x := by
    rw [lt_div_iff₀ hx]; simp only [r]; nlinarith
  have hev : ∀ᶠ n in Filter.atTop,
      (saw_count n : ℝ) ^ (1 / (n : ℝ)) < r / x :=
    connective_constant_is_limit'.eventually (gt_mem_nhds hrx)
  refine Summable.of_norm_bounded_eventually_nat (g := fun n => r ^ n)
    (summable_geometric_of_lt_one hr_pos.le hr_lt) ?_
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with n hn hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le n))]
  have hsn : (saw_count n : ℝ) ≤ (r / x) ^ n := by
    have h1 : (saw_count n : ℝ) = ((saw_count n : ℝ) ^ (1 / (n : ℝ))) ^ (n : ℕ) := by
      rw [← Real.rpow_natCast ((saw_count n : ℝ) ^ _),
          ← Real.rpow_mul (Nat.cast_nonneg _),
          one_div_mul_cancel (by positivity : (n : ℝ) ≠ 0),
          Real.rpow_one]
    rw [h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn.le n
  calc (saw_count n : ℝ) * x ^ n
      ≤ (r / x) ^ n * x ^ n := mul_le_mul_of_nonneg_right hsn (pow_nonneg hx.le n)
    _ = r ^ n := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n (ne_of_gt hx))]

/-! ## Characterization of the connective constant -/

/-- μ = 1/x₀ if Z diverges for x > x₀ and converges for x < x₀. -/
theorem cc_eq_inv_of_partition_radius {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hdiv : ∀ x, x₀ < x → ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n))
    (hconv : ∀ x, 0 < x → x < x₀ → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = x₀⁻¹ := by
  have h_inv_le_x₀ : connective_constant⁻¹ ≤ x₀ := by
    contrapose! hdiv
    exact ⟨(x₀ + connective_constant⁻¹) / 2, by linarith,
      partition_converges_below_inv_cc (by linarith) (by linarith)⟩
  have h_inv_ge_x₀ : connective_constant⁻¹ ≥ x₀ := by
    by_contra h_contra
    obtain ⟨x, hx₀_lt_x, hx_lt_x₀⟩ := exists_between (lt_of_not_ge h_contra)
    have hcc_pos := connective_constant_pos'
    exact absurd (hconv x (by linarith [inv_pos.mpr hcc_pos]) hx_lt_x₀)
      (partition_diverges_above_inv_cc (by linarith [inv_pos.mpr hcc_pos]) hx₀_lt_x)
  exact inv_eq_iff_eq_inv.mp (le_antisymm h_inv_le_x₀ h_inv_ge_x₀) ▸ by norm_num

/-- Z diverges monotonically: if it diverges at x₀ > 0, it diverges for all x ≥ x₀. -/
private lemma partition_diverges_mono {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x)
    (hdiv : ¬ Summable (fun n => (saw_count n : ℝ) * x₀ ^ n)) :
    ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  intro h
  exact hdiv (Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx₀.le _))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₀.le hx _) (Nat.cast_nonneg _))
    h)

/-! ## Bridge definitions -/

/-- A bridge of width T: a SAW crossing a strip of width T.
    Start at x-coordinate 0, end at x-coordinate T, all vertices in [0, T]. -/
structure Bridge (T : ℕ) where
  start_v : HexVertex
  end_v : HexVertex
  walk : hexGraph.Path start_v end_v
  start_left : start_v.1 = 0
  end_right : end_v.1 = T
  in_strip : ∀ v ∈ walk.1.support, 0 ≤ v.1 ∧ v.1 ≤ T

/-- The bridge partition function B_T(x) = Σ_{γ : bridge of width T} x^{ℓ(γ)}. -/
def bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : Bridge T), x ^ b.walk.1.length

/-! ## Elementary bounds on SAW counts -/

/-- Every vertex in hexGraph has exactly 3 neighbors. -/
lemma hexGraph_degree (v : HexVertex) : (hexGraph.neighborFinset v).card = 3 := by
  cases' v with x y b
  cases y; simp +decide [hexGraph]
  cases ‹Bool› <;> simp +decide [SimpleGraph.degree, SimpleGraph.neighborFinset]
  · rename_i y; exact Finset.card_eq_three.mpr ⟨(x, y, true), (x + 1, y, true), (x, y + 1, true), by aesop⟩
  · rename_i y; erw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem] <;> simp +decide
    grind

/-- For a path of length ≥ 1 ending at w, at most 2 of w's 3 neighbors
    are not in the path's support. -/
lemma path_extension_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) (hn : 1 ≤ p.length) :
    ((hexGraph.neighborFinset w).filter (fun u => u ∉ p.support)).card ≤ 2 := by
  obtain ⟨prev, hprev⟩ : ∃ prev : HexVertex, prev ∈ p.support ∧ hexGraph.Adj prev w := by
    induction p; aesop; cases ‹SimpleGraph.Walk _ _ _› <;> aesop
  have h_prev_in : prev ∈ Finset.filter (fun u => u ∈ p.support) (hexGraph.neighborFinset w) := by
    simp_all +decide [SimpleGraph.neighborFinset]; exact hprev.2.symm
  have : (Finset.filter (fun u => u ∉ p.support) (hexGraph.neighborFinset w)).card ≤
      (hexGraph.neighborFinset w).card - 1 := by
    have h := @Finset.card_filter_add_card_filter_not _ (s := hexGraph.neighborFinset w) (fun u => u ∈ p.support) _ _
    exact Nat.le_sub_one_of_lt (by linarith [Finset.card_pos.mpr ⟨prev, h_prev_in⟩])
  exact this.trans (by rw [hexGraph_degree])

/-- For a path p of length > n, the vertex at position n+1 is not in
    the support of p.take n. -/
lemma getVert_succ_not_in_take_support {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath) (n : ℕ) (hn : n < p.length) :
    p.getVert (n + 1) ∉ (p.take n).support := by
  have h_support_take : (p.take n).support = p.support.take (n + 1) :=
    SimpleGraph.Walk.take_support_eq_support_take_succ p n
  rw [h_support_take, List.mem_iff_get]
  have := hp.support_nodup; simp_all +decide [List.nodup_iff_injective_get]
  intro x hx
  have := @this ⟨x, by grind⟩ ⟨n + 1, by simp +arith +decide at *; linarith⟩
  simp_all +decide
  exact absurd (this (by exact SimpleGraph.Walk.getVert_eq_support_getElem p hn))
    (by linarith [Fin.is_lt x, List.length_take_le (n + 1) p.support])

/-- Truncation of an (n+1)-step SAW to an n-step SAW. -/
private def truncSAW (n : ℕ) (s : SAW hexOrigin (n + 1)) : SAW hexOrigin n where
  w := s.p.1.getVert n
  p := ⟨s.p.1.take n, by
    refine SimpleGraph.Walk.IsPath.mk' ?_
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
    exact s.p.2.support_nodup.take⟩
  l := by rw [SimpleGraph.Walk.take_length]; simp [s.l]

/-- Fiber counting: if every fiber of f has ≤ k elements, then |α| ≤ k·|β|. -/
private lemma card_le_mul_of_fiber_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (k : ℕ) (hk : ∀ b : β, (Finset.univ.filter (fun a => f a = b)).card ≤ k) :
    Fintype.card α ≤ k * Fintype.card β := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  linarith [Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hk b),
            show ∑ _ ∈ (Finset.univ : Finset β), k = k * Fintype.card β from
              by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_comm]]

private lemma saw_eq_of_trunc_and_last (n : ℕ) (s₁ s₂ : SAW hexOrigin (n + 1))
    (h_trunc : truncSAW n s₁ = truncSAW n s₂) (h_last : s₁.w = s₂.w) : s₁ = s₂ := by
  cases' s₁ with s₁_p s₁_w s₁_l s₁_p_path s₁_w_path s₁_l_eq
  cases' s₂ with s₂_p s₂_w s₂_l s₂_p_path s₂_w_path s₂_l_eq
  simp_all +decide [truncSAW]
  have h_drop_form : ∀ {v w : HexVertex} {p : hexGraph.Walk v w}, p.length = 1 → ∃ adj : hexGraph.Adj v w, p = .cons adj .nil := by
    intros v w p hp_length; rcases p with (_ | ⟨adj, p⟩) <;> simp_all +decide
    cases p <;> aesop (simp_config := { singlePass := true })
  generalize_proofs at *
  have h_walk_eq : s₁_w.1 = (s₁_w.1.take n).append (s₁_w.1.drop n) ∧ s₂_w.1 = (s₂_w.1.take n).append (s₂_w.1.drop n) := by
    norm_num +zetaDelta at *
  obtain ⟨adj₁, h_adj₁⟩ := h_drop_form (by
  rw [ SimpleGraph.Walk.drop_length ] ; norm_num [ s₁_l ] : (s₁_w.1.drop n).length = 1)
  obtain ⟨adj₂, h_adj₂⟩ := h_drop_form (by
  rw [ SimpleGraph.Walk.drop_length ] ; simp +decide [ s₂_l ] : (s₂_w.1.drop n).length = 1);
  grind +qlia

private lemma saw_last_adj (n : ℕ) (s : SAW hexOrigin (n + 1)) :
    hexGraph.Adj (s.p.1.getVert n) s.w := by
  have h_last_vertex : s.p.1.getVert (n + 1) = s.w := by
    have : ∀ {v w : HexVertex} {p : hexGraph.Walk v w}, p.length = n + 1 → p.getVert (n + 1) = w := by
      intros v w p hp_length; induction p <;> aesop
    exact this s.l
  convert s.p.1.adj_getVert_succ _
  · exact h_last_vertex.symm
  · linarith [s.l]

private lemma saw_last_not_in_trunc (n : ℕ) (s : SAW hexOrigin (n + 1)) :
    s.w ∉ (truncSAW n s).p.1.support := by
  have h_last_vertex : s.w = s.p.1.getVert (n + 1) := by
    convert rfl using 1
    convert s.p.1.getVert_length using 1
    simp [s.l]
  convert getVert_succ_not_in_take_support s.p.1 s.p.2 n _ using 1; aesop
  linarith [s.l]

private instance SAW.instDecidableEq (v : HexVertex) (n : ℕ) : DecidableEq (SAW v n) := by
  intro ⟨w₁, ⟨p₁, hp₁⟩, hl₁⟩ ⟨w₂, ⟨p₂, hp₂⟩, hl₂⟩
  by_cases hw : w₁ = w₂
  · subst hw
    by_cases hp : p₁ = p₂
    · subst hp; exact isTrue rfl
    · exact isFalse (fun h => hp (by cases h; rfl))
  · exact isFalse (fun h => hw (by cases h; rfl))

/-- c_{n+1} ≤ 2 · c_n for n ≥ 1 (each step has ≤ 2 new choices). -/
lemma saw_count_step_le_mul_two (n : ℕ) (hn : 1 ≤ n) : saw_count (n + 1) ≤ 2 * saw_count n := by
  unfold saw_count
  apply card_le_mul_of_fiber_le (truncSAW n) 2
  intro b
  have h_map : ∀ s : SAW hexOrigin (n + 1), truncSAW n s = b →
      s.w ∈ (hexGraph.neighborFinset b.w).filter (fun u => u ∉ b.p.1.support) := by
    intro s hs
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    exact ⟨by rw [← hs]; exact saw_last_adj n s, by rw [← hs]; exact saw_last_not_in_trunc n s⟩
  have h_inj : ∀ s₁ s₂ : SAW hexOrigin (n + 1),
      truncSAW n s₁ = b → truncSAW n s₂ = b → s₁.w = s₂.w → s₁ = s₂ :=
    fun s₁ s₂ h1 h2 hw => saw_eq_of_trunc_and_last n s₁ s₂ (h1.trans h2.symm) hw
  calc (Finset.univ.filter (fun a => truncSAW n a = b)).card
      ≤ ((hexGraph.neighborFinset b.w).filter (fun u => u ∉ b.p.1.support)).card :=
        Finset.card_le_card_of_injOn (fun s => s.w)
          (by intro s hs; exact h_map s (Finset.mem_filter.mp hs).2)
          (by intro s₁ hs₁ s₂ hs₂ hw;
              exact h_inj s₁ s₂ (Finset.mem_filter.mp hs₁).2 (Finset.mem_filter.mp hs₂).2 hw)
    _ ≤ 2 := path_extension_bound b.p.1 b.p.2 (by rw [b.l]; omega)

/-- c_1 = 3 (3 one-step SAWs from the origin). -/
lemma saw_count_one : saw_count 1 = 3 := by
  convert Fintype.card_eq_nat_card using 1
  have h_card : Nat.card (hexGraph.neighborSet hexOrigin) = 3 := by
    rw [Nat.card_eq_fintype_card]; norm_num [hexOrigin]
    exact Eq.symm (Nat.eq_of_beq_eq_true rfl)
  rw [← h_card]
  fapply Nat.card_congr
  refine' Equiv.ofBijective _ ⟨fun x y hxy => _, fun x => _⟩
  use fun x => ⟨x, ⟨.cons x.2 .nil, by aesop⟩, by rfl⟩
  all_goals generalize_proofs at *
  · grind
  · rcases x with ⟨w, ⟨p, hp⟩, hp'⟩; rcases p with (_ | ⟨_, _, p⟩) <;> aesop

/-- c_n ≤ 3 · 2^{n-1} for n ≥ 1. -/
lemma saw_count_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    (saw_count n : ℝ) ≤ 3 * 2 ^ (n - 1) := by
  suffices h : ∀ n, 1 ≤ n → saw_count n ≤ 3 * 2 ^ (n - 1) by exact_mod_cast h n hn
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [saw_count_one]
    | succ n =>
      have ih' := ih (by omega)
      have : n + 1 - 1 = n := by omega
      have : n + 1 + 1 - 1 = n + 1 := by omega
      simp_all
      calc saw_count (n + 2) ≤ 2 * saw_count (n + 1) := saw_count_step_le_mul_two _ (by omega)
        _ ≤ 2 * (3 * 2 ^ n) := by omega
        _ = 3 * 2 ^ (n + 1) := by ring

/-- μ ≥ 1 since c_n ≥ 1. -/
lemma connective_constant_ge_one : 1 ≤ connective_constant := by
  refine le_csInf ⟨_, Set.mem_image_of_mem _ (Set.mem_Ici.mpr le_rfl)⟩ ?_
  rintro x ⟨n, hn, rfl⟩
  exact Real.one_le_rpow (mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (saw_count_pos n)))
    (by positivity)

/-! ## Reduction to partition function bounds -/

private theorem main_theorem_from_partition
    (hdiv : ∀ x, xc < x → ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n))
    (hconv : ∀ x, 0 < x → x < xc → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) := by
  have h := cc_eq_inv_of_partition_radius xc_pos hdiv hconv
  rw [h, xc_inv]

/-- μ = √(2+√2) follows from Z(xc) = ∞ and Z(x) < ∞ for x < xc. -/
theorem connective_constant_eq_from_bounds
    (hdiv_xc : ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n))
    (hconv : ∀ x, 0 < x → x < xc → Summable (fun n => (saw_count n : ℝ) * x ^ n)) :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) := by
  apply main_theorem_from_partition
  · intro x hx; exact partition_diverges_mono xc_pos hx.le hdiv_xc
  · exact hconv

end