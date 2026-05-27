/-
# Helper lemmas for the hp_sum_step proof
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWElementary
import RequestProject.SAWHWStructural
import RequestProject.SAWHWBridgeExtractProof
import RequestProject.SAWHWBound
import RequestProject.SAWHWHalfPlane
import RequestProject.SAWHWLastVertex

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Splitting hp_walk_count -/

def extra_count (W n : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW paperStart n =>
    (∀ v ∈ s.p.1.support, -(↑(W + 1) : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0) ∧
    (∃ v ∈ s.p.1.support, v.1 + v.2.1 = -(↑(W + 1) : ℤ))))

lemma hp_walk_count_split (W n : ℕ) :
    hp_walk_count (W + 1) n = hp_walk_count W n + extra_count W n := by
  unfold hp_walk_count extra_count;
  rw [ ← Finset.card_union_of_disjoint ];
  · congr with s; grind
  · simp +contextual [ Finset.disjoint_left ]; grind

lemma hp_sum_split (W N : ℕ) (x : ℝ) :
    hp_sum (W + 1) N x = hp_sum W N x +
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n := by
  simp only [hp_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by
    rw [hp_walk_count_split]; push_cast; ring

/-! ## hexOrigin neighbors in strip -/

lemma hexOrigin_only_neighbor_in_strip {w : HexVertex}
    (h : hexGraph.Adj hexOrigin w) (hw : w.1 + w.2.1 ≤ 0) :
    w = paperStart := by
  unfold hexGraph hexOrigin at *; simp at h
  rcases w with ⟨w1, w2, wb⟩
  rcases h with ⟨_, _, h3 | h3 | h3⟩ | ⟨_, _, _⟩
  all_goals simp_all [paperStart]; all_goals omega

/-! ## Walk.copy helper -/

lemma walk_copy_isPath {G : SimpleGraph V} {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (hp : p.IsPath) :
    (p.copy hu hv).IsPath := by
  subst hu; subst hv; rwa [SimpleGraph.Walk.copy_rfl_rfl]

/-! ## hex_origin_strip_count and injection -/

def hex_origin_strip_count (W m : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun s : SAW hexOrigin m =>
    ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0))

lemma hex_origin_strip_zero (W : ℕ) : hex_origin_strip_count W 0 = 1 := by
  refine' Finset.card_eq_one.mpr _
  use ⟨ hexOrigin, ⟨ SimpleGraph.Walk.nil, by
    simp +decide [ SimpleGraph.Walk.isPath_def ] ⟩, rfl ⟩
  generalize_proofs at *
  ext ⟨ w, p, l ⟩ ; simp +decide [ SAW ]
  rcases p with ⟨ _ | ⟨ _, _ ⟩, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.length ]
  unfold hexOrigin; aesop

/-- The injection: drop the first step from a strip-constrained SAW from hexOrigin. -/
def dropFirstHexSub (W m : ℕ) :
    { s : SAW hexOrigin (m + 1) //
      ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 } →
    { s : SAW paperStart m //
      ∀ v ∈ s.p.1.support, -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 } := by
  intro ⟨⟨w, ⟨p, hp⟩, hl⟩, hs⟩
  cases p with
  | nil => exfalso; simp at hl
  | cons hadj rest =>
    rename_i u
    have hu : u = paperStart :=
      hexOrigin_only_neighbor_in_strip hadj
        (hs u (List.mem_cons.mpr (Or.inr (SimpleGraph.Walk.start_mem_support rest)))).2
    subst hu
    refine ⟨⟨w, ⟨rest, ((SimpleGraph.Walk.cons_isPath_iff hadj rest).mp hp).1⟩,
      by simp at hl; omega⟩, ?_⟩
    intro v hv
    exact hs v (List.mem_cons.mpr (Or.inr hv))

/-- The injection is injective. -/
lemma dropFirstHexSub_injective (W m : ℕ) :
    Function.Injective (dropFirstHexSub W m) := by
  intro ⟨ s₁, hs₁ ⟩ ⟨ s₂, hs₂ ⟩ h_eq
  obtain ⟨w₁, ⟨p₁, hp₁⟩, hl₁⟩ := s₁
  obtain ⟨w₂, ⟨p₂, hp₂⟩, hl₂⟩ := s₂
  cases p₁ with
  | nil => simp at hl₁
  | cons hadj₁ rest₁ =>
    cases p₂ with
    | nil => simp at hl₂
    | cons hadj₂ rest₂ =>
      rename_i u₁ u₂_eq;
      have hu₁ : u₁ = paperStart := by
        apply hexOrigin_only_neighbor_in_strip hadj₁ (hs₁ u₁ (by simp)).2
      have hu₂_eq : u₂_eq = paperStart := by
        apply hexOrigin_only_neighbor_in_strip hadj₂ (hs₂ u₂_eq (by simp [SimpleGraph.Walk.support_cons])).2
      subst hu₁
      subst hu₂_eq;
      grind +locals

/-- hex_origin_strip_count(W, m) ≤ hp_walk_count(W, m-1) for m ≥ 1. -/
lemma hex_origin_strip_le_hp (W : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    hex_origin_strip_count W m ≤ hp_walk_count W (m - 1) := by
  rcases m with _ | m; · omega
  simp only [hex_origin_strip_count, hp_walk_count]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective (dropFirstHexSub W m) (dropFirstHexSub_injective W m)

/-! ## hp_sum_step -/

/-
hp_walk_count(W, 0) = 1 (the trivial walk).
-/
lemma hp_walk_count_zero (W : ℕ) : hp_walk_count W 0 = 1 := by
  convert Finset.card_eq_one.mpr _;
  use ⟨ paperStart, ⟨ .nil, by
    exact? ⟩, rfl ⟩
  generalize_proofs at *;
  ext ⟨w, ⟨p, hp⟩, hl⟩; simp [paperStart];
  rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide

/-
hp_sum(W, N, x) ≥ 1 for x ≥ 0.
-/
lemma hp_sum_ge_one (W N : ℕ) (x : ℝ) (hx : 0 ≤ x) : 1 ≤ hp_sum W N x := by
  refine' le_trans _ ( Finset.single_le_sum ( fun n _ => mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hx n ) ) ( Finset.mem_range.mpr ( Nat.succ_pos N ) ) );
  norm_num [ hp_walk_count_zero ]

/-
The key generating function bound:
    ∑_{n≤N} extra_count(W,n) · x^n ≤ 6 · B_{W+1}(x) · hp_sum(W, N, x)

    Proof outline (not yet formalized):
    1. Each extra walk decomposes at the LAST vertex at dc=-(W+1) into
       bridge prefix + suffix.
    2. Suffix starts from FALSE at dc=-(W+1), after one step goes to
       TRUE at dc=-W (2 choices), then continues in dc ∈ [-W, 0].
    3. After translate+flip, suffix → walk from hexOrigin in dc ∈ [-W, 0].
    4. Suffix GF ≤ 1 + 2x(1 + x·hp_sum(W)) ≤ (1+2x+2x²)·hp_sum(W) ≤ 6·hp_sum(W).
    5. By Cauchy product: ∑ extra(n)·x^n ≤ B_{W+1}·SuffixGF ≤ 6·B_{W+1}·hp_sum(W).
-/
private lemma extra_sum_le_placeholder (W N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    ∑ n ∈ Finset.range (N + 1), (extra_count W n : ℝ) * x ^ n ≤
    6 * paper_bridge_partition (W + 1) x * hp_sum W N x := by
  sorry

/-- **Key inductive step** (with constant 6):
    hp_sum(W+1) ≤ (1 + 6 · B_{W+1}) · hp_sum(W). -/
lemma hp_sum_step {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (W N : ℕ) :
    hp_sum (W + 1) N x ≤
    (1 + 6 * paper_bridge_partition (W + 1) x) * hp_sum W N x := by
  rw [hp_sum_split]
  have h1 := extra_sum_le_placeholder W N x hx hx1
  have h2 := hp_sum_nonneg W N x hx.le
  nlinarith

/-! ## The inductive bound (product form) -/

/-- Half-plane walk bound:
    hp_sum(W) ≤ 2 · ∏_{T=1}^W (1 + 6·B_T(x)). -/
theorem hp_sum_le_prod {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (W N : ℕ) :
    hp_sum W N x ≤
    2 * ∏ T ∈ Finset.range W, (1 + 6 * paper_bridge_partition (T + 1) x) := by
  induction W with
  | zero =>
    simp
    linarith [hp_sum_zero_le N x hx.le hx1.le]
  | succ W ih =>
    rw [Finset.prod_range_succ]
    have hB_nn : 0 ≤ paper_bridge_partition (W + 1) x :=
      tsum_nonneg fun _ => pow_nonneg hx.le _
    have hF : 0 ≤ 1 + 6 * paper_bridge_partition (W + 1) x := by linarith
    have hstep := hp_sum_step hx hx1 W N
    have h1 : hp_sum (W + 1) N x ≤ (1 + 6 * paper_bridge_partition (W + 1) x) *
        (2 * ∏ T ∈ Finset.range W, (1 + 6 * paper_bridge_partition (T + 1) x)) :=
      le_trans hstep (mul_le_mul_of_nonneg_left ih hF)
    linarith [mul_comm (∏ T ∈ Finset.range W, (1 + 6 * paper_bridge_partition (T + 1) x))
      (1 + 6 * paper_bridge_partition (W + 1) x)]

end