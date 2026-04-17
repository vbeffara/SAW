/-
# Cutting argument for the bridge recurrence

The cutting argument from Section 3 of Duminil-Copin & Smirnov (2012):
A walk from the left boundary of S_{T+1} to the left boundary
that reaches the right boundary of S_{T+1} (but not of S_T)
can be cut at the first point reaching the right boundary,
giving two bridges of width T+1.

This gives: A_{T+1} - A_T ≤ xc · B_{T+1}²

Combined with the strip identity 1 = c_α·A_T + B_T + c_ε·E_T:
B_T ≤ c_α·xc · B_{T+1}² + B_{T+1}

This is the quadratic recurrence.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWWalkHelpers

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Strip monotonicity -/

/-- PaperInfStrip is monotone in T: wider strip contains narrower strip. -/
lemma PaperInfStrip_mono {T : ℕ} {v : HexVertex} (hv : PaperInfStrip T v) :
    PaperInfStrip (T + 1) v := by
  unfold PaperInfStrip at *; cases hb : v.2.2 <;> simp_all <;> omega

/-! ## Infinite strip walks -/

/-- A walk from paperStart to a LEFT boundary vertex (TRUE, diagCoord = 0)
    that is NOT paperStart, staying in PaperInfStrip T. -/
structure PaperSAW_A_inf (T : ℕ) where
  end_v : HexVertex
  walk : hexGraph.Path paperStart end_v
  end_left : end_v.1 + end_v.2.1 = 0 ∧ end_v.2.2 = true ∧ end_v ≠ paperStart
  in_strip : ∀ v ∈ walk.1.support, PaperInfStrip T v

/-- Partition function for walks to the left boundary in the infinite strip. -/
def A_inf (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : PaperSAW_A_inf T), x ^ (s.walk.1.length + 1)

/-- The walks in PaperSAW_A_inf T embed into PaperSAW_A_inf (T+1). -/
def PaperSAW_A_inf_widen {T : ℕ} (s : PaperSAW_A_inf T) : PaperSAW_A_inf (T + 1) where
  end_v := s.end_v
  walk := s.walk
  end_left := s.end_left
  in_strip := fun v hv => PaperInfStrip_mono (s.in_strip v hv)

/-- The widening injection preserves walk length. -/
lemma PaperSAW_A_inf_widen_length {T : ℕ} (s : PaperSAW_A_inf T) :
    (PaperSAW_A_inf_widen s).walk.1.length = s.walk.1.length := rfl

/-- The widening map is injective. -/
lemma PaperSAW_A_inf_widen_injective (T : ℕ) :
    Function.Injective (@PaperSAW_A_inf_widen T) := by
  intro s₁ s₂ h
  unfold PaperSAW_A_inf_widen at h
  cases s₁; cases s₂; simp at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

/-- A_inf is non-negative. -/
lemma A_inf_nonneg (T : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_inf T x :=
  tsum_nonneg fun s => pow_nonneg hx _

/-! ## Cutting argument: walks reaching the boundary -/

/-
A walk in A_inf (T+1) that is NOT in A_inf T must reach diagCoord -(T+1).

    A vertex v in PaperInfStrip(T+1) but not PaperInfStrip T satisfies:
    - FALSE: v.1+v.2.1 = -(T+1) [directly gives the result]
    - TRUE: v.1+v.2.1 = -T [use true_at_boundary_has_lower_false]
-/
lemma A_inf_diff_reaches_boundary {T : ℕ} (hT : 0 < T)
    (s : PaperSAW_A_inf (T + 1))
    (h_not_in_T : ¬ ∀ v ∈ s.walk.1.support, PaperInfStrip T v) :
    ∃ v ∈ s.walk.1.support, v.1 + v.2.1 = -(T + 1 : ℤ) ∧ v.2.2 = false := by
  simp +zetaDelta at *;
  contrapose! h_not_in_T;
  intro x y; constructor <;> intro h <;> have := s.in_strip _ h <;> simp_all +decide [ PaperInfStrip ] ;
  · grind;
  · by_cases hxy : x + y = -T;
    · have := true_at_boundary_has_lower_false s.walk.1 s.walk.2 s.end_left x y hxy h hT; aesop;
    · omega

/-- Cutting a walk at the first vertex with diagCoord -(T+1)
    gives two bridges of width T+1.

    A_{T+1} - A_T ≤ xc · B_{T+1}² -/
lemma cutting_argument (T : ℕ) (hT : 1 ≤ T) :
    A_inf (T + 1) xc - A_inf T xc ≤
    xc * paper_bridge_partition (T + 1) xc ^ 2 := by
  sorry

/-! ## The recurrence from strip identity + cutting

The quadratic recurrence follows from:
1. Strip identity: 1 = c_α · A_inf T xc + paper_bridge_partition T xc + c_ε · E_inf T xc
2. A_{T+1} - A_T ≤ xc · B_{T+1}² (cutting argument)
3. E_{T+1} ≤ E_T (monotonicity of escape partition function)

Subtracting strip identity at T and T+1:
  B_T - B_{T+1} ≤ c_α · (A_{T+1} - A_T) ≤ c_α · xc · B_{T+1}²
Therefore: B_T ≤ c_α · xc · B_{T+1}² + B_{T+1}
So α = c_alpha * xc.
-/

/-
The recurrence: B_T ≤ α · B_{T+1}² + B_{T+1} where α = c_alpha * xc.
    Proved from the strip identity + cutting argument.
-/
theorem bridge_recurrence_from_cutting
    (h_cut : ∀ T : ℕ, 1 ≤ T →
      A_inf (T + 1) xc - A_inf T xc ≤ xc * paper_bridge_partition (T + 1) xc ^ 2)
    (h_strip : ∀ T : ℕ, 1 ≤ T →
      ∃ A E : ℝ, A = A_inf T xc ∧
        1 = c_alpha * A + paper_bridge_partition T xc + c_eps * E ∧
        0 ≤ E)
    (h_E_mono : ∀ T : ℕ, 1 ≤ T →
      ∀ E₁ E₂ : ℝ,
        (1 = c_alpha * A_inf T xc + paper_bridge_partition T xc + c_eps * E₁) →
        (1 = c_alpha * A_inf (T+1) xc + paper_bridge_partition (T+1) xc + c_eps * E₂) →
        E₂ ≤ E₁) :
    ∃ α > 0, ∀ T : ℕ, 1 ≤ T →
      paper_bridge_partition T xc ≤ α * paper_bridge_partition (T + 1) xc ^ 2 +
        paper_bridge_partition (T + 1) xc := by
  use c_alpha * xc, mul_pos (by
  exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩) (by
  exact?), by
    simp +zetaDelta at *;
    intros T hT
    obtain ⟨E₁, hE₁⟩ := h_strip T hT
    obtain ⟨E₂, hE₂⟩ := h_strip (T + 1) (by linarith)
    have h_recurrence : paper_bridge_partition T xc - paper_bridge_partition (T + 1) xc ≤ c_alpha * (A_inf (T + 1) xc - A_inf T xc) := by
      nlinarith [ h_E_mono T hT E₁ E₂ hE₁.1 hE₂.1, show 0 < c_eps by exact c_eps_pos ]
    have h_recurrence' : paper_bridge_partition T xc ≤ c_alpha * xc * paper_bridge_partition (T + 1) xc ^ 2 + paper_bridge_partition (T + 1) xc := by
      nlinarith [ h_cut T hT, show 0 < c_alpha by exact c_alpha_pos ]
    exact h_recurrence'

end