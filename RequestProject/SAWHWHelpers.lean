/-
# Helper lemmas for the Hammersley-Welsh bridge decomposition
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## diagCoord helpers -/

abbrev dc (v : HexVertex) : ℤ := v.1 + v.2.1

@[simp] lemma dc_paperStart : dc paperStart = 0 := by
  simp [dc, paperStart]

lemma dc_adj_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    |dc w - dc v| ≤ 1 := by
  have := hexGraph_adj_sum_bound h
  unfold dc
  exact abs_le.mpr ⟨by omega, by omega⟩

/-! ## SAW from paperStart: diagCoord bounds -/

/-- In a SAW from paperStart, every vertex has dc ≥ -n. -/
lemma saw_dc_lower {n : ℕ} (s : SAW paperStart n) (u : HexVertex)
    (hu : u ∈ s.p.1.support) : -(n : ℤ) ≤ dc u := by
  have h := hexGraph_walk_sum_bound_neg (s.p.1.takeUntil u hu)
  have hlen := s.p.1.length_takeUntil_le hu
  simp [dc, paperStart] at h ⊢
  linarith [s.l]

/-- In a SAW from paperStart, every vertex has dc ≤ n. -/
lemma saw_dc_upper {n : ℕ} (s : SAW paperStart n) (u : HexVertex)
    (hu : u ∈ s.p.1.support) : dc u ≤ n := by
  have h := hexGraph_walk_sum_bound_pos (s.p.1.takeUntil u hu)
  have hlen := s.p.1.length_takeUntil_le hu
  simp [dc, paperStart] at h ⊢
  linarith [s.l]

/-! ## Splitting a SAW at a vertex -/

/-- After splitting a SAW at a vertex, both parts are paths. -/
lemma saw_split_paths {n : ℕ} (s : SAW paperStart n) (u : HexVertex)
    (hu : u ∈ s.p.1.support) :
    (s.p.1.takeUntil u hu).IsPath ∧ (s.p.1.dropUntil u hu).IsPath :=
  ⟨s.p.2.takeUntil hu, s.p.2.dropUntil hu⟩

/-- Splitting preserves total length. -/
lemma saw_split_length {n : ℕ} (s : SAW paperStart n) (u : HexVertex)
    (hu : u ∈ s.p.1.support) :
    (s.p.1.takeUntil u hu).length + (s.p.1.dropUntil u hu).length = n := by
  have h1 := s.p.1.take_spec hu
  conv_rhs => rw [← s.l]
  rw [← SimpleGraph.Walk.length_append, h1]

/-! ## Weight monotonicity -/



/-! ## Paper bridge to SAW injection -/

/-- A paper bridge of width T gives a SAW from paperStart. -/
def paperBridgeToSAW' {T : ℕ} (b : PaperBridge T) :
    SAW paperStart b.walk.1.length :=
  ⟨b.end_v, b.walk, rfl⟩

/-
Injection from paper bridges to (length, SAW) is injective.
-/
lemma paperBridgeToSAW_sigma_inj' (T : ℕ) :
    Function.Injective (fun b : PaperBridge T =>
      (⟨b.walk.1.length, paperBridgeToSAW' b⟩ : Σ n, SAW paperStart n)) := by
  intro b₁ b₂ h;
  cases b₁ ; cases b₂ ; simp_all +decide [ paperBridgeToSAW' ];
  grind

/-! ## Bridge from a SAW prefix -/

/-- Construct a paper bridge from a SAW prefix. -/
def sawPrefixBridge {n : ℕ} (s : SAW paperStart n) (u : HexVertex)
    (hu : u ∈ s.p.1.support) (T : ℕ)
    (hdc : dc u = -(T : ℤ))
    (hfalse : u.2.2 = false)
    (hstrip : ∀ w ∈ (s.p.1.takeUntil u hu).support, PaperInfStrip T w) :
    PaperBridge T where
  end_v := u
  walk := ⟨s.p.1.takeUntil u hu, s.p.2.takeUntil hu⟩
  end_right := ⟨by unfold dc at hdc; exact hdc, hfalse⟩
  in_strip := hstrip

end