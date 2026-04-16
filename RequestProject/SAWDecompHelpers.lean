/-
# Helper lemmas for the Hammersley-Welsh bridge decomposition

Key infrastructure for decomposing SAWs into bridges.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Diagonal coordinate properties -/

/-- The diagonal coordinate of a vertex. -/
abbrev diagCoord' (v : HexVertex) : ℤ := v.1 + v.2.1

/-- Each hex edge changes diagCoord by 0 or ±1. -/
lemma diagCoord_adj_bound' {v w : HexVertex} (h : hexGraph.Adj v w) :
    diagCoord' w - diagCoord' v ∈ ({-1, 0, 1} : Set ℤ) := by
  unfold hexGraph at h
  rcases h with ⟨_, _, h3 | h3 | h3⟩ | ⟨_, _, h3 | h3 | h3⟩ <;>
    simp_all [diagCoord'] <;> omega

/-- diagCoord of paperStart is 0. -/
@[simp] lemma diagCoord'_paperStart : diagCoord' paperStart = 0 := by
  simp [diagCoord', paperStart]

/-! ## Key combinatorial identity -/

/-- The powerset product identity: ∏ (1 + f(i)) = ∑_{S ⊆ range n} ∏_{i ∈ S} f(i). -/
lemma powerset_prod_eq' {n : ℕ} (f : ℕ → ℝ) :
    ∏ i ∈ Finset.range n, (1 + f i) =
    ∑ S ∈ (Finset.range n).powerset, ∏ i ∈ S, f i := by
  rw [Finset.prod_one_add]

/-! ## Weight bound for decomposition -/

/-- For 0 ≤ x ≤ 1, x^n ≤ x^m when n ≥ m. -/
lemma pow_le_pow_of_le_one_ge {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n m : ℕ} (hnm : m ≤ n) : x ^ n ≤ x ^ m :=
  pow_le_pow_of_le_one hx hx1 hnm

/-! ## SAW path splitting -/

/-- Splitting a path at a vertex gives two walks whose lengths sum correctly. -/
lemma path_split_length {v w u : HexVertex} (p : hexGraph.Path v w)
    (hu : u ∈ p.1.support) :
    (p.1.takeUntil u hu).length + (p.1.dropUntil u hu).length = p.1.length := by
  rw [← SimpleGraph.Walk.length_append, p.1.take_spec hu]

/-- The takeUntil walk stays within the support of the original walk. -/
lemma takeUntil_support_subset' {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hu : u ∈ p.support) :
    ∀ a ∈ (p.takeUntil u hu).support, a ∈ p.support :=
  fun _ hz => SimpleGraph.Walk.support_takeUntil_subset p hu hz

/-- The dropUntil walk stays within the support of the original walk. -/
lemma dropUntil_support_subset' {v w u : HexVertex} (p : hexGraph.Walk v w)
    (hu : u ∈ p.support) :
    ∀ a ∈ (p.dropUntil u hu).support, a ∈ p.support :=
  fun _ hz => SimpleGraph.Walk.support_dropUntil_subset p hu hz

/-! ## Translation shifts diagCoord -/

/-- Translation shifts diagCoord by dx + dy. -/
lemma hexTranslate_diagCoord' (dx dy : ℤ) (v : HexVertex) :
    diagCoord' (hexTranslate dx dy v) = diagCoord' v + (dx + dy) := by
  simp [hexTranslate, diagCoord']
  ring

end
