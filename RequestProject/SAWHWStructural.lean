/-
# Structural Lemmas for the Hammersley-Welsh Bridge Decomposition
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## DiagCoord step structure on hex lattice -/

/-- From a TRUE vertex, the next (FALSE) vertex has dc ≤ dc_current. -/
lemma dc_step_from_true {v w : HexVertex} (h : hexGraph.Adj v w) (hv : v.2.2 = true) :
    w.1 + w.2.1 ≤ v.1 + v.2.1 := by
  rcases h with ⟨hf, ht, h3 | h3 | h3⟩ | ⟨hf, ht, h3 | h3 | h3⟩ <;> simp_all <;> omega

/-- From a FALSE vertex, the next (TRUE) vertex has dc ≥ dc_current. -/
lemma dc_step_from_false {v w : HexVertex} (h : hexGraph.Adj v w) (hv : v.2.2 = false) :
    w.1 + w.2.1 ≥ v.1 + v.2.1 := by
  rcases h with ⟨hf, ht, h3 | h3 | h3⟩ | ⟨hf, ht, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-- Adjacent vertices on hexGraph have opposite Bool values (bipartite). -/
lemma hex_adj_flip_bool {v w : HexVertex} (h : hexGraph.Adj v w) :
    v.2.2 = !w.2.2 := by
  rcases h with ⟨hf, ht, _⟩ | ⟨hf, ht, _⟩ <;> simp_all

/-- The only FALSE neighbor of TRUE(a,b) within dc ≥ a+b is FALSE(a,b). -/
lemma true_only_false_neighbor_at_dc {a b : ℤ} {w : HexVertex}
    (h : hexGraph.Adj (a, b, true) w) (hdc : w.1 + w.2.1 ≥ a + b) :
    w = (a, b, false) := by
  cases h; aesop; grind

/-! ## PaperInfStrip compatibility -/

/-
A non-endpoint vertex in a path has both a predecessor and a successor.
-/
lemma path_interior_has_neighbors {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (u : HexVertex) (hu : u ∈ p.support)
    (hu_ne_v : u ≠ v) (hu_ne_w : u ≠ w) :
    ∃ a b : HexVertex, a ∈ p.support ∧ b ∈ p.support ∧
      hexGraph.Adj a u ∧ hexGraph.Adj u b ∧ a ≠ b := by
  -- Since u is not the start or end, there exist indices i and j such that p.getVert i = u and p.getVert j = u with i < j.
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i < p.length ∧ p.getVert i = u := by
    have h_support : u ∈ p.support → ∃ i : ℕ, i < p.length ∧ p.getVert i = u := by
      intro hu
      have h_support : u ∈ p.support → ∃ i : ℕ, i ≤ p.length ∧ p.getVert i = u := by
        rw [ SimpleGraph.Walk.mem_support_iff_exists_getVert ] at hu ; aesop;
      obtain ⟨ i, hi₁, hi₂ ⟩ := h_support hu; use i; cases lt_or_eq_of_le hi₁ <;> simp_all +decide [ SimpleGraph.Walk.getVert ] ;
    exact h_support hu;
  refine' ⟨ p.getVert ( i - 1 ), p.getVert ( i + 1 ), _, _, _, _, _ ⟩ <;> rcases i with ( _ | i ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
  · grind +suggestions;
  · convert p.adj_getVert_succ _ using 1;
    · exact hi.2.symm;
    · lia;
  · have := hp.getVert_injOn;
    exact fun h => by have := this ( show i ≤ p.length from by linarith ) ( show i + 1 + 1 ≤ p.length from by linarith ) h; linarith;

/-
In a SAW staying in dc ∈ [-T, 0] (T ≥ 1) starting from dc > -T,
    all non-endpoint TRUE vertices have dc > -T.
-/
lemma no_true_at_min_dc_in_strip {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (T : ℕ) (hT : 1 ≤ T)
    (hv_dc : v.1 + v.2.1 > -(T : ℤ))
    (hstrip : ∀ u ∈ p.support, -(T : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (u : HexVertex) (hu : u ∈ p.support) (hu_true : u.2.2 = true)
    (hu_not_last : u ≠ w) :
    u.1 + u.2.1 > -(T : ℤ) := by
  -- By contradiction. Assume u.1 + u.2.1 ≤ -(T : ℤ). Combined with hstrip, u.1 + u.2.1 = -T.
  by_contra h_contra;
  -- By path_interior_has_neighbors, there exist predecessors/successors a₀, b₀ in p.support with hexGraph.Adj a₀ u and hexGraph.Adj u b₀ and a₀ ≠ b₀.
  obtain ⟨a₀, b₀, ha₀, hb₀, hab⟩ : ∃ a₀ b₀ : HexVertex, a₀ ∈ p.support ∧ b₀ ∈ p.support ∧ hexGraph.Adj a₀ u ∧ hexGraph.Adj u b₀ ∧ a₀ ≠ b₀ := by
    apply path_interior_has_neighbors p hp u hu;
    · grind;
    · assumption;
  -- By true_only_false_neighbor_at_dc, we get a₀ = (a,b,false) and b₀ = (a,b,false).
  have ha₀_false : a₀ = (u.1, u.2.1, false) := by
    apply true_only_false_neighbor_at_dc;
    · convert hab.1.symm using 1;
      grind;
    · linarith [ hstrip a₀ ha₀, hstrip u hu ]
  have hb₀_false : b₀ = (u.1, u.2.1, false) := by
    apply true_only_false_neighbor_at_dc;
    · grind +splitIndPred;
    · grind;
  grind

/-
In a SAW from TRUE at dc 0 staying in dc ∈ [-T, 0] (T ≥ 1),
    all non-endpoint FALSE vertices have dc < 0.
-/
lemma no_false_at_zero_dc {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath)
    (T : ℕ) (hT : 1 ≤ T)
    (hv_true : v.2.2 = true) (hv_dc : v.1 + v.2.1 = 0)
    (hstrip : ∀ u ∈ p.support, -(T : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (u : HexVertex) (hu : u ∈ p.support) (hu_false : u.2.2 = false)
    (hu_not_last : u ≠ w) :
    u.1 + u.2.1 < 0 := by
  by_contra h_contra
  have h_contra_eq : u.1 + u.2.1 = 0 := by linarith [hstrip u hu]
  have h_neighbors : ∀ w, hexGraph.Adj u w → w.1 + w.2.1 ≤ 0 → w = (u.1, u.2.1, true) := by
    intros w hw hw_le_zero
    have h_neighbor : w = (u.1, u.2.1, true) ∨ w = (u.1 + 1, u.2.1, true) ∨ w = (u.1, u.2.1 + 1, true) := by
      unfold hexGraph at hw; simp_all +decide [Prod.ext_iff]; grind
    grind
  have h_predecessor : ∀ w, hexGraph.Adj w u → w ∈ p.support → w = (u.1, u.2.1, true) := by
    intros w hw hw_support
    have h_predecessor_step : w.1 + w.2.1 ≤ 0 := by exact hstrip _ hw_support |>.2
    exact h_neighbors _ (by simpa [hex_adj_flip_bool hw] using hw.symm) h_predecessor_step
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, hexGraph.Adj u w₁ ∧ w₁ ∈ p.support := by
    have h_successor : ∃ w₁, hexGraph.Adj u w₁ ∧ w₁ ∈ p.support := by
      have h_support : u ∈ p.support := hu
      have h_not_last : u ≠ w := hu_not_last
      have h_walk : ∃ i, p.getVert i = u ∧ i < p.length := by
        rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at h_support
        obtain ⟨n, hn₁, hn₂⟩ := h_support
        exact ⟨n, hn₁, lt_of_le_of_ne hn₂ fun h => h_not_last <| by rw [← hn₁, h]; exact p.getVert_length⟩
      obtain ⟨i, hi, hi'⟩ := h_walk
      use p.getVert (i + 1)
      exact ⟨by rw [← hi]; exact p.adj_getVert_succ (by linarith), by exact p.getVert_mem_support _⟩
    exact h_successor
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, hexGraph.Adj w₂ u ∧ w₂ ∈ p.support := by
    exact ⟨ w₁, by simpa [ hex_adj_flip_bool ] using hw₁.1.symm, hw₁.2 ⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : HexVertex, hexGraph.Adj u w₁ ∧ w₁ ∈ p.support ∧ w₁ = (u.1, u.2.1, true) := by
    grind
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : HexVertex, hexGraph.Adj w₂ u ∧ w₂ ∈ p.support ∧ w₂ = (u.1, u.2.1, true) := by
    exact ⟨ w₂, hw₂.1, hw₂.2, h_predecessor w₂ hw₂.1 hw₂.2 ⟩;
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : HexVertex, hexGraph.Adj u w₁ ∧ w₁ ∈ p.support ∧ w₁ ≠ (u.1, u.2.1, true) := by
    have h_neighbors : ∃ a b : HexVertex, a ∈ p.support ∧ b ∈ p.support ∧ hexGraph.Adj a u ∧ hexGraph.Adj u b ∧ a ≠ b := by
      apply path_interior_has_neighbors p hp u hu;
      · grind;
      · exact hu_not_last;
    grind +qlia;
  exact hw₁.2.2 ( h_neighbors w₁ hw₁.1 ( by linarith [ hstrip w₁ hw₁.2.1 ] ) )

/-- The key PaperInfStrip compatibility: any SAW from paperStart to a FALSE
    vertex at dc -T, staying in dc ∈ [-T, 0], satisfies PaperInfStrip T. -/
theorem bridge_satisfies_paper_inf_strip
    (T : ℕ) (hT : 1 ≤ T) {w : HexVertex}
    (p : hexGraph.Path paperStart w)
    (hw_false : w.2.2 = false)
    (hw_dc : w.1 + w.2.1 = -(T : ℤ))
    (hstrip : ∀ u ∈ p.1.support, -(T : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) :
    ∀ u ∈ p.1.support, PaperInfStrip T u := by
  intro u hu
  have ⟨hlo, hhi⟩ := hstrip u hu
  unfold PaperInfStrip
  cases hu_b : u.2.2
  · -- FALSE case: need -T ≤ dc ≤ -1
    simp
    refine ⟨hlo, ?_⟩
    by_cases heq : u = w
    · subst heq; omega
    · have h := no_false_at_zero_dc p.1 p.2 T hT
        (by decide) (by simp [paperStart]) hstrip u hu hu_b heq
      omega
  · -- TRUE case: need -(T-1) ≤ dc ≤ 0
    simp
    refine ⟨?_, hhi⟩
    by_cases heq : u = w
    · subst heq; simp_all
    · have h := no_true_at_min_dc_in_strip p.1 p.2 T hT
        (by simp [paperStart]; omega) hstrip u hu hu_b heq
      omega

end