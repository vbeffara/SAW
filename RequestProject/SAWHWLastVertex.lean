/-
# Last Vertex Infrastructure for Hammersley-Welsh

Defines the "last vertex at dc=d" and proves properties needed
for the bridge-suffix decomposition.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWHWStructural

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Last index at a given dc value -/

/-- The maximum index k ≤ p.length such that p.getVert k has dc = d. -/
def lastDCIndex {v w : HexVertex} (p : hexGraph.Walk v w) (d : ℤ)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = d) : ℕ :=
  ((Finset.Icc 0 p.length).filter
    (fun k => decide ((p.getVert k).1 + (p.getVert k).2.1 = d))).max'
    (by obtain ⟨k, hk, hdc⟩ := h
        exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩,
          by simp [hdc]⟩⟩)

lemma lastDCIndex_le_length {v w : HexVertex} (p : hexGraph.Walk v w) (d : ℤ)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = d) :
    lastDCIndex p d h ≤ p.length := by
  exact Finset.max'_mem ( Finset.filter ( fun k => decide ( ( p.getVert k ).1 + ( p.getVert k ).2.1 = d ) ) ( Finset.Icc 0 p.length ) ) ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.zero_le _, h.choose_spec.1 ⟩, by simpa using h.choose_spec.2 ⟩ ⟩ |> fun x => Finset.mem_filter.mp x |>.1 |> fun x => Finset.mem_Icc.mp x |>.2

lemma lastDCIndex_dc {v w : HexVertex} (p : hexGraph.Walk v w) (d : ℤ)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = d) :
    (p.getVert (lastDCIndex p d h)).1 + (p.getVert (lastDCIndex p d h)).2.1 = d := by
  have := Finset.max'_mem ( Finset.filter ( fun k => decide ( ( p.getVert k ).1 + ( p.getVert k ).2.1 = d ) ) ( Finset.Icc 0 p.length ) ) ?_;
  convert this using 1;
  all_goals norm_num [ lastDCIndex ];
  exact fun _ y hy _ => hy;
  exact ⟨ h.choose, Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.zero_le _, h.choose_spec.1 ⟩, h.choose_spec.2 ⟩ ⟩

lemma lastDCIndex_is_max {v w : HexVertex} (p : hexGraph.Walk v w) (d : ℤ)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = d)
    (j : ℕ) (hj : j ≤ p.length) (hj_dc : (p.getVert j).1 + (p.getVert j).2.1 = d) :
    j ≤ lastDCIndex p d h := by
  exact Finset.le_max' ( Finset.filter ( fun k => decide ( ( p.getVert k ).1 + ( p.getVert k ).2.1 = d ) ) ( Finset.Icc 0 p.length ) ) j ( Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by simpa using hj_dc ⟩ )

/-
After the last dc=d vertex, no subsequent vertex has dc=d.
-/
lemma after_lastDCIndex_no_dc {v w : HexVertex} (p : hexGraph.Walk v w) (d : ℤ)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = d)
    (j : ℕ) (hj : j ≤ p.length) (hj_gt : lastDCIndex p d h < j) :
    (p.getVert j).1 + (p.getVert j).2.1 ≠ d := by
  exact fun h' => hj_gt.not_ge <| lastDCIndex_is_max p d h j hj h'

/-! ## The last vertex at dc=-(W+1) is FALSE -/

/-
In a SAW from paperStart staying in dc ∈ [-(W+1), 0],
    the last vertex at dc=-(W+1) is FALSE.

    Proof: if z (= getVert i at dc=-(W+1)) were TRUE, then getVert(i+1)
    is FALSE at dc ≤ -(W+1) (by dc_step_from_true), hence dc = -(W+1)
    (by strip). But i+1 > i and getVert(i+1) also has dc=-(W+1),
    contradicting that i is the maximum index.
-/
lemma lastDCIndex_is_false
    {w : HexVertex}
    (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (W : ℕ) (hW : 0 < W)
    (hstrip : ∀ u ∈ p.support, -(↑(W + 1) : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = -(↑(W + 1) : ℤ))
    (h_not_last : lastDCIndex p (-(↑(W + 1) : ℤ)) h < p.length) :
    (p.getVert (lastDCIndex p (-(↑(W + 1) : ℤ)) h)).2.2 = false := by
  -- Assume for contradiction that the last vertex at dc=-(W+1) is TRUE.
  by_contra h_contra
  have h_false : (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).2.2 = false := by
    have h_false : hexGraph.Adj (p.getVert (lastDCIndex p (-↑(W + 1)) h)) (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)) := by
      exact?
    generalize_proofs at *; (
    have := hex_adj_flip_bool h_false; aesop;)
  have h_false_dc : (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).1 + (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).2.1 = -(W + 1) := by
    have h_false_dc : (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).1 + (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).2.1 ≤ -(W + 1) := by
      have h_false_dc : hexGraph.Adj (p.getVert (lastDCIndex p (-↑(W + 1)) h)) (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)) := by
        exact?;
      convert dc_step_from_true h_false_dc _ using 1;
      · convert lastDCIndex_dc p ( -↑ ( W + 1 ) ) h |> Eq.symm using 1;
      · grind;
    have h_false_dc : (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).1 + (p.getVert (lastDCIndex p (-↑(W + 1)) h + 1)).2.1 ≥ -(W + 1) := by
      exact hstrip _ ( by simp ) |>.1.trans' ( by norm_num ) ;
    linarith [h_false_dc]
  exact (by
  exact absurd ( after_lastDCIndex_no_dc p ( -↑ ( W + 1 ) ) h ( lastDCIndex p ( -↑ ( W + 1 ) ) h + 1 ) ( by linarith ) ( by linarith ) ) ( by aesop ))

/-! ## Suffix after last dc vertex stays in [-W, 0] -/

/-
After the last vertex at dc=-(W+1), all subsequent vertices
    in the walk have dc ∈ [-W, 0].
-/
lemma suffix_after_last_narrow {w : HexVertex}
    (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (W : ℕ) (hW : 0 < W)
    (hstrip : ∀ u ∈ p.support, -(↑(W + 1) : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0)
    (h : ∃ k, k ≤ p.length ∧ (p.getVert k).1 + (p.getVert k).2.1 = -(↑(W + 1) : ℤ))
    (j : ℕ) (hj : j ≤ p.length) (hj_gt : lastDCIndex p (-(↑(W + 1) : ℤ)) h < j) :
    -(W : ℤ) ≤ (p.getVert j).1 + (p.getVert j).2.1 ∧
    (p.getVert j).1 + (p.getVert j).2.1 ≤ 0 := by
  grind +suggestions

end