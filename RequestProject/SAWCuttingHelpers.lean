/-
# Cutting argument helper lemmas

Infrastructure for cutting a walk at the first vertex reaching the strip boundary,
producing two bridges whose weight product bounds the original walk's weight.
-/

import Mathlib
import RequestProject.SAWCutting
import RequestProject.SAWHWAlgorithm

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Shifted walk preserves PaperInfStrip -/

/-- Shifting by (dx, dy) with dx + dy = 0 preserves PaperInfStrip.
    PaperInfStrip only depends on v.1+v.2.1 (diagCoord) and v.2.2 (sublattice).
    hexShift preserves v.2.2 and changes diagCoord by dx+dy = 0. -/
lemma hexShift_preserves_strip {T : ℕ} {dx dy : ℤ} (hsum : dx + dy = 0)
    {v : HexVertex} (hv : PaperInfStrip T v) :
    PaperInfStrip T (hexShift dx dy v) := by
  unfold PaperInfStrip at *; unfold hexShift
  cases hb : v.2.2 <;> simp_all <;> constructor <;> omega

/-! ## Prefix of an A_inf walk gives a PaperBridge -/

/-- The prefix of a walk (from paperStart to a vertex v with diagCoord -(T+1),
    v.2.2 = false) gives a PaperBridge (T+1). -/
lemma prefix_gives_bridge {T : ℕ}
    {w : HexVertex} (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (v : HexVertex) (hv : v ∈ p.support)
    (hv_diag : v.1 + v.2.1 = -(T + 1 : ℤ)) (hv_false : v.2.2 = false)
    (h_strip : ∀ u ∈ p.support, PaperInfStrip (T + 1) u) :
    ∃ b : PaperBridge (T + 1),
      b.walk.1.length = (p.takeUntil v hv).length := by
  exact ⟨⟨v, ⟨p.takeUntil v hv, hp.takeUntil hv⟩,
    ⟨by omega, hv_false⟩,
    fun u hu => h_strip u (p.support_takeUntil_subset hv hu)⟩, rfl⟩

/-! ## Suffix reversed and shifted gives a PaperBridge -/

/-- For a walk ending at end_v (TRUE, diagCoord 0), the shift
    (-end_v.1, -end_v.2.1) sends end_v to paperStart. -/
lemma shift_endpoint_to_paperStart {end_v : HexVertex}
    (h_diag : end_v.1 + end_v.2.1 = 0) (h_true : end_v.2.2 = true) :
    hexShift (-end_v.1) (-end_v.2.1) end_v = paperStart := by
  unfold hexShift paperStart; ext <;> simp <;> omega

/-- The shift (-end_v.1, -end_v.2.1) has coordinate sum 0
    when end_v has diagCoord 0. -/
lemma shift_sum_zero {end_v : HexVertex} (h_diag : end_v.1 + end_v.2.1 = 0) :
    (-end_v.1) + (-end_v.2.1) = 0 := by omega

/-
Constructing a PaperBridge from the reversed shifted suffix.
-/
lemma suffix_reversed_shifted_gives_bridge {T : ℕ}
    (end_v v : HexVertex)
    (h_end_diag : end_v.1 + end_v.2.1 = 0) (h_end_true : end_v.2.2 = true)
    (hv_diag : v.1 + v.2.1 = -(T + 1 : ℤ)) (hv_false : v.2.2 = false)
    (q : hexGraph.Walk v end_v) (hq : q.IsPath)
    (h_strip : ∀ u ∈ q.support, PaperInfStrip (T + 1) u) :
    ∃ b : PaperBridge (T + 1),
      b.walk.1.length = q.length := by
  revert q;
  intro q hq h_strip
  set dx := -end_v.1
  set dy := -end_v.2.1
  set shifted_v := hexShift dx dy v
  set q_rev := q.reverse
  set q_shifted := shiftWalk dx dy q_rev;
  -- Use `cast` or `subst` with the equality hexShift dx dy end_v = paperStart to fix the walk's starting vertex type.
  have h_cast : hexShift dx dy end_v = paperStart := by
    exact?
  generalize_proofs at *;
  refine' ⟨ ⟨ shifted_v, ⟨ _, _ ⟩, _, _ ⟩, _ ⟩;
  exact h_cast ▸ q_shifted
  all_goals generalize_proofs at *;
  · convert shiftWalk_isPath dx dy q_rev ( hq.reverse ) using 1
    generalize_proofs at *;
    · exact h_cast.symm;
    · grind +splitImp;
  · simp +zetaDelta at *;
    exact ⟨ by linarith! [ show ( hexShift ( -end_v.1 ) ( -end_v.2.1 ) v ).2.1 = v.2.1 + ( -end_v.2.1 ) from rfl ], by rw [ show ( hexShift ( -end_v.1 ) ( -end_v.2.1 ) v ).2.2 = v.2.2 from rfl ] ; exact hv_false ⟩;
  · intro u hu
    have hu' : ∃ u' ∈ q.support, u = hexShift dx dy u' := by
      have hu' : u ∈ q_shifted.support := by
        grind
      generalize_proofs at *;
      have hu' : u ∈ q_rev.support.map (hexShift dx dy) := by
        exact shiftWalk_support dx dy q_rev ▸ hu'
      generalize_proofs at *;
      rw [ List.mem_map ] at hu' ; obtain ⟨ u', hu', rfl ⟩ := hu' ; use u' ; aesop;
    generalize_proofs at *;
    obtain ⟨u', hu', rfl⟩ := hu'
    exact hexShift_preserves_strip (by
    grind +extAll) (h_strip u' hu');
  · convert shiftWalk_length dx dy q_rev using 1;
    · grind +splitIndPred;
    · rw [ SimpleGraph.Walk.length_reverse ]

/-! ## Walk length decomposition -/

/-- When a walk is split at a vertex, the lengths add up. -/
lemma walk_split_lengths {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    (p.takeUntil u hu).length + (p.dropUntil u hu).length = p.length := by
  have h := SimpleGraph.Walk.take_spec p hu
  conv_rhs => rw [← h]
  exact (SimpleGraph.Walk.length_append _ _).symm

end