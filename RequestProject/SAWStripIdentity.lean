/-
# Z(xc) Divergence from Bridge Lower Bound

Uses bridge_sum_le_Z from SAWHWBridge to show that Z(xc) diverges,
given origin_bridge_lower_bound.
-/

import RequestProject.SAWFiniteStrip
import RequestProject.SAWHWBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-- Superseded by paper_bridge_lower_bound in SAWPaperChain.lean. -/
private theorem origin_bridge_lower_bound :
    ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ origin_bridge_partition T xc := by
  sorry

/-! ## Z(xc) diverges from bridge lower bound

The key argument: assume Z(xc) converges (for contradiction).
Then bridge_sum_le_Z gives ∑_T B_{T+1} ≤ Z(xc), so ∑ B_{T+1} converges.
But origin_bridge_lower_bound gives B_{T+1} ≥ c/(T+1),
so ∑ c/(T+1) converges, contradicting harmonic series divergence.
-/

theorem Z_xc_diverges_from_lower_bound :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := origin_bridge_lower_bound
  intro h_summable
  have h_lower : ∀ T : ℕ, c / ((T : ℝ) + 1) ≤
      origin_bridge_partition (T + 1) xc := by
    intro T; have := hc_bound (T + 1) (by omega); push_cast at this ⊢; linarith
  -- From h_summable and bridge_sum_le_Z: ∑ B_{T+1} converges
  have h_bridge_summable : Summable (fun T : ℕ =>
      origin_bridge_partition (T + 1) xc) :=
    summable_of_sum_range_le
      (fun T => tsum_nonneg fun _ => pow_nonneg xc_pos.le _)
      (fun N => bridge_sum_le_Z N xc_pos h_summable)
  exact absurd
    (Summable.of_nonneg_of_le (fun T => by positivity) h_lower h_bridge_summable)
    (not_summable_of_lower_bound hc_pos (fun n => le_refl _))

end
