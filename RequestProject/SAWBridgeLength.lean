/-
# Tight bound on PaperBridge length

PaperBridge T has length ≥ 2T-1. This is tighter than paper_bridge_length_ge (≥ T).

The proof uses the bipartite structure of hexGraph:
- Walks alternate TRUE ↔ FALSE sublattice
- Starting at TRUE (paperStart), the bridge has odd length (ending at FALSE)
- TRUE→FALSE steps decrease diagCoord by 0 or 1
- To decrease diagCoord by T, we need ≥ T such steps
- With (length+1)/2 TRUE→FALSE steps, length ≥ 2T-1
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Bipartite walk parity -/

/-- Adjacent vertices in hexGraph have different sublattice types. -/
lemma hexGraph_adj_flip_bool {v w : HexVertex} (h : hexGraph.Adj v w) :
    w.2.2 = !v.2.2 := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> simp_all

/-! ## Diagcoord decrease per TRUE→FALSE step -/

/-- TRUE→FALSE edge changes diagCoord by 0 or -1. -/
lemma true_to_false_dc_change {v w : HexVertex}
    (h : hexGraph.Adj v w) (hv : v.2.2 = true) (hw : w.2.2 = false) :
    w.1 + w.2.1 = v.1 + v.2.1 ∨ w.1 + w.2.1 = v.1 + v.2.1 - 1 := by
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-- FALSE→TRUE edge changes diagCoord by 0 or +1. -/
lemma false_to_true_dc_change {v w : HexVertex}
    (h : hexGraph.Adj v w) (hv : v.2.2 = false) (hw : w.2.2 = true) :
    w.1 + w.2.1 = v.1 + v.2.1 ∨ w.1 + w.2.1 = v.1 + v.2.1 + 1 := by
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-! ## Tight length bound -/

/-
PaperBridge has length ≥ 2T - 1.

    Proof: The walk starts at TRUE (paperStart) and ends at FALSE (diagCoord = -T).
    Steps alternate TRUE↔FALSE. TRUE→FALSE steps decrease diagCoord by 0 or 1.
    There are ⌈length/2⌉ = (length+1)/2 TRUE→FALSE steps (since length is odd
    and the first step is TRUE→FALSE). We need the total diagCoord decrease ≥ T,
    so (length+1)/2 ≥ T, giving length ≥ 2T-1.
-/
lemma paper_bridge_length_ge_tight (T : ℕ) (hT : 1 ≤ T) (b : PaperBridge T) :
    2 * T - 1 ≤ b.walk.1.length := by
  -- By induction on the walk length, we can show that the walk's length is at least 2T - 1.
  have h_ind : ∀ n : ℕ, ∀ (v : HexVertex) (w : HexVertex) (p : hexGraph.Walk v w), p.length = n → (v.2.2 = true → w.2.2 = false → n ≥ 2 * (v.1 + v.2.1 - (w.1 + w.2.1)) - 1) := by
    intro n
    induction' n using Nat.strong_induction_on with n ih;
    rintro v w p rfl hv hw;
    rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> norm_num at *;
    · have := true_to_false_dc_change ‹_› hv hw; omega;
    · rename_i k hk₁ hk₂ hk₃;
      have := hexGraph_adj_flip_bool k; have := hexGraph_adj_flip_bool hk₂; simp_all +decide ;
      have := false_to_true_dc_change k; have := false_to_true_dc_change hk₂; simp_all +decide ;
      have := true_to_false_dc_change k; have := true_to_false_dc_change hk₂; simp_all +decide ;
      grind;
  specialize h_ind _ _ _ b.walk.1 rfl;
  simp_all +decide [ paperStart ];
  linarith [ h_ind b.end_right.2, b.end_right.1 ]

end