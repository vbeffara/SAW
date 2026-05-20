/-
# Bridge Extraction from SAWs

Key structural lemma: Given a SAW from paperStart that visits dc = -W,
the prefix to the first vertex at dc = -W is a valid PaperBridge of width W.
-/

import Mathlib
import RequestProject.SAWHWStructural
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## First vertex at dc = -W is FALSE -/

/-
The first vertex reaching dc = -W in a walk from paperStart
    (all dc ∈ [-W, 0]) is FALSE.

    Proof: paperStart is TRUE at dc=0. The walk alternates TRUE↔FALSE.
    dc can only decrease at TRUE→FALSE steps (dc_step_from_true).
    dc can only increase at FALSE→TRUE steps (dc_step_from_false).
    So the first time dc reaches -W, it must happen at a TRUE→FALSE step,
    meaning the vertex at dc=-W is FALSE.
-/
lemma first_min_dc_is_false {w : HexVertex}
    (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    {W : ℕ} (hW : 1 ≤ W)
    (v : HexVertex) (hv : v ∈ p.support)
    (hv_dc : v.1 + v.2.1 = -(W : ℤ))
    (hprev_above : ∀ u ∈ (p.takeUntil v hv).support,
      u ≠ v → u.1 + u.2.1 > -(W : ℤ)) :
    v.2.2 = false := by
  cases inst : v.2.2 ; simp_all +decide;
  -- Since $v$ is in the support of $p$ and $v \neq paperStart$, there exists a predecessor $u$ in the walk such that $hexGraph.Adj u v$ and $u \in (p.takeUntil v hv).support$.
  obtain ⟨u, hu_adj, hu_support⟩ : ∃ u ∈ (p.takeUntil v hv).support, hexGraph.Adj u v ∧ u ≠ v := by
    have h_predecessor : ∀ {u v : HexVertex} {p : hexGraph.Walk u v}, p.IsPath → v ≠ u → ∃ w ∈ p.support, hexGraph.Adj w v ∧ w ≠ v := by
      intros u v p hp hv_ne_u; induction' p with u v p ih; aesop;
      cases eq_or_ne ih p <;> simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ];
      exact Or.inl ( Ne.symm hv_ne_u );
    apply h_predecessor;
    · grind +suggestions;
    · rintro rfl; norm_num [ paperStart ] at hv_dc; linarith;
  have := hex_adj_flip_bool hu_support.1; simp_all +decide ;
  exact absurd ( dc_step_from_false hu_support.1 ( by aesop ) ) ( by specialize hprev_above u.1 u.2.1; aesop )

/-
The prefix from paperStart to the first vertex at dc = -W,
    where all vertices before v have dc > -W, gives a valid PaperBridge.

    Uses bridge_satisfies_paper_inf_strip from SAWHWStructural.
-/
theorem prefix_to_first_min_is_bridge {w : HexVertex}
    (p : hexGraph.Path paperStart w) (W : ℕ) (hW : 1 ≤ W)
    (v : HexVertex) (hv : v ∈ p.1.support)
    (hv_dc : v.1 + v.2.1 = -(W : ℤ))
    (hv_false : v.2.2 = false)
    (hstrip : ∀ u ∈ (p.1.takeUntil v hv).support,
      -(W : ℤ) ≤ u.1 + u.2.1 ∧ u.1 + u.2.1 ≤ 0) :
    ∃ (b : PaperBridge W), b.walk.1.length = (p.1.takeUntil v hv).length := by
  have h_path : (p.1.takeUntil v hv).IsPath := by
    grind +suggestions;
  exact ⟨ ⟨ v, ⟨ _, h_path ⟩, ⟨ hv_dc, hv_false ⟩, fun u hu => bridge_satisfies_paper_inf_strip W hW ⟨ _, h_path ⟩ hv_false hv_dc hstrip u hu ⟩, rfl ⟩

end