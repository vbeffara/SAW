/-
# Bridge Extraction from SAWs

The key step in the Hammersley-Welsh decomposition:
extracting a PaperBridge from a SAW that visits low diagCoord values.
-/

import Mathlib
import RequestProject.SAWHWStructural
import RequestProject.SAWHWComplete

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Walk minimum diagCoord -/

/-- Minimum diagCoord in a walk. -/
def walk_min_dc {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map (fun u => u.1 + u.2.1)).foldl min (v.1 + v.2.1)

/-
walk_min_dc ≤ any vertex's dc in the walk.
-/
lemma walk_min_dc_le {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walk_min_dc p ≤ u.1 + u.2.1 := by
  -- The minimum of a list is less than or equal to any element in the list.
  have h_min_le_fold : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → List.foldl min (v.1 + v.2.1) l ≤ x := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_min_le_fold ( List.mem_map.mpr ⟨ u, hu, rfl ⟩ )

/-
walk_min_dc is achieved by some vertex.
-/
lemma walk_min_dc_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, u.1 + u.2.1 = walk_min_dc p := by
  have h_min_achieved : ∀ {l : List ℤ}, l ≠ [] → ∃ x ∈ l, x = List.foldl min (l.head!) l := by
    intro l hl_nonempty
    induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.foldl ];
    cases l <;> simp_all +decide [ List.foldl ];
    grind;
  specialize @h_min_achieved ( List.map ( fun u => u.1 + u.2.1 ) p.support ) ; simp_all +decide;
  cases h : p.support <;> simp_all +decide [ walk_min_dc ];
  cases p <;> aesop

/-- walk_min_dc ≤ v.1 + v.2.1 (starting vertex). -/
lemma walk_min_dc_le_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    walk_min_dc p ≤ v.1 + v.2.1 := by
  exact walk_min_dc_le p v (SimpleGraph.Walk.start_mem_support p)

/-! ## Width of a SAW -/

/-- Width of a SAW from paperStart: the max dc drop.
    paperStart has dc = 0, so width = -min_dc. -/
def saw_width {w : HexVertex} (p : hexGraph.Path paperStart w) : ℕ :=
  (-(walk_min_dc p.1)).toNat

/-! ## Bridge extraction: the first vertex at minimum dc -/

/-- For a path from paperStart that visits dc < 0, extract a bridge.
    The prefix up to the first vertex at minimum dc is a PaperBridge. -/
lemma bridge_extraction {w : HexVertex}
    (p : hexGraph.Path paperStart w)
    (hw : walk_min_dc p.1 < 0)
    : ∃ (T : ℕ) (hT : 1 ≤ T) (β : PaperBridge T),
      β.walk.1.length ≤ p.1.length ∧
      T = saw_width p := by
  sorry

/-! ## Key inequality for width-W SAWs -/

/-- The number of width-W SAWs of length n is at most
    the sum over bridges of width W of (number of remaining SAWs). -/
lemma width_W_saw_bound (W : ℕ) (hW : 1 ≤ W) {x : ℝ} (hx : 0 < x) (hxc : x ≤ xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1),
      (Fintype.card {s : SAW paperStart n // saw_width s.p = W} : ℝ) * x ^ n ≤
    paper_bridge_partition W x *
      ∑ n ∈ Finset.range (N + 1),
        (Fintype.card {s : SAW paperStart n // saw_width s.p < W} : ℝ) * x ^ n := by
  sorry

end