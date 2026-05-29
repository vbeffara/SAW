/-
# Bridge Decomposition Injection Infrastructure

Helper lemmas for the bridge decomposition injection from SAWHammersleyWelsh.lean.

The Hammersley-Welsh bridge decomposition (1962) shows that any SAW
can be uniquely decomposed into a sequence of bridges with monotone widths.

## Reference

  Hammersley, J. M. and Welsh, D. J. A.,
  "Further results on the rate of convergence to the connective constant
   of the hypercubical lattice", 1962.

  Madras, N. and Slade, G., "Self-avoiding walks", Section 3.1, 1993.
-/

import Mathlib
import RequestProject.SAWBridgeFix

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Maximum x-coordinate in a walk -/

/-- The maximum x-coordinate among vertices in a walk's support. -/
def walk_max_x {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map (·.1)).foldl max v.1


lemma walk_max_x_bound {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    u.1 ≤ walk_max_x p := by
  have h_max : ∀ {l : List ℤ}, (∀ x ∈ l, x ≤ List.foldl max v.1 l) := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_max _ ( List.mem_map.mpr ⟨ u, hu, rfl ⟩ )

/-- The start vertex has x-coordinate ≤ walk_max_x. -/
lemma walk_max_x_ge_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    v.1 ≤ walk_max_x p := by
  exact walk_max_x_bound p v (SimpleGraph.Walk.start_mem_support p)


lemma walk_max_x_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, u.1 = walk_max_x p := by
  unfold walk_max_x;
  have h_max_in_list : ∀ {l : List ℤ}, l ≠ [] → ∃ x ∈ l, x = List.foldl max l.head! l := by
    intros l hl_nonempty
    induction' l using List.reverseRecOn with l ih;
    · contradiction;
    · cases l <;> simp_all +decide [ List.foldl_append ];
      grind;
  specialize h_max_in_list (show List.map (fun x => x.1) p.support ≠ [] from ?_) ; aesop;
  cases p <;> aesop

/-! ## SAW decomposition at a vertex -/

lemma saw_x_coord_bound {n : ℕ} (s : SAW hexOrigin n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) : v.1 ≤ n := by
  have h_len : (s.p.1.length : ℤ) = n := by
    exact_mod_cast s.l;
  have h_bound : ∀ w ∈ (s.p.1.support), w.1 ≤ (s.p.1.length : ℤ) := by
    intros w hw; exact (by
    have := hexGraph_walk_bound (s.p.1.takeUntil w hw);
    norm_num [ hexOrigin ] at * ; linarith [ SimpleGraph.Walk.length_takeUntil_le ( s.p.1 ) hw ] ;);
  exact h_len ▸ h_bound v hv


lemma saw_max_x_le_length {n : ℕ} (s : SAW hexOrigin n) :
    walk_max_x s.p.1 ≤ n := by
  have := walk_max_x_achieved s.p.1;
  exact this.choose_spec.2 ▸ saw_x_coord_bound s _ this.choose_spec.1

/-! ## Existence of width-1 origin bridges -/

/-- There exists at least one origin bridge of width 1. -/
lemma origin_bridge_one_nonempty : Nonempty (OriginBridge 1) :=
  ⟨⟨bridge_width1 0, rfl⟩⟩

/- Note: origin_bridge_lower_bound, origin_bridge_summable_le_xc', and
   origin_bridge_partition_pos were previously defined here but are
   superseded by paper_bridge_lower_bound, paper_bridge_summable, and
   paper_bridge_partition_pos in SAWPaperChain.lean which use diagonal-
   coordinate bridges (PaperBridge) instead of horizontal-coordinate
   bridges (OriginBridge). -/

end
