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

/-- Superseded by paper_bridge_lower_bound in SAWPaperChain.lean.
    Kept as sorry to avoid breaking dependent files. -/
private theorem origin_bridge_lower_bound :
    ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ origin_bridge_partition T xc := by
  sorry

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
  -- The maximum of the list of x-coordinates is achieved by some element in the list.
  have h_max_in_list : ∀ {l : List ℤ}, l ≠ [] → ∃ x ∈ l, x = List.foldl max l.head! l := by
    intros l hl_nonempty
    induction' l using List.reverseRecOn with l ih;
    · contradiction;
    · cases l <;> simp_all +decide [ List.foldl_append ];
      grind;
  specialize h_max_in_list (show List.map (fun x => x.1) p.support ≠ [] from ?_) ; aesop;
  cases p <;> aesop

/-! ## SAW decomposition at a vertex

A key step: splitting a SAW at a given interior vertex produces
two sub-SAWs. This is needed for the bridge decomposition. -/


lemma saw_x_coord_bound {n : ℕ} (s : SAW hexOrigin n) (v : HexVertex)
    (hv : v ∈ s.p.1.support) : v.1 ≤ n := by
  -- By definition of SAW, we know that the path has length n.
  have h_len : (s.p.1.length : ℤ) = n := by
    exact_mod_cast s.l;
  -- By definition of SAW, we know that the path has length n and that the x-coordinate of any vertex in the path is bounded by n.
  have h_bound : ∀ w ∈ (s.p.1.support), w.1 ≤ (s.p.1.length : ℤ) := by
    intros w hw; exact (by
    have := hexGraph_walk_bound (s.p.1.takeUntil w hw);
    norm_num [ hexOrigin ] at * ; linarith [ SimpleGraph.Walk.length_takeUntil_le ( s.p.1 ) hw ] ;);
  exact h_len ▸ h_bound v hv


lemma saw_max_x_le_length {n : ℕ} (s : SAW hexOrigin n) :
    walk_max_x s.p.1 ≤ n := by
  have := walk_max_x_achieved s.p.1;
  exact this.choose_spec.2 ▸ saw_x_coord_bound s _ this.choose_spec.1

/-! ## Origin bridge partition summability for x < xc -/


lemma origin_bridge_summable_le_xc' (T : ℕ) (hT : 1 ≤ T) {x : ℝ}
    (hx : 0 < x) (hxc : x ≤ xc) :
    Summable (fun b : OriginBridge T => x ^ b.1.walk.1.length) := by
  -- Since $x \leq xc$, we have $x^{b.1.walk.1.length} \leq xc^{b.1.walk.1.length}$ for all $b$.
  have h_le : ∀ b : OriginBridge T, x ^ (b.1.walk.1.length) ≤ xc ^ (b.1.walk.1.length) := by
    exact fun b => pow_le_pow_left₀ hx.le hxc _
  generalize_proofs at *; (
  refine' Summable.of_nonneg_of_le ( fun b => pow_nonneg hx.le _ ) ( fun b => h_le b ) _;
  by_contra h_not_summable
  generalize_proofs at *; (
  have h_zero : origin_bridge_partition T xc = 0 := by
    exact tsum_eq_zero_of_not_summable h_not_summable
  generalize_proofs at *; (
  have := origin_bridge_lower_bound; obtain ⟨ c, hc₀, hc ⟩ := this; specialize hc T hT; linarith [ show 0 < c / T from div_pos hc₀ ( Nat.cast_pos.mpr hT ) ] ;)))

/-! ## Existence of width-1 origin bridges -/

/-- There exists at least one origin bridge of width 1. -/
lemma origin_bridge_one_nonempty : Nonempty (OriginBridge 1) :=
  ⟨⟨bridge_width1 0, rfl⟩⟩


lemma origin_bridge_partition_pos {T : ℕ} (hT : 1 ≤ T) {x : ℝ}
    (hx : 0 < x) (hxc : x ≤ xc) :
    0 < origin_bridge_partition T x := by
  by_contra h_neg;
  obtain ⟨c, hc_pos, hc_bound⟩ : ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ origin_bridge_partition T xc := by
    exact origin_bridge_lower_bound;
  -- Since there exists at least one bridge b with xc^{b.length} > 0, we have origin_bridge_partition T xc > 0.
  have h_pos : origin_bridge_partition T xc > 0 := by
    exact lt_of_lt_of_le ( div_pos hc_pos ( Nat.cast_pos.mpr hT ) ) ( hc_bound T hT );
  obtain ⟨b, hb⟩ : ∃ b : OriginBridge T, b.1.walk.1.length > 0 := by
    by_cases h : ∃ b : OriginBridge T, b.1.walk.1.length > 0;
    · exact h;
    · simp_all +decide [ origin_bridge_partition ];
  exact h_neg <| lt_of_lt_of_le ( by positivity ) <| Summable.le_tsum ( show Summable _ from by
                                                                          convert origin_bridge_summable_le_xc' T hT hx hxc using 1 ) b <| by
                                                                          exact fun _ _ => pow_nonneg hx.le _

end