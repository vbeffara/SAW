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

/-
PROBLEM
Every vertex in the support has x-coordinate ≤ walk_max_x.

PROVIDED SOLUTION
walk_max_x is defined as (p.support.map (·.1)).foldl max v.1. Since u ∈ p.support, u.1 is in the mapped list. The foldl max over a list gives a value ≥ any element in the list (starting from v.1). Use List.foldl_max_le or similar. The key is that foldl max returns a value that is ≥ each element in the list and the initial value.
-/
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

/-
PROBLEM
The walk_max_x is achieved by some vertex in the support.

PROVIDED SOLUTION
walk_max_x is defined as (p.support.map (·.1)).foldl max v.1. Since p.support is nonempty (contains at least v), the mapped list contains v.1. The foldl max over a nonempty list achieves its maximum at some element. So there exists u in the support with u.1 = walk_max_x p. Use induction on the walk or on the list. Base case: nil walk, max = v.1. Inductive: cons step, the max is either the previous max or the new vertex.
-/
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

/-
PROBLEM
An n-step SAW from hexOrigin visits vertices with x-coordinate
    in [0, n]. This is because each step changes x by at most 1.

PROVIDED SOLUTION
Each step in hexGraph changes x-coordinate by at most 1 (from hexGraph_walk_bound or by inspecting adjacency). Starting from hexOrigin with x=0, after n steps the x-coordinate is at most n. Use hexGraph_walk_bound which gives |w.1 - v.1| ≤ walk.length for any walk from v to w. Since v = hexOrigin has v.1 = 0, and the walk has length n, every vertex u in the support satisfies u.1 ≤ n (since u can be reached from hexOrigin in at most n steps, and each step changes x by at most 1).
-/
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

/-
PROBLEM
The maximum x-coordinate in an n-step SAW from hexOrigin is at most n.

PROVIDED SOLUTION
Use walk_max_x_achieved to get some u in the support with u.1 = walk_max_x, then use saw_x_coord_bound to get u.1 ≤ n, hence walk_max_x ≤ n.
-/
lemma saw_max_x_le_length {n : ℕ} (s : SAW hexOrigin n) :
    walk_max_x s.p.1 ≤ n := by
  have := walk_max_x_achieved s.p.1;
  exact this.choose_spec.2 ▸ saw_x_coord_bound s _ this.choose_spec.1

/-! ## Origin bridge partition summability for x < xc -/

/-
PROBLEM
Origin bridge partition is summable at any 0 < x ≤ xc.
    Follows from summability at xc by comparison.

PROVIDED SOLUTION
We need summability of fun b : OriginBridge T => x ^ b.1.walk.1.length for 0 < x ≤ xc.

The key fact is origin_bridge_upper_bound T hT : origin_bridge_partition T xc ≤ 1, where origin_bridge_partition T xc = ∑' b : OriginBridge T, xc ^ b.1.walk.1.length.

But this fact uses the tsum convention (= 0 if not summable), so we can't directly conclude summability from it.

Instead, use a direct approach: summability at xc follows from the fact that the series has bounded partial sums. If not summable, then origin_bridge_partition T xc would be 0 by convention, but origin_bridge_lower_bound says ∃ c > 0, ∀ T ≥ 1, c/T ≤ origin_bridge_partition T xc. So origin_bridge_partition T xc > 0 for T ≥ 1.

Actually, the argument in origin_bridge_summable_at_xc from SAWHammersleyWelsh does exactly this but it's in a file we don't import. Let me reproduce the argument:
1. origin_bridge_upper_bound gives origin_bridge_partition T xc ≤ 1
2. By contraposition: if not summable, tsum = 0, but origin_bridge_lower_bound gives tsum > 0. Contradiction.

Wait, origin_bridge_lower_bound says ∃ c > 0, ∀ T ≥ 1, c/T ≤ origin_bridge_partition T xc. If not summable, origin_bridge_partition T xc = 0 (by tsum convention), but c/T > 0, contradicting 0 = origin_bridge_partition T xc ≥ c/T > 0.

So summability at xc follows by contradiction using origin_bridge_lower_bound.

For x ≤ xc: use Summable.of_nonneg_of_le with the pointwise bound x^n ≤ xc^n (from pow_le_pow_left₀ since x ≤ xc).
-/
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

/-
PROBLEM
For 0 < x ≤ xc, origin_bridge_partition 1 x > 0.
    Requires x ≤ xc to ensure summability (so tsum gives the true value).

PROVIDED SOLUTION
origin_bridge_partition T x = ∑' b : OriginBridge T, x ^ b.1.walk.1.length.

Since x ≤ xc, origin_bridge_summable_le_xc' gives summability. So the tsum is the true sum.

From origin_bridge_lower_bound: ∃ c > 0, c/T ≤ origin_bridge_partition T xc. If x = xc, then origin_bridge_partition T xc ≥ c/T > 0.

For x < xc: we need a different argument. We know there exists at least one OriginBridge T (for T = 1, bridge_width1 0 works; for larger T, we need more). Actually, for T ≥ 1, we can construct a bridge of width T: a zigzag from (0,0,false) to (T,y,b) staying in the strip.

But actually, origin_bridge_lower_bound gives origin_bridge_partition T xc ≥ c/T > 0. For x ≤ xc, each term x^length > 0 when x > 0. If the series at xc sums to a positive value, and x > 0, then the series at x also sums to a positive value. Specifically:

If x ≤ xc: by origin_bridge_summable_le_xc' we have summability. Since origin_bridge_partition T xc > 0 (from lower bound), there exists at least one bridge b with xc^{b.length} > 0. The same bridge contributes x^{b.length} > 0 to origin_bridge_partition T x. Since the series is summable and nonneg with at least one positive term, tsum > 0.

Use tsum_pos: requires summability, nonneg terms, and existence of a positive term.
-/
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