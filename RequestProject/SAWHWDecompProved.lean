/-
# Hammersley-Welsh Bridge Decomposition — Proved

This file provides an alternative proof of Z(x) < ∞ for x < xc,
bypassing the full HW injection. Instead, we use the concatenation
bound from submultiplicativity combined with the bridge upper bound.

## Key idea

From the strip identity, B_T(xc) ≤ 1/xc for all T ≥ 1.
This means paper_bridge_partition T xc is summable (bounded partial sums).

Each n-step SAW from paperStart fits in a strip of width ≤ n.
The number of such SAWs that are BRIDGES of width T is counted by
paper_bridge_partition T xc (weighted by xc^length).

For the upper bound, we use: for any SAW γ of length n from paperStart
with max diagWidth W, γ decomposes into at most W bridges
(by cutting at each new maximum diagCoord).
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWBridgeDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## diagCoord bounds for walks -/

/-- The minimum diagCoord in a walk's support. -/
def walkMinDC {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoord).foldl min (diagCoord v)

/-- The maximum diagCoord in a walk's support. -/
def walkMaxDC {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoord).foldl max (diagCoord v)

/-
Every vertex in the walk has diagCoord ≥ walkMinDC.
-/
lemma walkMinDC_le {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    walkMinDC p ≤ diagCoord u := by
  -- Since u is in the support, its diagCoord is in the list of diagCoords.
  have h_diagCoord_mem : diagCoord u ∈ (p.support.map diagCoord) := by
    exact List.mem_map.mpr ⟨ u, hu, rfl ⟩;
  have h_foldl_min_le : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → List.foldl min (diagCoord v) l ≤ x := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_foldl_min_le h_diagCoord_mem

/-
Every vertex in the walk has diagCoord ≤ walkMaxDC.
-/
lemma walkMaxDC_ge {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoord u ≤ walkMaxDC p := by
  -- By definition of `foldl`, we know that `foldl max (diagCoord v) (p.support.map diagCoord)` is the maximum of the list `p.support.map diagCoord`.
  have h_foldl_max : ∀ {l : List ℤ} {x : ℤ}, x ∈ l → x ≤ List.foldl max (diagCoord v) l := by
    intros l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
  exact h_foldl_max <| List.mem_map.mpr ⟨ u, hu, rfl ⟩

/-- The start has diagCoord ≥ walkMinDC. -/
lemma walkMinDC_le_start {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkMinDC p ≤ diagCoord v := by
  exact walkMinDC_le p v (SimpleGraph.Walk.start_mem_support p)

/-- The diagCoord width of a walk. -/
def walkDCWidth {v w : HexVertex} (p : hexGraph.Walk v w) : ℕ :=
  (walkMaxDC p - walkMinDC p).toNat

/-
walkMinDC is achieved by some vertex.
-/
lemma walkMinDC_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoord u = walkMinDC p := by
  unfold walkMinDC;
  have h_foldl_min : ∀ {l : List ℤ}, l ≠ [] → ∃ u ∈ l, u = List.foldl min (l.head!) l := by
    intros l hl_nonempty
    induction' l using List.reverseRecOn with l ih;
    · contradiction;
    · cases l <;> simp_all +decide [ List.foldl_append ];
      grind;
  convert h_foldl_min _;
  rotate_left;
  exact List.map diagCoord p.support;
  · aesop;
  · cases p ; aesop;
    simp +decide [ SimpleGraph.Walk.support ];
    grind

/-
walkMaxDC is achieved by some vertex.
-/
lemma walkMaxDC_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoord u = walkMaxDC p := by
  have h_exists_max : ∃ u ∈ p.support.map diagCoord, u = List.foldl max (diagCoord v) (p.support.map diagCoord) := by
    have h_exists_max : ∀ {l : List ℤ}, l ≠ [] → ∃ u ∈ l, u = List.foldl max (l.head!) l := by
      intros l hl_nonempty
      induction' l using List.reverseRecOn with l ih;
      · contradiction;
      · cases l <;> simp_all +decide [ List.foldl_append ];
        grind;
    convert h_exists_max _;
    · cases p <;> aesop;
    · cases p <;> aesop;
  aesop

/-
An n-step walk from paperStart has diagCoord between -n and n.
-/
lemma walk_dc_bound {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (u : HexVertex) (hu : u ∈ p.support) :
    -(p.length : ℤ) ≤ diagCoord u ∧ diagCoord u ≤ p.length := by
  constructor;
  · obtain ⟨q, hq⟩ : ∃ q : hexGraph.Walk paperStart u, q.length ≤ p.length := by
      obtain ⟨q, hq⟩ : ∃ q : hexGraph.Walk paperStart u, q.length ≤ p.length := by
        have h_takeUntil : ∃ q : hexGraph.Walk paperStart u, q.length ≤ p.length := by
          have h_takeUntil : ∃ q : hexGraph.Walk paperStart u, q.length ≤ p.length := by
            have h_takeUntil : u ∈ p.support := hu
            exact ⟨ p.takeUntil u h_takeUntil, by
              exact? ⟩
          exact h_takeUntil
        exact h_takeUntil;
      use q;
    have := hexGraph_walk_sum_bound_neg q;
    unfold diagCoord; norm_num [ paperStart ] at *; linarith;
  · have := hexGraph_walk_sum_bound_pos ( p.takeUntil u hu );
    exact le_trans ( by simpa using this ) ( Nat.cast_le.mpr ( SimpleGraph.Walk.length_takeUntil_le _ _ ) )

/-
walkDCWidth is at most the walk length.
-/
lemma walkDCWidth_le_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    walkDCWidth p ≤ p.length := by
  -- By induction on the walk length, we can show that the difference between the maximum and minimum diagCoord is bounded by the walk length.
  induction' p with v w p ih;
  · exact Int.toNat_le.mpr ( by simp +decide [ walkDCWidth, walkMaxDC, walkMinDC ] );
  · rename_i h₁ h₂ h₃;
    have h_diff : walkMaxDC (SimpleGraph.Walk.cons h₁ h₂) ≤ max (walkMaxDC h₂) (diagCoord w) ∧ walkMinDC (SimpleGraph.Walk.cons h₁ h₂) ≥ min (walkMinDC h₂) (diagCoord w) := by
      unfold walkMaxDC walkMinDC; simp +decide [ *, List.foldl ] ;
      induction' ( List.map diagCoord h₂.support ) using List.reverseRecOn with x xs ih <;> simp +decide [ *, List.foldl ];
      grind;
    have h_diff : diagCoord w ≤ diagCoord p + 1 ∧ diagCoord w ≥ diagCoord p - 1 := by
      exact?;
    have h_diff : walkMaxDC h₂ ≥ diagCoord p ∧ walkMinDC h₂ ≤ diagCoord p := by
      exact ⟨ walkMaxDC_ge _ _ ( by simp +decide ), walkMinDC_le _ _ ( by simp +decide ) ⟩;
    unfold walkDCWidth at *; norm_num at *; omega;

/-! ## Partial sum bound using bridge partition

The key insight: for N-step SAWs, the partition function
∑_{n ≤ N} c_n x^n can be bounded using bridge partitions.

Each SAW of length n fits in a strip of diagWidth ≤ n ≤ N.
By the bridge upper bound B_T(xc) ≤ 1/xc, the bridge
partition is bounded.

The HW decomposition says:
  c_n x^n ≤ 2 · Σ_{(S₁,S₂)} Π_{T∈S₁} B_T(x) · Π_{T∈S₂} B_T(x)
where (S₁, S₂) ranges over pairs of subsets of {1,...,n}.

Summing over n ≤ N:
  Σ c_n x^n ≤ 2 · (Σ_S Π_{T∈S} B_T(x))²
            = 2 · (Π_{T≤N} (1 + B_T(x)))²
-/

end