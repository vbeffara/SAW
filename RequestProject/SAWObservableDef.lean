/-
# Parafermionic Observable — Formal Definition and Cancellation Identity

Formalizes the parafermionic observable F(z) and the cancellation identity
(Lemma 1) from Section 2 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Main definitions

* `hexNeighbors3` — the three neighbors of a hex vertex
* `midEdgeDir` — direction vector from a vertex to a neighbor
* `MidEdgeTrail` — a trail (edge-SAW) from a starting vertex to a mid-edge
* `hexWalkWinding` — correct winding using arg(d₂/d₁) at each turn

## Main results

* `midEdgeDir_j_relation` — direction vectors satisfy d₁ = j·d₀, d₂ = j̄·d₀
* `tripletExtendFromN` — the triplet walk extension operation
* `triplet_contribution_at_vertex` — triplet group contribution is zero
* `pair_contribution_at_vertex` — pair group contribution is zero
* `cancellation_identity_abstract` — vertex relation from the j-relation
-/

import Mathlib
import RequestProject.SAWObservable

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Hex vertex neighbors -/

/-- The three neighbors of a FALSE vertex (x, y, false). -/
def falseNeighbors (x y : ℤ) : Fin 3 → HexVertex
  | 0 => (x, y, true)
  | 1 => (x + 1, y, true)
  | 2 => (x, y + 1, true)

/-- The three neighbors of a TRUE vertex (x, y, true). -/
def trueNeighbors (x y : ℤ) : Fin 3 → HexVertex
  | 0 => (x, y, false)
  | 1 => (x - 1, y, false)
  | 2 => (x, y - 1, false)

/-- The three neighbors of any hex vertex. -/
def hexNeighbors3 (v : HexVertex) : Fin 3 → HexVertex :=
  if v.2.2 then trueNeighbors v.1 v.2.1
  else falseNeighbors v.1 v.2.1

/-- Each neighbor is adjacent to v. -/
lemma hexNeighbors3_adj (v : HexVertex) (i : Fin 3) :
    hexGraph.Adj v (hexNeighbors3 v i) := by
  unfold hexNeighbors3 falseNeighbors trueNeighbors hexGraph
  rcases v with ⟨x, y, b⟩
  cases b <;> fin_cases i <;> simp

/-- The direction from v to its i-th neighbor, embedded in ℂ. -/
def midEdgeDir (v : HexVertex) (i : Fin 3) : ℂ :=
  correctHexEmbed (hexNeighbors3 v i) - correctHexEmbed v

/-! ## Direction vectors satisfy the j-relation -/

/-- At a FALSE vertex, d₁ = j · d₀ and d₂ = conj(j) · d₀. -/
lemma false_midEdgeDir_j (x y : ℤ) :
    midEdgeDir (x, y, false) 1 = j * midEdgeDir (x, y, false) 0 ∧
    midEdgeDir (x, y, false) 2 = conj j * midEdgeDir (x, y, false) 0 := by
  unfold midEdgeDir hexNeighbors3 falseNeighbors
  simp only [ite_false]
  exact ⟨false_dir2_eq_j x y, false_dir3_eq_conjj x y⟩

/-- At a TRUE vertex, d₁ = j · d₀ and d₂ = conj(j) · d₀. -/
lemma true_midEdgeDir_j (x y : ℤ) :
    midEdgeDir (x, y, true) 1 = j * midEdgeDir (x, y, true) 0 ∧
    midEdgeDir (x, y, true) 2 = conj j * midEdgeDir (x, y, true) 0 := by
  unfold midEdgeDir hexNeighbors3 trueNeighbors
  simp only [ite_true]
  exact ⟨true_dir2_eq_j x y, true_dir3_eq_conjj x y⟩

/-- At any hex vertex, the direction vectors satisfy d₁ = j·d₀, d₂ = conj(j)·d₀. -/
theorem midEdgeDir_j_relation (v : HexVertex) :
    midEdgeDir v 1 = j * midEdgeDir v 0 ∧
    midEdgeDir v 2 = conj j * midEdgeDir v 0 := by
  rcases v with ⟨x, y, b⟩
  cases b
  · exact false_midEdgeDir_j x y
  · exact true_midEdgeDir_j x y

/-! ## Correct winding function for hexagonal lattice walks

The winding of a walk is the total rotation of the direction vector.
At each vertex, the turning angle is computed as `Complex.arg(d₂/d₁)`,
where d₁ and d₂ are the incoming and outgoing direction vectors.

Using `arg(d₂/d₁)` instead of `arg(d₂) - arg(d₁)` correctly handles
the branch cut of Complex.arg at the negative real axis. On the hex
lattice, consecutive edge directions always have `|arg(d₂/d₁)| < π`,
so `arg(d₂/d₁)` gives the unique correct turning angle. -/

/-- The winding of a walk, computed using `arg(d₂/d₁)` at each turn.
    This correctly handles the branch cut of Complex.arg. -/
def hexWalkWinding : List HexVertex → ℝ
  | [] | [_] | [_, _] => 0
  | v₀ :: v₁ :: v₂ :: rest =>
    let d₁ := correctHexEmbed v₁ - correctHexEmbed v₀
    let d₂ := correctHexEmbed v₂ - correctHexEmbed v₁
    Complex.arg (d₂ / d₁) + hexWalkWinding (v₁ :: v₂ :: rest)

/-! ## Trail-based mid-edge walks -/

/-- A trail from vertex `s` ending at the mid-edge between `prev` and `next`.
    The trail from s to prev uses each edge at most once. -/
structure MidEdgeTrail (s prev next : HexVertex) where
  trail : hexGraph.Walk s prev
  is_trail : trail.IsTrail
  adj : hexGraph.Adj prev next

/-- The length of a MidEdgeTrail (edges in trail + 1 for the half-edge). -/
def MidEdgeTrail.len {s prev next : HexVertex}
    (γ : MidEdgeTrail s prev next) : ℕ :=
  γ.trail.length + 1

/-- The full vertex list including the next vertex. -/
def MidEdgeTrail.fullSupport {s prev next : HexVertex}
    (γ : MidEdgeTrail s prev next) : List HexVertex :=
  γ.trail.support ++ [next]

/-- The winding of a MidEdgeTrail, using the corrected hexWalkWinding. -/
def MidEdgeTrail.winding {s prev next : HexVertex}
    (γ : MidEdgeTrail s prev next) : ℝ :=
  hexWalkWinding γ.fullSupport

/-- The weight of a MidEdgeTrail: e^{-iσW} · xc^ℓ. -/
def MidEdgeTrail.weight {s prev next : HexVertex}
    (γ : MidEdgeTrail s prev next) : ℂ :=
  walkWeight γ.winding γ.len xc sigma

/-! ## Helper lemma: trail append preserves trail -/

private lemma trail_append_of_disjoint {V : Type*} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w)
    (hp : p.IsTrail) (hq : q.IsTrail)
    (h : ∀ e, e ∈ p.edges → e ∉ q.edges) :
    (p.append q).IsTrail :=
  ⟨by rw [SimpleGraph.Walk.edges_append]
      exact hp.edges_nodup.append hq.edges_nodup
        (List.disjoint_iff_ne.mpr fun a ha b hb hab => h a ha (hab ▸ hb))⟩

/-! ## Triplet extension (correct model)

In the paper's proof of the cancellation identity, a walk γ₁ that
visits only one mid-edge at vertex v is grouped with two extensions.

**Walk model for the triplet:**

γ₁ = MidEdgeTrail(s, n₀, v): walk from s to n₀, half-edge from n₀ to v.
  This visits mid-edge p (between v and n₀) from the n₀ side.

γ₂ = MidEdgeTrail(s, v, n₁): extend γ₁ by appending edge n₀ → v,
  then half-edge from v to n₁.
  This visits mid-edges p (as full edge) and q (as half-edge).

γ₃ = MidEdgeTrail(s, v, n₂): similarly, ending at mid-edge r.

The winding relations:
  W(γ₂) = W(γ₁) + arg(-midEdgeDir v 1 / midEdgeDir v 0)
  W(γ₃) = W(γ₁) + arg(-midEdgeDir v 2 / midEdgeDir v 0)

For the hexagonal lattice: arg(-j) = -π/3, arg(-conj(j)) = π/3. -/

/-- Extend a MidEdgeTrail(s, n₀, v) to MidEdgeTrail(s, v, nⱼ) by
    appending edge n₀ → v, then taking half-edge v → nⱼ.
    Requires: edge {n₀, v} not in trail (automatic for "visits only one
    mid-edge" walks). -/
def tripletExtendFromN {s n₀ v nⱼ : HexVertex}
    (γ : MidEdgeTrail s n₀ v)
    (adj_n₀_v : hexGraph.Adj n₀ v)
    (adj_v_nⱼ : hexGraph.Adj v nⱼ)
    (h_fresh : s(n₀, v) ∉ γ.trail.edges) :
    MidEdgeTrail s v nⱼ where
  trail := γ.trail.append (.cons adj_n₀_v .nil)
  is_trail := trail_append_of_disjoint γ.trail _ γ.is_trail
    (by constructor; simp [SimpleGraph.Walk.edges])
    (fun e he hq => by simp [SimpleGraph.Walk.edges] at hq; subst hq; exact h_fresh he)
  adj := adj_v_nⱼ

/-- The extended walk has length = original length + 1. -/
lemma tripletExtendFromN_len {s n₀ v nⱼ : HexVertex}
    (γ : MidEdgeTrail s n₀ v) (h₁ : hexGraph.Adj n₀ v) (h₂ : hexGraph.Adj v nⱼ)
    (hf : s(n₀, v) ∉ γ.trail.edges) :
    (tripletExtendFromN γ h₁ h₂ hf).len = γ.len + 1 := by
  simp [tripletExtendFromN, MidEdgeTrail.len, SimpleGraph.Walk.length_append]

/-! ## Key winding identity: arg(-j) = -π/3 and arg(-conj(j)) = π/3

These are the turning angles for the triplet extension on the hex lattice. -/

/-
arg(-j) = -π/3. This is the winding change for the first extension.
    -j = exp(i·(2π/3 - π)) = exp(-iπ/3), so arg(-j) = -π/3.
-/
lemma arg_neg_j : Complex.arg (-j) = -Real.pi / 3 := by
  convert Complex.arg_cos_add_sin_mul_I _ using 2;
  · norm_num [ neg_div, j_eq_complex ];
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin ];
  · constructor <;> linarith [ Real.pi_pos ]

/-
arg(-conj(j)) = π/3. This is the winding change for the second extension.
    -conj(j) = exp(-i·(2π/3 - π)) = exp(iπ/3), so arg(-conj(j)) = π/3.
-/
lemma arg_neg_conj_j : Complex.arg (-conj j) = Real.pi / 3 := by
  convert Complex.arg_cos_add_sin_mul_I _ using 2;
  · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin, j ];
    norm_num [ show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring ];
  · constructor <;> linarith [ Real.pi_pos ]

/-! ## Winding relation for triplet extension

The key fact: the winding change in the triplet extension equals
`arg(-dⱼ/d₀)` where d₀ = midEdgeDir v 0 and dⱼ = midEdgeDir v j.

For j=1: arg(-d₁/d₀) = arg(-j·d₀/d₀) = arg(-j) = -π/3
For j=2: arg(-d₂/d₀) = arg(-conj(j)·d₀/d₀) = arg(-conj(j)) = π/3 -/

/-
The winding relation for the first triplet extension:
    W(γ₂) = W(γ₁) - π/3.
-/
lemma triplet_winding_ext1 {s v : HexVertex}
    (γ : MidEdgeTrail s (hexNeighbors3 v 0) v)
    (hf : s(hexNeighbors3 v 0, v) ∉ γ.trail.edges) :
    (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm
      (hexNeighbors3_adj v 1) hf).winding =
    γ.winding - Real.pi / 3 := by
  unfold MidEdgeTrail.winding tripletExtendFromN;
  unfold MidEdgeTrail.fullSupport; simp +decide [ hexWalkWinding ] ;
  have h_append : ∀ (L : List HexVertex), hexWalkWinding (L ++ [v, hexNeighbors3 v 1]) = hexWalkWinding (L ++ [v]) + Complex.arg ((correctHexEmbed (hexNeighbors3 v 1) - correctHexEmbed v) / (correctHexEmbed v - correctHexEmbed (L.getLastD v))) := by
    intro L; induction' L using List.reverseRecOn with L ih <;> simp_all +decide [ hexWalkWinding ] ;
    induction' L with L ih <;> simp_all +decide [ hexWalkWinding ];
    cases ih <;> simp_all +decide [ hexWalkWinding ];
    rename_i k hk₁ hk₂ hk;
    cases hk₁ <;> simp_all +decide [ hexWalkWinding ];
    · ring;
    · grind;
  convert h_append ( γ.trail.support ) using 1;
  · simp +decide [ SimpleGraph.Walk.support_append ];
  · rw [ show ( correctHexEmbed ( hexNeighbors3 v 1 ) - correctHexEmbed v ) / ( correctHexEmbed v - correctHexEmbed ( γ.trail.support.getLastD v ) ) = -j from ?_ ] ; norm_num [ arg_neg_j ] ; ring;
    rw [ show γ.trail.support.getLastD v = hexNeighbors3 v 0 from ?_ ];
    · rw [ div_eq_iff ] <;> norm_num [ sub_eq_iff_eq_add ];
      · have := midEdgeDir_j_relation v; simp_all +decide [ midEdgeDir ] ;
        linear_combination' this.1;
      · cases v ; simp +decide [ hexNeighbors3 ];
        split_ifs <;> simp +decide [ *, trueNeighbors, falseNeighbors ];
        · unfold correctHexEmbed; aesop;
        · grind +suggestions;
    · have h_last : γ.trail.support.getLastD v = γ.trail.support.getLast! := by
        cases h : γ.trail.support <;> aesop;
      have h_last : γ.trail.support.getLast! = γ.trail.support[γ.trail.support.length - 1]! := by
        grind;
      aesop

/-
The winding relation for the second triplet extension:
    W(γ₃) = W(γ₁) + π/3.
-/
lemma triplet_winding_ext2 {s v : HexVertex}
    (γ : MidEdgeTrail s (hexNeighbors3 v 0) v)
    (hf : s(hexNeighbors3 v 0, v) ∉ γ.trail.edges) :
    (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm
      (hexNeighbors3_adj v 2) hf).winding =
    γ.winding + Real.pi / 3 := by
  unfold tripletExtendFromN MidEdgeTrail.winding;
  unfold MidEdgeTrail.fullSupport;
  simp +decide [ SimpleGraph.Walk.support_append ];
  have h_winding : ∀ (l : List HexVertex), hexWalkWinding (l ++ [v, hexNeighbors3 v 2]) = hexWalkWinding (l ++ [v]) + Complex.arg ((correctHexEmbed (hexNeighbors3 v 2) - correctHexEmbed v) / (correctHexEmbed v - correctHexEmbed (l.getLastD v))) := by
    intro l; induction' l with l ih <;> simp +decide [ *, hexWalkWinding ] ;
    induction' ih with ih ih_ih generalizing l <;> simp_all +decide [ hexWalkWinding ];
    cases ih_ih <;> simp_all +decide [ hexWalkWinding ];
    ring;
  rw [ h_winding, ← arg_neg_conj_j ];
  rw [ show γ.trail.support.getLastD v = hexNeighbors3 v 0 from ?_ ];
  · rw [ show correctHexEmbed ( hexNeighbors3 v 2 ) - correctHexEmbed v = conj j * ( correctHexEmbed ( hexNeighbors3 v 0 ) - correctHexEmbed v ) from ?_, show correctHexEmbed v - correctHexEmbed ( hexNeighbors3 v 0 ) = - ( correctHexEmbed ( hexNeighbors3 v 0 ) - correctHexEmbed v ) from ?_ ];
    · rw [ mul_div_assoc ];
      rw [ div_neg_self ] <;> norm_num [ Complex.ext_iff ];
      cases v ; simp +decide [ hexNeighbors3 ];
      split_ifs <;> simp +decide [ trueNeighbors, falseNeighbors ]; all_goals unfold correctHexEmbed; aesop;
    · ring;
    · convert midEdgeDir_j_relation v |>.2 using 1;
  · have h_last : ∀ (l : List HexVertex), l ≠ [] → l.getLastD v = l.getLast! := by
      intro l hl; induction l using List.reverseRecOn <;> aesop;
    rw [ h_last ];
    · have h_last : ∀ (u v : HexVertex) (p : SimpleGraph.Walk hexGraph u v), p.support.getLast! = v := by
        intros u v p; induction p <;> simp_all +decide [ SimpleGraph.Walk.support ] ;
        grind +locals;
      exact h_last _ _ _;
    · cases γ ; aesop

/-! ## Triplet cancellation for MidEdgeTrail -/

/-- The triplet contribution vanishes. For a walk γ₁ from s to
    mid-edge (n₀, v), its two extensions to mid-edges (v, n₁) and
    (v, n₂) form a triplet whose total contribution is zero.

    Uses: the j-relation on directions, winding relations, and
    the algebraic triplet_contribution_zero. -/
theorem triplet_contribution_at_vertex (v : HexVertex) {s : HexVertex}
    (γ : MidEdgeTrail s (hexNeighbors3 v 0) v)
    (hf : s(hexNeighbors3 v 0, v) ∉ γ.trail.edges) :
    midEdgeDir v 0 * γ.weight +
    midEdgeDir v 1 *
      (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm (hexNeighbors3_adj v 1) hf).weight +
    midEdgeDir v 2 *
      (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm (hexNeighbors3_adj v 2) hf).weight = 0 := by
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]
  have hlen₁ := tripletExtendFromN_len γ (hexNeighbors3_adj v 0).symm (hexNeighbors3_adj v 1) hf
  have hlen₂ := tripletExtendFromN_len γ (hexNeighbors3_adj v 0).symm (hexNeighbors3_adj v 2) hf
  have hwind₁ := triplet_winding_ext1 γ hf
  have hwind₂ := triplet_winding_ext2 γ hf
  show midEdgeDir v 0 * γ.weight +
    j * midEdgeDir v 0 *
      (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm (hexNeighbors3_adj v 1) hf).weight +
    conj j * midEdgeDir v 0 *
      (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm (hexNeighbors3_adj v 2) hf).weight = 0
  have hw₁ : (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm
      (hexNeighbors3_adj v 1) hf).weight =
      walkWeight (γ.winding - Real.pi / 3) (γ.len + 1) xc sigma := by
    unfold MidEdgeTrail.weight; rw [hwind₁, hlen₁]
  have hw₂ : (tripletExtendFromN γ (hexNeighbors3_adj v 0).symm
      (hexNeighbors3_adj v 2) hf).weight =
      walkWeight (γ.winding + Real.pi / 3) (γ.len + 1) xc sigma := by
    unfold MidEdgeTrail.weight; rw [hwind₂, hlen₂]
  rw [hw₁, hw₂]
  convert triplet_contribution_zero (midEdgeDir v 0) γ.winding γ.len using 1
  unfold MidEdgeTrail.weight; ring

/-! ## Pair cancellation for MidEdgeTrail -/

/-- The pair contribution vanishes. Two walks visiting all three
    mid-edges at v, paired by loop reversal. -/
theorem pair_contribution_at_vertex (v : HexVertex) {s : HexVertex}
    (γ₁ : MidEdgeTrail s (hexNeighbors3 v 1) v)
    (γ₂ : MidEdgeTrail s (hexNeighbors3 v 2) v)
    (h_len : γ₁.len = γ₂.len)
    (h_wind : ∃ W : ℝ,
      γ₁.winding = W - 4 * Real.pi / 3 ∧
      γ₂.winding = W + 4 * Real.pi / 3) :
    midEdgeDir v 1 * γ₁.weight +
    midEdgeDir v 2 * γ₂.weight = 0 := by
  obtain ⟨W, hw₁, hw₂⟩ := h_wind
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]
  show j * midEdgeDir v 0 * γ₁.weight +
    conj j * midEdgeDir v 0 * γ₂.weight = 0
  simp only [MidEdgeTrail.weight, hw₁, hw₂]
  convert pair_contribution_zero (midEdgeDir v 0) W γ₁.len using 1
  rw [h_len]; ring

/-! ## The Cancellation Identity (Lemma 1) — abstract form -/

/-- The vertex relation holds when the observable values at the three
    mid-edges satisfy d₀·F₀ + j·d₀·F₁ + j̄·d₀·F₂ = 0.
    This reduces to a rewrite using the j-relation. -/
theorem cancellation_identity_abstract (v : HexVertex) (F₀ F₁ F₂ : ℂ)
    (h : midEdgeDir v 0 * F₀ + j * midEdgeDir v 0 * F₁ +
         conj j * midEdgeDir v 0 * F₂ = 0) :
    midEdgeDir v 0 * F₀ + midEdgeDir v 1 * F₁ + midEdgeDir v 2 * F₂ = 0 := by
  have hj := midEdgeDir_j_relation v
  rw [hj.1, hj.2]
  exact h

/-- The vertex relation sum at v. -/
def vertexRelSum (v : HexVertex) (F₀ F₁ F₂ : ℂ) : ℂ :=
  midEdgeDir v 0 * F₀ + midEdgeDir v 1 * F₁ + midEdgeDir v 2 * F₂

/-- The vertex relation from the walk partition. -/
theorem vertex_relation_from_partition (v : HexVertex) (F₀ F₁ F₂ : ℂ)
    (h_partition : midEdgeDir v 0 * F₀ + j * midEdgeDir v 0 * F₁ +
         conj j * midEdgeDir v 0 * F₂ = 0) :
    vertexRelSum v F₀ F₁ F₂ = 0 :=
  cancellation_identity_abstract v F₀ F₁ F₂ h_partition

/-! ## Summary of proof architecture

### Fully proved (all sorry-free):
1. `midEdgeDir_j_relation` — d₁ = j·d₀, d₂ = j̄·d₀ at every hex vertex
2. `tripletExtendFromN` — the triplet extension is a valid trail operation
3. `tripletExtendFromN_len` — extended walk has length ℓ+1
4. `arg_neg_j` — arg(-j) = -π/3
5. `arg_neg_conj_j` — arg(-conj(j)) = π/3
6. `triplet_winding_ext1` — winding changes by -π/3 in first extension
7. `triplet_winding_ext2` — winding changes by +π/3 in second extension
8. `triplet_contribution_at_vertex` — triplet contribution = 0
9. `pair_contribution_at_vertex` — pair contribution = 0
   (given winding/length relations as hypotheses)
10. `cancellation_identity_abstract` — reduces vertex relation to
    the walk partition hypothesis

### Proof chain:
  Triplet/pair grouping of walks (combinatorial, not yet formalized)
  + triplet_contribution_at_vertex / pair_contribution_at_vertex (proved)
  → cancellation_identity_abstract (proved)
  → B_paper_le_one_strip (via discrete Stokes, not yet formalized)
-/

end