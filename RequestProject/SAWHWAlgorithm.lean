/-
# Hammersley-Welsh Bridge Decomposition: Core Algorithm

Infrastructure for the bridge decomposition injection.

The key theorem `bridge_decomposition_injection_proof` from SAWHWDecomp
says:
  ∑_{n≤N} c_n x^n ≤ 2 · (∑_{S⊆range(N)} ∏_{T∈S} B_{T+1}^x)²

This file establishes helper lemmas for the decomposition.

## Reference

  Hammersley, J.M. and Welsh, D.J.A., 1962.
  Duminil-Copin, H. and Smirnov, S., Annals of Mathematics 175(3), 2012.
-/

import Mathlib
import RequestProject.SAWHWInject

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Translation symmetry of hexGraph -/

/-- Translate a hex vertex by (dx, dy), preserving sublattice type. -/
def hexShift (dx dy : ℤ) (v : HexVertex) : HexVertex :=
  (v.1 + dx, v.2.1 + dy, v.2.2)

/-- Translation preserves hexGraph adjacency. -/
lemma hexShift_adj (dx dy : ℤ) {v w : HexVertex}
    (h : hexGraph.Adj v w) :
    hexGraph.Adj (hexShift dx dy v) (hexShift dx dy w) := by
  simp only [hexShift, hexGraph]
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-- Translation is injective. -/
lemma hexShift_injective (dx dy : ℤ) :
    Function.Injective (hexShift dx dy) := by
  intro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp [hexShift, Prod.mk.injEq] at h
  ext <;> simp_all

/-- x-coordinate of shifted vertex. -/
@[simp] lemma hexShift_fst (dx dy : ℤ) (v : HexVertex) :
    (hexShift dx dy v).1 = v.1 + dx := rfl

/-- Translate a walk along the graph. -/
def shiftWalk (dx dy : ℤ) : {v w : HexVertex} →
    hexGraph.Walk v w →
    hexGraph.Walk (hexShift dx dy v) (hexShift dx dy w)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons (hexShift_adj dx dy h) (shiftWalk dx dy p)

/-- Shifted walk has the same length. -/
@[simp] lemma shiftWalk_length (dx dy : ℤ) {v w : HexVertex}
    (p : hexGraph.Walk v w) :
    (shiftWalk dx dy p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [shiftWalk, ih]

/-- Support of shifted walk is the shift of the original support. -/
lemma shiftWalk_support (dx dy : ℤ) {v w : HexVertex}
    (p : hexGraph.Walk v w) :
    (shiftWalk dx dy p).support = p.support.map (hexShift dx dy) := by
  induction p with
  | nil => simp [shiftWalk]
  | cons h p ih => simp [shiftWalk, SimpleGraph.Walk.support_cons, ih]

/-- Shifting a path gives a path. -/
lemma shiftWalk_isPath (dx dy : ℤ) {v w : HexVertex}
    (p : hexGraph.Walk v w) (hp : p.IsPath) :
    (shiftWalk dx dy p).IsPath := by
  rw [SimpleGraph.Walk.isPath_def] at hp ⊢
  rw [shiftWalk_support]
  exact hp.map (hexShift_injective dx dy)

/-! ## Bipartiteness of hexGraph -/

/-- The hexagonal lattice is bipartite: edges always connect
    false-sublattice to true-sublattice vertices. -/
lemma hexGraph_bipartite {v w : HexVertex} (h : hexGraph.Adj v w) :
    v.2.2 ≠ w.2.2 := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> simp_all

/-
PROBLEM
In any walk from hexOrigin, the vertex at step i has
    sublattice type (i % 2 = 1). In particular, even steps have
    false sublattice (same as hexOrigin).

PROVIDED SOLUTION
By induction on the walk. Base case (nil): hexOrigin.2.2 = false = decide(0 % 2 = 1) = false. Inductive step (cons h p ih): We have hexGraph.Adj u v and a walk from hexOrigin to u. By ih, u.2.2 = decide(p.length % 2 = 1). By hexGraph_bipartite, v.2.2 ≠ u.2.2 (edges swap sublattice). The length of cons h p is p.length + 1. So decide((p.length+1) % 2 = 1) = !decide(p.length % 2 = 1). Since v.2.2 = !u.2.2 (by bipartiteness), and u.2.2 = decide(p.length % 2 = 1), we get v.2.2 = !decide(p.length % 2 = 1) = decide((p.length+1) % 2 = 1).
-/
lemma walk_sublattice_parity {w : HexVertex} (p : hexGraph.Walk hexOrigin w) :
    w.2.2 = decide (p.length % 2 = 1) := by
  -- By definition of $hexGraph.Adj$, we know that $hexGraph.Adj u v$ implies $u.2.2 \neq v.2.2$.
  have h_adj : ∀ {u v : HexVertex}, hexGraph.Adj u v → u.2.2 ≠ v.2.2 :=
    fun a => hexGraph_bipartite a
  -- By induction on the length of the walk, we can show that the sublattice type of the vertex at step i is i % 2.
  have h_ind : ∀ {u v : HexVertex} {p : hexGraph.Walk u v}, (v.2.2 = !u.2.2) ↔ p.length % 2 = 1 := by
    intros u v p;
    induction p <;> simp +decide [ *, Nat.add_mod ];
    grind +ring;
  cases Nat.mod_two_eq_zero_or_one p.length <;> specialize @h_ind hexOrigin w p <;> aesop ( simp_config := { decide := true } ) ;

/-- A SAW from hexOrigin of even length ends at a false-sublattice vertex. -/
lemma saw_even_end_false {n : ℕ} (s : SAW hexOrigin n) (hn : Even n) :
    s.w.2.2 = false := by
  have := walk_sublattice_parity s.p.1
  rw [s.l] at this
  simp [Nat.even_iff.mp hn] at this
  exact this

/-! ## Bridge translation to origin bridge

Given a bridge starting from (0, y, false), we can translate it
to start from hexOrigin = (0, 0, false), obtaining an origin bridge
of the same width and length. -/

/-- A bridge starting from a false-sublattice vertex at x=0 can be
    translated to an origin bridge. -/
def bridgeToOriginBridge_false {T : ℕ} (b : Bridge T)
    (hb : b.start_v.2.2 = false) : OriginBridge T :=
  let dy := b.start_v.2.1
  ⟨{
    start_v := hexShift 0 (-dy) b.start_v
    end_v := hexShift 0 (-dy) b.end_v
    walk := ⟨shiftWalk 0 (-dy) b.walk.1,
            shiftWalk_isPath 0 (-dy) b.walk.1 b.walk.2⟩
    start_left := by simp [hexShift, b.start_left]
    end_right := by simp [hexShift, b.end_right]
    in_strip := by
      intro v hv
      rw [shiftWalk_support] at hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      have := b.in_strip u hu
      simp [hexShift]
      exact this
  }, by
    show hexShift 0 (-dy) b.start_v = hexOrigin
    simp [hexShift, hexOrigin]
    exact ⟨b.start_left, by ring, hb⟩⟩

/-- The translated bridge has the same length. -/
lemma bridgeToOriginBridge_false_length {T : ℕ} (b : Bridge T)
    (hb : b.start_v.2.2 = false) :
    (bridgeToOriginBridge_false b hb).1.walk.1.length = b.walk.1.length := by
  simp [bridgeToOriginBridge_false]

/-! ## Walk splitting and analysis -/

/-- For a path, splitting preserves total length. -/
lemma path_split_length {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support) :
    (p.takeUntil u hu).length + (p.dropUntil u hu).length = p.length := by
  have h := SimpleGraph.Walk.take_spec p hu
  conv_rhs => rw [← h]
  exact (SimpleGraph.Walk.length_append _ _).symm

/-- Every vertex in takeUntil has x ≤ max x of the full walk. -/
lemma takeUntil_x_le_max {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support)
    (z : HexVertex) (hz : z ∈ (p.takeUntil u hu).support) :
    z.1 ≤ walk_max_x p := by
  exact walk_max_x_bound p z (SimpleGraph.Walk.support_takeUntil_subset p hu hz)

/-- Every vertex in dropUntil has x ≤ max x of the full walk. -/
lemma dropUntil_x_le_max {v w u : HexVertex}
    (p : hexGraph.Walk v w) (hu : u ∈ p.support)
    (z : HexVertex) (hz : z ∈ (p.dropUntil u hu).support) :
    z.1 ≤ walk_max_x p := by
  exact walk_max_x_bound p z (SimpleGraph.Walk.support_dropUntil_subset p hu hz)

/-! ## Half-plane walk counting

A half-plane walk (start has minimal x among all visited vertices)
of width T₀ can be decomposed into bridges.

For the counting inequality, we need:
- The bridge weights form a subset of {1,...,N}
- The walk length ≥ sum of bridge lengths

This section establishes the half-plane walk counting bound
by strong induction on the width. -/

-- Half-plane walk count: for walks from hexOrigin where hexOrigin
-- has minimal x, the total weighted count is bounded by the
-- bridge selection weight.
--
-- This is the key inductive step of the Hammersley-Welsh decomposition.
--
-- Informal proof: By strong induction on width T₀.
-- Base case T₀ = 0: the walk stays at x=0, so it IS a bridge of width 0.
-- Inductive step: Given a half-plane walk of width T₀ ≥ 1:
-- 1. Find the last vertex u with x = T₀ (maximal x)
-- 2. The walk from hexOrigin to u is a bridge of width T₀
-- 3. The remaining walk from u has width < T₀
-- 4. By IH, the remaining walk injects into bridge selections
-- 5. The full walk injects into bridge selections with widths in {1,...,T₀}
--
-- The full formalization requires the decomposition algorithm.
-- See the detailed proof outline in the docstring of
-- bridge_decomp_injection_from_algorithm below.

/-! ## The main bridge decomposition injection

We now combine the half-plane decomposition with walk splitting
to prove the full counting inequality. -/

/-- **The bridge decomposition counting inequality.**

    For 0 < x < xc (hence x < 1):
    ∑_{n=0}^{N} c_n x^n ≤ 2 · (∑_{S ⊆ range(N)} ∏_{T∈S} B_{T+1}^x)²

    Proof outline (Hammersley-Welsh):
    1. Each n-step SAW γ from hexOrigin has max x-coordinate M ≤ n ≤ N.
    2. Split γ at the first vertex with x = M into left part γ₁ and right part γ₂.
    3. Reversed γ₁ is a half-plane walk (start at x=M has maximal x).
       γ₂ is a half-plane walk (start at x=M has maximal x).
    4. Each half-plane walk decomposes into bridges by induction on width.
    5. Translating each bridge to start from hexOrigin gives origin bridges.
    6. The bridge widths form a subset of {1,...,N} (since max x ≤ N).
    7. Walk length n = left_length + right_length ≥ sum of bridge lengths
       (forgotten vertices between consecutive bridges add extra edges).
    8. Hence x^n ≤ ∏ x^{bridge_length} for x ≤ 1.
    9. The map (γ, vertex_choice) → (left bridges, right bridges) is injective:
       given the sequence of origin bridges and the starting point,
       the reverse procedure reconstructs the walk uniquely.
    10. Factor 2: accounts for 2 possible first-vertex choices from hexOrigin
        (the hexagonal lattice has 3 neighbors, but the mid-edge formulation
        in the paper gives 2; our vertex formulation allows a cruder bound).
    11. Therefore ∑ c_n x^n ≤ 2 · (∑_S ∏ B_{T+1}^x)². -/
theorem bridge_decomp_injection_from_algorithm
    {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, origin_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end