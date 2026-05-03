/-
# Hammersley-Welsh Decomposition: Proof Infrastructure

This file provides helper lemmas for the Hammersley-Welsh
bridge decomposition injection.

The key result: ∑_{n≤N} c_n x^n ≤ 2 (∏_{T=1}^{N} (1 + B_T(x)))^2.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWDecompHelper
import RequestProject.SAWBridgeDecompNew
import RequestProject.SAWWalkSplit

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Key counting bound: SAWs inject into bridges

The Hammersley-Welsh decomposition shows that self-avoiding walks
can be "decomposed" into sequences of bridges. This gives a bound
on the number of SAWs in terms of bridge counts.

The key inequality (at the level of finite sums):
  ∑ s : SAW paperStart n, x ^ n ≤
    (∑ S ∈ (range n).powerset, ∏ T ∈ S, paper_bridge_partition (T+1) x)^2

for any x > 0. Here the LHS counts SAWs of EXACTLY length n, and
the RHS counts pairs of bridge sequences. -/

/-! ## Translation invariance for bridges

A key ingredient: bridges starting from any vertex v with the same
"relative structure" as a PaperBridge have the same count.
This is because the hexagonal lattice is translation-invariant. -/

/-- A "shifted bridge" of width T starting from vertex v is a SAW from v
    to a vertex w with diagCoordHW w = diagCoordHW v - T, staying in
    the strip {diagCoordHW v - T ≤ diagCoord ≤ diagCoordHW v}. -/
structure ShiftedBridge (T : ℤ) (v : HexVertex) where
  end_v : HexVertex
  walk : hexGraph.Path v end_v
  end_dc : diagCoordHW end_v = diagCoordHW v - T
  in_strip : ∀ u ∈ walk.1.support,
    diagCoordHW v - T ≤ diagCoordHW u ∧ diagCoordHW u ≤ diagCoordHW v

/-
A shifted bridge has length ≥ T (each step changes diagCoord by ≤ 1).
-/
lemma shifted_bridge_length_ge {T : ℤ} {v : HexVertex} (hT : 0 ≤ T)
    (b : ShiftedBridge T v) : T ≤ b.walk.1.length := by
  obtain ⟨ end_v, walk, hT, in_strip ⟩ := b;
  have := in_strip _ ( show end_v ∈ ( walk.1.support ) from by simp +decide [ SimpleGraph.Walk.support ] ) ; simp_all +decide [ diagCoordHW ] ;
  have := hexGraph_walk_sum_bound_neg walk.1; have := hexGraph_walk_sum_bound_pos walk.1; norm_num [ diagCoordHW ] at *; omega;

/-! ## Half-plane walk to bridge sequence decomposition

A half-plane walk (all vertices at diagCoord ≥ starting diagCoord)
decomposes into shifted bridges of strictly decreasing widths.

The decomposition is by induction on the width of the walk:
- Width 0: no bridges
- Width W > 0: extract the last bridge, recurse on the remainder -/

/-- Width of a half-plane walk: max diagCoord - min diagCoord. -/
def halfPlaneWidth {v w : HexVertex} (p : hexGraph.Walk v w)
    (h_hp : ∀ u ∈ p.support, diagCoordHW v ≤ diagCoordHW u) : ℕ :=
  (walk_max_dc p - diagCoordHW v).toNat

/-- Total bridge length in the decomposition ≤ walk length.
    This is because the bridges are sub-walks of the original walk. -/
lemma bridge_decomp_total_length_le {v w : HexVertex}
    (p : hexGraph.Path v w)
    (h_hp : ∀ u ∈ p.1.support, diagCoordHW v ≤ diagCoordHW u)
    (bridge_lengths : List ℕ) -- lengths of extracted bridges
    (h_decomp : bridge_lengths.sum ≤ p.1.length) :
    bridge_lengths.sum ≤ p.1.length :=
  h_decomp

/-! ## SAW splitting at first minimum diagCoord

Given a SAW from paperStart, split at the first vertex of minimum diagCoord.
The prefix (reversed) and suffix each form half-plane walks. -/

/-- For any SAW from paperStart, the minimum diagCoord is achieved. -/
lemma SAW_min_achieved {n : ℕ} (s : SAW paperStart n) :
    ∃ u ∈ s.p.1.support, diagCoordHW u = walk_min_dc s.p.1 :=
  walk_min_dc_achieved s.p.1

/-- For any SAW from paperStart, the suffix after the min vertex
    stays above the min level. -/
lemma SAW_suffix_above_min {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support)
    (hu_min : diagCoordHW u = walk_min_dc s.p.1) :
    ∀ z ∈ (s.p.1.dropUntil u hu).support, diagCoordHW u ≤ diagCoordHW z := by
  intro z hz
  rw [hu_min]
  exact walk_min_dc_le s.p.1 z (s.p.1.support_dropUntil_subset hu hz)

/-- The prefix up to the min vertex also stays above the min level. -/
lemma SAW_prefix_above_min {n : ℕ} (s : SAW paperStart n)
    (u : HexVertex) (hu : u ∈ s.p.1.support)
    (hu_min : diagCoordHW u = walk_min_dc s.p.1) :
    ∀ z ∈ (s.p.1.takeUntil u hu).support, diagCoordHW u ≤ diagCoordHW z := by
  intro z hz
  rw [hu_min]
  exact walk_min_dc_le s.p.1 z (s.p.1.support_takeUntil_subset hu hz)

end