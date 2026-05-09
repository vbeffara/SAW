/-
# Bridge Extraction for the Hammersley-Welsh Decomposition

Defines the bridge extraction algorithm for half-plane walks on the
hex lattice and proves key properties needed for paper_bridge_decomp_injection.

## Algorithm (from the paper)

Given a half-plane SAW γ̃ (start has minimal diagCoord):
1. If width = 0, no bridges.
2. If width T₀ ≥ 1:
   a. Find the LAST vertex with maximal diagCoord.
   b. The walk up to this vertex forms a bridge of width T₀.
   c. Skip one vertex (determined by the bridge).
   d. The remaining walk is a half-plane walk of width < T₀.
   e. Recurse.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWHWDecompHelper

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Half-plane walk definition -/

/-- The maximum diagCoord in a walk's support. -/
def walk_max_dc {v w : HexVertex} (p : hexGraph.Walk v w) : ℤ :=
  (p.support.map diagCoordHW).foldl max (diagCoordHW v)

/-- The width of a half-plane walk: max diagCoord - min diagCoord. -/
def hp_walk_width {v w : HexVertex} (p : hexGraph.Walk v w) : ℕ :=
  ((walk_max_dc p) - (walk_min_dc p)).toNat

/-
walk_max_dc is at least the diagCoord of any vertex in the walk.
-/
lemma walk_max_dc_ge {v w : HexVertex} (p : hexGraph.Walk v w)
    (u : HexVertex) (hu : u ∈ p.support) :
    diagCoordHW u ≤ walk_max_dc p := by
  have h_walk_max : ∀ (l : List ℤ), ∀ (x : ℤ), x ∈ l → x ≤ List.foldl max (List.head! l) l := by
    intro l x hx;
    induction' l using List.reverseRecOn with l IH <;> simp_all +decide [ List.foldl_assoc ];
    cases l <;> aesop;
  convert h_walk_max ( p.support.map diagCoordHW ) ( diagCoordHW u ) _ using 1;
  · cases p <;> simp +decide [ walk_max_dc ];
  · exact List.mem_map.mpr ⟨ u, hu, rfl ⟩

/-
walk_max_dc is achieved by some vertex.
-/
lemma walk_max_dc_achieved {v w : HexVertex} (p : hexGraph.Walk v w) :
    ∃ u ∈ p.support, diagCoordHW u = walk_max_dc p := by
  -- The maximum of a finite set of integers is achieved by some element in the set.
  have h_max_achieved : ∀ (s : List ℤ), s ≠ [] → ∃ u ∈ s, u = s.foldl max (s.head!) := by
    intro s hs_nonempty;
    induction s using List.reverseRecOn <;> simp_all +decide;
    cases ‹List ℤ› <;> simp_all +decide [ List.foldl_append ];
    grind;
  convert h_max_achieved ( p.support.map diagCoordHW ) _ using 1;
  · unfold walk_max_dc;
    cases p <;> simp +decide [ List.foldl_map ];
    grind;
  · cases p <;> aesop

/-
For a SAW in PaperInfStrip T starting from paperStart,
    the max diagCoord is 0 (= diagCoord of paperStart).
-/
lemma strip_walk_max_dc_le_zero {w : HexVertex} {T : ℕ}
    (p : hexGraph.Walk paperStart w) (hp : p.IsPath)
    (hs : ∀ v ∈ p.support, PaperInfStrip T v) :
    walk_max_dc p ≤ 0 := by
  -- By definition of `walk_max_dc`, we know that `walk_max_dc p` is the maximum value of `diagCoordHW` over the support of `p`.
  have h_max_le_zero : ∀ u ∈ p.support, diagCoordHW u ≤ 0 := by
    -- By definition of `PaperInfStrip`, we know that for any vertex `u` in the support of `p`, `u` satisfies `PaperInfStrip T u`.
    intro u hu
    specialize hs u hu;
    unfold PaperInfStrip at hs;
    unfold diagCoordHW; split_ifs at hs <;> linarith;
  -- By definition of `walk_max_dc`, we know that `walk_max_dc p` is the maximum value of `diagCoordHW` over the support of `p`, which is a list.
  have h_max_le_zero_list : ∀ (l : List ℤ), (∀ u ∈ l, u ≤ 0) → (l.foldl max (diagCoordHW paperStart)) ≤ 0 := by
    intro l hl; induction' l using List.reverseRecOn with l ih <;> aesop;
  exact h_max_le_zero_list _ fun u hu => by aesop;

/-
Adjacent vertices on hex lattice change diagCoord by at most 1.
-/
lemma hex_adj_diagCoord_diff {v w : HexVertex} (h : hexGraph.Adj v w) :
    |diagCoordHW w - diagCoordHW v| ≤ 1 := by
  obtain ⟨ hv₁, hv₂ ⟩ := h;
  · unfold diagCoordHW; aesop;
  · unfold diagCoordHW; aesop

end