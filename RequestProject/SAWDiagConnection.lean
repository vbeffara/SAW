/-
# Connection between diagonal bridges and PaperSAW_B

The paper's strip identity bounds B_paper ≤ 1, where B_paper counts
SAWs from paperStart ending at the right boundary of the diagonal strip.
This file connects diagonal bridges (from SAWDiagBridge.lean) to
PaperSAW_B (from SAWStripIdentityCorrect.lean).

## Key insight: column vs diagonal bridges

The original Bridge definition uses column coordinates (x-coordinate),
while the paper's strips use diagonal coordinates (x+y). The strip
identity B_paper ≤ 1 holds for DIAGONAL strips, not column strips.
This file provides the diagonal bridge infrastructure needed to
correctly formalize the paper's argument.
-/

import RequestProject.SAWDiagBridge
import RequestProject.SAWStripIdentityProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Hex lattice reflection

The map (x,y,b) ↦ (-y,-x,¬b) is a graph automorphism of hexGraph
that reverses the diagonal coordinate: x+y ↦ -(x+y). -/

/-- Reflection of a hex vertex: (x,y,b) ↦ (-y,-x,¬b). -/
def hexReflect (v : HexVertex) : HexVertex :=
  (-v.2.1, -v.1, !v.2.2)

/-- hexReflect maps hexOrigin to paperStart. -/
lemma hexReflect_origin : hexReflect hexOrigin = paperStart := by
  simp [hexReflect, hexOrigin, paperStart]

/-- hexReflect maps paperStart to hexOrigin. -/
lemma hexReflect_paperStart : hexReflect paperStart = hexOrigin := by
  simp [hexReflect, hexOrigin, paperStart]

/-- hexReflect is an involution. -/
lemma hexReflect_involution (v : HexVertex) : hexReflect (hexReflect v) = v := by
  obtain ⟨x, y, b⟩ := v
  simp [hexReflect]

/-- hexReflect is injective. -/
lemma hexReflect_injective : Function.Injective hexReflect := by
  intro v w h
  have := congr_arg hexReflect h
  rwa [hexReflect_involution, hexReflect_involution] at this

/-- hexReflect reverses the diagonal coordinate. -/
lemma hexReflect_diag (v : HexVertex) :
    (hexReflect v).1 + (hexReflect v).2.1 = -(v.1 + v.2.1) := by
  obtain ⟨x, y, b⟩ := v
  simp [hexReflect]

/-- hexReflect flips the sublattice. -/
lemma hexReflect_bool (v : HexVertex) :
    (hexReflect v).2.2 = !v.2.2 := by
  obtain ⟨x, y, b⟩ := v
  simp [hexReflect]

/-
hexReflect preserves adjacency.
-/
lemma hexReflect_adj {v w : HexVertex} (h : hexGraph.Adj v w) :
    hexGraph.Adj (hexReflect v) (hexReflect w) := by
  cases h;
  · rcases ‹_› with ⟨ h₁, h₂, h₃ | h₃ | h₃ ⟩ <;> unfold hexGraph <;> simp +decide [ *, hexReflect ];
    · omega;
    · omega;
  · unfold hexReflect; unfold hexGraph; aesop;

/-! ## Negative diagonal bridges

To match the paper's convention (strips going in the negative diagonal
direction), we define "negative diagonal bridges". -/

/-- A negative diagonal bridge: walk from x+y=0 to x+y=-T
    staying in -T ≤ x+y ≤ 0. -/
structure NegDiagBridge (T : ℕ) where
  start_v : HexVertex
  end_v : HexVertex
  walk : hexGraph.Path start_v end_v
  start_left : start_v.1 + start_v.2.1 = 0
  end_right : end_v.1 + end_v.2.1 = -(T : ℤ)
  in_strip : ∀ v ∈ walk.1.support, -(T : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0

/-- Negative diagonal bridge from paperStart. -/
def NegDiagOriginBridge (T : ℕ) := {b : NegDiagBridge T // b.start_v = paperStart}

/-- A negative diagonal bridge of width T has length ≥ T. -/
theorem neg_diag_bridge_length_ge_width (T : ℕ) (b : NegDiagBridge T) :
    T ≤ b.walk.1.length := by
  have h := hexGraph_walk_sum_bound_neg b.walk.1
  have h_start := b.start_left
  have h_end := b.end_right
  omega

/-! ## PaperSAW_B embeds into NegDiagOriginBridge

Every PaperSAW_B walk (from paperStart ending at FALSE with x+y=-T
in PaperFinStrip T L) determines a negative diagonal bridge from
paperStart of width T. -/

/-- A PaperSAW_B walk gives a NegDiagBridge. -/
def paperSAW_B_to_negDiagBridge (T L : ℕ) (s : PaperSAW_B T L) :
    NegDiagOriginBridge T :=
  ⟨{
    start_v := paperStart
    end_v := s.saw.w
    walk := s.saw.p
    start_left := by simp [paperStart]
    end_right := s.end_right.1
    in_strip := by
      intro v hv
      have hstrip := s.in_strip v hv
      unfold PaperFinStrip PaperInfStrip at hstrip
      obtain ⟨x, y, b⟩ := v
      cases b <;> simp_all <;> omega
  }, rfl⟩

/-- The map preserves walk length. -/
lemma paperSAW_B_to_negDiagBridge_length (T L : ℕ) (s : PaperSAW_B T L) :
    (paperSAW_B_to_negDiagBridge T L s).1.walk.1.length = s.len := by
  simp [paperSAW_B_to_negDiagBridge, s.saw.l]

/-
The map is injective.
-/
lemma paperSAW_B_to_negDiagBridge_injective (T L : ℕ) :
    Function.Injective (paperSAW_B_to_negDiagBridge T L) := by
  intro s₁ s₂ h
  cases s₁; cases s₂; simp_all +decide [ NegDiagOriginBridge ] ;
  rename_i k hk₁ hk₂ hk₃ l hl₁ hl₂ hl₃;
  cases hk₁ ; cases hl₁ ; simp_all +decide [ paperSAW_B_to_negDiagBridge ];
  grind

/-! ## Negative diagonal bridge partition ≤ 1

This follows from B_paper_le_one by passage to the limit. -/

/-- The negative diagonal bridge partition function. -/
def neg_diag_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : NegDiagOriginBridge T), x ^ b.1.walk.1.length

/-! ## Important architectural note

NegDiagBridge uses the constraint -T ≤ x+y ≤ 0 for ALL vertices,
but PaperInfStrip uses TIGHTER sublattice-dependent constraints:
- TRUE: -(T-1) ≤ x+y ≤ 0
- FALSE: -T ≤ x+y ≤ -1

This means NegDiagBridge is COARSER than PaperInfStrip:
- FALSE vertices with x+y = 0 are in NegDiagBridge but NOT in PaperInfStrip
- TRUE vertices with x+y = -T are in NegDiagBridge but NOT in PaperInfStrip

Consequence: NegDiagOriginBridge has MORE walks than PaperSAW_B.
So B_paper ≤ 1 does NOT directly imply neg_diag_bridge_partition ≤ 1.

The correct approach uses PaperSAW_B (which matches PaperInfStrip)
throughout the proof. The strip identity bounds B_paper directly.

Similarly, the column bridge partition (origin_bridge_partition from
SAWBridgeFix.lean) uses x-coordinate strips, which have DIFFERENT
boundary geometry from the paper's diagonal strips. The strip identity
B_paper ≤ 1 does not directly imply origin_bridge_partition ≤ 1.

To close the proof, one should either:
1. Formalize the vertex relation + telescoping argument to prove
   B_paper_le_one_direct directly, or
2. Define the correct bridge partition matching PaperInfStrip and
   restructure the downstream proofs accordingly.
-/

end