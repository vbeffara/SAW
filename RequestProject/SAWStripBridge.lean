/-
# Bridge between strip identity and the main theorem

This file connects the strip identity (B_paper ≤ 1 from
SAWStripIdentityCorrect.lean) to the bridge partition bounds needed
for the main theorem (connective_constant_eq from SAWFinal.lean).

## Key results

1. `paper_bridge_partition`: The paper-compatible bridge partition
   (from paperStart in the diagonal strip).

2. `negDiagBridgeToSAW`: Paper bridges inject into SAWs from paperStart.

3. `neg_diag_bridge_endpoints_differ`: Bridges of different widths have
   different endpoints (by diagonal coordinate).

4. `saw_count_from_paperStart`: SAW count is vertex-independent.

## Architecture

The original Bridge definition uses column coordinates (x-coordinate),
while the paper's strip identity uses diagonal coordinates (x+y).
This file works with the paper's diagonal coordinates.
-/

import RequestProject.SAWDiagConnection
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Paper bridge partition function -/

/-- Paper bridge partition using edge-based weighting. -/
def paper_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : NegDiagOriginBridge T), x ^ b.1.walk.1.length

/-! ## Paper bridge to SAW injection -/

/-- Convert a NegDiagOriginBridge to a SAW from paperStart. -/
def negDiagBridgeToSAW {T : ℕ} (b : NegDiagOriginBridge T) :
    SAW paperStart b.1.walk.1.length :=
  match b with
  | ⟨⟨_, ev, walk, _, _, _⟩, rfl⟩ => ⟨ev, walk, rfl⟩

/-
The NegDiagBridge-to-SAW map is injective (as sigma types).
-/
lemma negDiagBridgeToSAW_injective (T : ℕ) :
    Function.Injective (fun b : NegDiagOriginBridge T =>
      (⟨b.1.walk.1.length, negDiagBridgeToSAW b⟩ : Σ n, SAW paperStart n)) := by
  rintro ⟨ b₁, hb₁ ⟩ ⟨ b₂, hb₂ ⟩ h;
  unfold negDiagBridgeToSAW at h;
  grind

/-- Bridges of different widths give SAWs with different endpoints. -/
lemma neg_diag_bridge_endpoints_differ {T₁ T₂ : ℕ} (hT : T₁ ≠ T₂)
    (b₁ : NegDiagOriginBridge T₁) (b₂ : NegDiagOriginBridge T₂) :
    b₁.1.end_v ≠ b₂.1.end_v := by
  intro h
  have h1 := b₁.1.end_right
  have h2 := b₂.1.end_right
  rw [h] at h1; omega

/-! ## SAW count vertex independence -/

/-- SAW count is the same from paperStart as from hexOrigin. -/
lemma saw_count_from_paperStart (n : ℕ) :
    Fintype.card (SAW paperStart n) = saw_count n :=
  saw_count_vertex_independent paperStart n

end