/-
# Hammersley-Welsh Bridge Decomposition: Core Infrastructure

The canonical decomposition of SAWs into bridges.
-/

import Mathlib
import RequestProject.SAWDiagProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Diagonal coordinate -/

/-- The diagonal coordinate of a hex vertex: x + y. -/
def hexDiagCoord (v : HexVertex) : ℤ := v.1 + v.2.1

lemma hexDiagCoord_paperStart : hexDiagCoord paperStart = 0 := by
  simp [hexDiagCoord, paperStart]

/-
Adjacent vertices differ in diagCoord by at most 1.
-/
lemma hexDiagCoord_adj_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    |hexDiagCoord w - hexDiagCoord v| ≤ 1 := by
  rcases h with ⟨hv, hw⟩;
  · unfold hexDiagCoord; aesop;
  · unfold hexDiagCoord; aesop;

/-- PaperBridge endpoint has diagCoord -T. -/
lemma paperBridge_endpoint_dc {T : ℕ} (b : PaperBridge T) :
    hexDiagCoord b.end_v = -(T : ℤ) :=
  b.end_right.1

/-! ## Walk support has extrema -/

/-- Walk support is nonempty. -/
lemma walk_support_nonempty {v w : HexVertex} (p : hexGraph.Walk v w) :
    p.support ≠ [] := SimpleGraph.Walk.support_ne_nil p

/-! ## Bridge diagCoord range -/

/-- All vertices in a PaperBridge have diagCoord between -T and 0. -/
lemma paperBridge_dc_range {T : ℕ} (b : PaperBridge T)
    (v : HexVertex) (hv : v ∈ b.walk.1.support) :
    -(T : ℤ) ≤ hexDiagCoord v ∧ hexDiagCoord v ≤ 0 := by
  have hs := b.in_strip v hv
  unfold PaperInfStrip at hs
  unfold hexDiagCoord
  cases hb : v.2.2 <;> simp [hb] at hs <;> omega

/-! ## Bridge partition functions are translation invariant

Bridges starting from different vertices at the same diagCoord level
have the same partition function. This allows us to use paper_bridge_partition
regardless of the bridge's starting point. -/

-- The partition function paper_bridge_partition T x counts bridges from
-- paperStart to diagCoord -T. By the translation invariance of the hex lattice,
-- this equals the bridge partition from any vertex at diagCoord 0.
/-! ## Product-powerset identity -/

/-
∑_{S ⊆ range N} ∏_{T ∈ S} a_T = ∏_{T ∈ range N} (1 + a_T).
-/
lemma finset_powerset_prod_eq' {N : ℕ} {a : ℕ → ℝ} :
    ∑ S ∈ (Finset.range N).powerset, ∏ T ∈ S, a T =
    ∏ T ∈ Finset.range N, (1 + a T) := by
  simp +decide [ add_comm, Finset.prod_add ]

/-! ## Bridge decomposition counting bound

This is the core of the Hammersley-Welsh argument:

Given a SAW γ from the origin of length n, we decompose it into bridges.
The decomposition gives a pair of subsets (S₁, S₂) of {1, ..., n},
where S₁ contains the bridge widths of the forward half and S₂ contains
the bridge widths of the backward half. Different SAWs give different
bridge sequences, so this is at most 2-to-1.

The weight bound:
  x^n = Π_{bridge b} x^{length(b)}
      ≤ Π_{T ∈ S₁} B_T(x) · Π_{T ∈ S₂} B_T(x)

Summing over all SAWs:
  Σ c_n x^n ≤ 2 · (Σ_{S ⊆ range N} Π_{T ∈ S} B_{T+1}(x))²
            = 2 · (Π_{T ∈ range N} (1 + B_{T+1}(x)))²
-/

/-- The Hammersley-Welsh counting bound.

    **Proof outline:**
    1. Each SAW γ of length ≤ N from the origin determines a pair of
       finite subsets (S₁, S₂) ⊆ {0, ..., N-1} via the bridge decomposition.
    2. The bridge decomposition is injective (up to factor 2): given
       (S₁, S₂) and the bridge sequences, the SAW is uniquely determined.
    3. The weight x^n of γ is at most ∏_{T ∈ S₁} B_{T+1}(x) · ∏_{T ∈ S₂} B_{T+1}(x).
    4. Summing over all possible (S₁, S₂):
       Σ c_n x^n ≤ 2 · (Σ_{S} ∏_{T ∈ S} B_{T+1}(x))². -/
theorem hw_counting_bound {x : ℝ} (hx : 0 < x) (hxc : x < xc) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (saw_count n : ℝ) * x ^ n ≤
    2 * (∑ S ∈ (Finset.range N).powerset,
      ∏ T ∈ S, paper_bridge_partition (T + 1) x) ^ 2 := by
  sorry

end