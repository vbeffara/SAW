/-
# Corrected bridge partition and connection to SAW counts

This file fixes a definitional issue with `bridge_partition` from SAWBridge.lean:
the original definition sums over ALL bridges of width T (including all vertical
translates), making the tsum always 0 for T ≥ 1 since Bridge T is infinite.

We fix this by:
1. Constructing explicit bridges to show Bridge T is infinite
2. Proving bridge_partition T xc = 0 (due to non-summability)
3. Proving `lower_bound_from_strip_identity` is vacuously true
4. Defining a corrected bridge partition (from hexOrigin)
5. Connecting the corrected partition to saw_count

## Reference

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

The paper defines B_T^x as a sum over walks from a FIXED starting mid-edge a
to the right boundary β. The corrected definition reflects this.
-/

import RequestProject.SAWBridge

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Construction of bridges of width 1

For each y ∈ ℤ, there is a bridge of width 1:
  (0, y, false) → (1, y, true)
This single-edge path stays within the strip [0,1] and crosses
from left to right boundary.
-/

/-- Adjacency: (0, y, false) is adjacent to (1, y, true) in hexGraph. -/
lemma width1_adj (y : ℤ) : hexGraph.Adj (0, y, false) (1, y, true) := by
  left; exact ⟨rfl, rfl, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩

/-- The single-edge walk from (0,y,false) to (1,y,true). -/
def width1_walk (y : ℤ) : hexGraph.Walk (0, y, false) (1, y, true) :=
  SimpleGraph.Walk.cons (width1_adj y) SimpleGraph.Walk.nil

/-- The walk has length 1. -/
@[simp] lemma width1_walk_length (y : ℤ) : (width1_walk y).length = 1 := rfl

/-- The walk is a path (no repeated vertices). -/
lemma width1_walk_isPath (y : ℤ) : (width1_walk y).IsPath := by
  refine ⟨⟨?_⟩, ?_⟩
  · -- edges_nodup
    simp [width1_walk]
  · -- support_nodup
    simp [width1_walk, SimpleGraph.Walk.support]

/-- The single-edge path from (0,y,false) to (1,y,true). -/
def width1_path (y : ℤ) : hexGraph.Path (0, y, false) (1, y, true) :=
  ⟨width1_walk y, width1_walk_isPath y⟩

/-- A bridge of width 1 for each y ∈ ℤ. -/
def bridge_width1 (y : ℤ) : Bridge 1 where
  start_v := (0, y, false)
  end_v := (1, y, true)
  walk := width1_path y
  start_left := rfl
  end_right := rfl
  in_strip := by
    intro v hv
    simp [width1_path, width1_walk, SimpleGraph.Walk.support] at hv
    rcases hv with rfl | rfl <;> omega

/-- The bridge_width1 construction is injective. -/
lemma bridge_width1_injective : Function.Injective bridge_width1 := by
  intro y1 y2 h
  have : (bridge_width1 y1).start_v = (bridge_width1 y2).start_v := by rw [h]
  simp [bridge_width1] at this
  exact this

/-- Bridge 1 is infinite (has infinitely many elements). -/
instance : Infinite (Bridge 1) :=
  Infinite.of_injective bridge_width1 bridge_width1_injective

/-- The length of a bridge_width1 bridge is 1. -/
lemma bridge_width1_length (y : ℤ) :
    (bridge_width1 y).walk.1.length = 1 := by
  simp [bridge_width1, width1_path, width1_walk]

/-! ## Non-summability of the bridge partition function

Since Bridge 1 is infinite and each bridge has positive weight xc^{length},
the sum is not summable, hence bridge_partition 1 xc = 0 by convention.
-/

/-- The bridge weight function on Bridge 1 is not summable:
    there are infinitely many bridges with weight xc > 0. -/
lemma bridge1_not_summable :
    ¬ Summable (fun b : Bridge 1 => xc ^ b.walk.1.length) := by
  intro h
  -- Compose with the injection bridge_width1 : ℤ → Bridge 1
  have h1 : Summable (fun y : ℤ => xc ^ (bridge_width1 y).walk.1.length) :=
    h.comp_injective bridge_width1_injective
  -- Each term equals xc (since length = 1)
  have h2 : Summable (fun _ : ℤ => xc) := by
    refine h1.congr fun y => ?_
    rw [bridge_width1_length]
    simp
  -- But the constant function xc > 0 is not summable on ℤ
  rw [summable_const_iff] at h2
  exact absurd h2 (ne_of_gt xc_pos)

/-- bridge_partition 1 xc = 0, because the underlying tsum is not summable. -/
lemma bridge_partition_1_eq_zero : bridge_partition 1 xc = 0 :=
  tsum_eq_zero_of_not_summable bridge1_not_summable

/-! ## lower_bound_from_strip_identity is vacuously true

The hypothesis `hbridge_lower` requires bridge_partition T xc ≥ c/T > 0,
but bridge_partition 1 xc = 0, so c ≤ 0, contradicting c > 0.
-/

/-- The hypothesis of lower_bound_from_strip_identity is contradictory:
    bridge_partition 1 xc = 0 but the hypothesis requires it to be ≥ c > 0. -/
lemma bridge_lower_hyp_false :
    ¬ (∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ bridge_partition T xc) := by
  intro ⟨c, hc, hT⟩
  have h1 := hT 1 le_rfl
  rw [Nat.cast_one, div_one] at h1
  linarith [bridge_partition_1_eq_zero]

/-! ## Corrected bridge partition (from hexOrigin)

The paper defines B_T^x as a sum over walks from a FIXED starting
mid-edge a to the right boundary β. We define this correctly as
the sum over bridges starting from hexOrigin.
-/

/-- A bridge of width T starting from hexOrigin. -/
def OriginBridge (T : ℕ) := {b : Bridge T // b.start_v = hexOrigin}

/-- The corrected bridge partition function: sum over bridges from hexOrigin.
    This corresponds to the paper's B_T^x. -/
def origin_bridge_partition (T : ℕ) (x : ℝ) : ℝ :=
  ∑' (b : OriginBridge T), x ^ b.1.walk.1.length

/-! ## Connection: origin bridges inject into SAWs from hexOrigin

Each origin bridge of width T determines a unique SAW from hexOrigin.
This is the key connection between bridge_partition and saw_count.
-/

/-- Bridges of different widths have different endpoints.
    A bridge of width T ends at a vertex with first coordinate T. -/
lemma bridge_endpoints_differ {T₁ T₂ : ℕ} (hT : T₁ ≠ T₂)
    (b₁ : Bridge T₁) (b₂ : Bridge T₂) :
    b₁.end_v ≠ b₂.end_v := by
  intro h
  have h1 := b₁.end_right  -- end_v.1 = T₁
  have h2 := b₂.end_right  -- end_v.1 = T₂
  rw [h] at h1
  omega

/-! ## The corrected strip identity

With the corrected bridge partition, the strip identity becomes:
  1 = c_α · A_T + origin_bridge_partition T xc + c_ε · E_T

where A_T and E_T are the (corrected) partition functions for walks
ending on the left and top/bottom boundaries respectively.

This requires defining walks restricted to strip domains,
which is the main remaining formalization task.
-/

/- SUPERSEDED: origin_bridge_upper_bound is FALSE for x-coordinate bridges.
   For T=1, origin_bridge_partition 1 xc ≈ 1.76 > 1.
   The correct bound uses diagonal bridges (paper_bridge_partition T xc ≤ 1/xc)
   in SAWDiagProof.lean. -/
theorem origin_bridge_upper_bound (T : ℕ) (hT : 1 ≤ T) :
    origin_bridge_partition T xc ≤ 1 := by
  sorry -- FALSE for x-coordinate bridges, see SAWPaperChain.lean

/- SUPERSEDED by paper_bridge_lower_bound in SAWPaperChain.lean,
   which uses diagonal bridges matching the paper's convention. -/
theorem origin_bridge_lower_bound :
    ∃ c > 0, ∀ T : ℕ, 1 ≤ T → c / T ≤ origin_bridge_partition T xc := by
  sorry

/-! ## The lower bound: Z(xc) = ∞

Using the corrected bridge partition:
- origin_bridge_partition T xc ≥ c/T (for all T ≥ 1)
- Z(xc) ≥ Σ_T origin_bridge_partition T xc (bridges inject into SAWs)
- Σ c/T = ∞ (harmonic series)
Hence Z(xc) = ∞.
-/

/- SUPERSEDED by Z_xc_diverges_corrected in SAWPaperChain.lean. -/
theorem Z_xc_diverges :
    ¬ Summable (fun n => (saw_count n : ℝ) * xc ^ n) := by
  sorry

/-! ## The upper bound: Z(x) < ∞ for x < xc

The Hammersley-Welsh bridge decomposition gives:
  Z(x) ≤ 2 · ∏_{T≥1} (1 + origin_bridge_partition T x)²

Since origin_bridge_partition T xc ≤ 1 and bridges of width T have
length ≥ T, for x < xc:
  origin_bridge_partition T x ≤ (x/xc)^T

The product converges since x/xc < 1.
-/

/- SUPERSEDED by hw_summable_corrected in SAWPaperChain.lean.
   Uses paper bridges (diagonal strips) instead of x-coordinate bridges. -/
theorem hammersley_welsh_injection :
    ∀ x, 0 < x → x < xc →
      Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  sorry

end
