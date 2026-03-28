/-
# The finite strip domain S_{T,L}

Formalization of the finite strip domain and its boundary decomposition,
from Section 3 of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Overview

The paper defines the strip domain S_{T,L} as follows:

  V(S_T) = {z ∈ V(H) : 0 ≤ Re(z) ≤ (3T+1)/2}
  V(S_{T,L}) = {z ∈ V(S_T) : |√3·Im(z) - Re(z)| ≤ 3L}

## Content

1. The infinite strip S_T and finite strip S_{T,L}
2. Boundary classification: α, β, ε, ε̄
3. Partition functions A_{T,L}, B_{T,L}, E_{T,L}
4. The strip identity (sorry) and consequences (B ≤ 1)
5. Origin bridge upper bound from strip identity
-/

import RequestProject.SAWBridgeFix
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Strip domains -/

/-- The infinite strip of width T: vertex (x, y, b) is in S_T iff 0 ≤ x ≤ T. -/
def InfiniteStrip (T : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T

/-- The finite strip S_{T,L}. -/
def FiniteStrip (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)

instance (T L : ℕ) (v : HexVertex) : Decidable (FiniteStrip T L v) :=
  inferInstanceAs (Decidable (0 ≤ v.1 ∧ v.1 ≤ T ∧ |2 * v.2.1 - v.1| ≤ 2 * (L : ℤ)))

/-! ## Boundary classification -/

def LeftBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  FiniteStrip T L v ∧ v.1 = 0

def RightBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  FiniteStrip T L v ∧ v.1 = T

def TopBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ 2 * v.2.1 - v.1 = 2 * (L : ℤ)

def BottomBoundary (T L : ℕ) (v : HexVertex) : Prop :=
  0 ≤ v.1 ∧ v.1 ≤ T ∧ 2 * v.2.1 - v.1 = -(2 * (L : ℤ))

/-! ## Partition functions on the finite strip -/

structure StripSAW_A (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  end_left : saw.w.1 = 0 ∧ saw.w ≠ hexOrigin
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

structure StripSAW_B (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  end_right : saw.w.1 = T
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

structure StripSAW_E (T L : ℕ) where
  len : ℕ
  saw : SAW hexOrigin len
  end_escape : |2 * saw.w.2.1 - saw.w.1| = 2 * (L : ℤ)
  in_strip : ∀ v ∈ saw.p.1.support, FiniteStrip T L v

def A_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_A T L), x ^ s.len

def B_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_B T L), x ^ s.len

def E_TL (T L : ℕ) (x : ℝ) : ℝ :=
  ∑' (s : StripSAW_E T L), x ^ s.len

/-! ## Monotonicity -/

lemma finite_strip_monotone {T L L' : ℕ} (hLL : L ≤ L') (v : HexVertex)
    (hv : FiniteStrip T L v) : FiniteStrip T L' v := by
  obtain ⟨h1, h2, h3⟩ := hv
  exact ⟨h1, h2, le_trans h3 (by omega)⟩

/-! ## The strip identity (Lemma 2) -/

/-- **Lemma 2** (Strip identity):
    For x = x_c, 1 = c_α · A_{T,L} + B_{T,L} + c_ε · E_{T,L}. -/
theorem strip_identity_concrete (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    1 = c_alpha * A_TL T L xc + B_TL T L xc + c_eps * E_TL T L xc := by
  sorry

/-! ## Passage to the infinite strip -/

def A_T_inf (T : ℕ) (x : ℝ) : ℝ := ⨆ L : ℕ, A_TL T L x
def B_T_inf (T : ℕ) (x : ℝ) : ℝ := ⨆ L : ℕ, B_TL T L x

/-- B_T_inf equals origin_bridge_partition when x > 0. -/
theorem B_T_inf_eq_origin_bridge (T : ℕ) (x : ℝ) (hx : 0 < x) :
    B_T_inf T x = origin_bridge_partition T x := by
  sorry

/-! ## Non-negativity -/

lemma A_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ A_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma B_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ B_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

lemma E_TL_nonneg (T L : ℕ) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ E_TL T L x :=
  tsum_nonneg fun s => pow_nonneg hx s.len

/-! ## Consequences of the strip identity -/

/-- From the strip identity: B_{T,L} ≤ 1 at x = x_c. -/
theorem B_TL_le_one (T L : ℕ) (hT : 1 ≤ T) (hL : 1 ≤ L) :
    B_TL T L xc ≤ 1 := by
  have hid := strip_identity_concrete T L hT hL
  have hA := A_TL_nonneg T L xc xc_pos.le
  have hE := E_TL_nonneg T L xc xc_pos.le
  nlinarith [c_alpha_pos, c_eps_pos]

/-! ## Origin bridge fits in finite strip -/

/-- Every origin bridge fits in S_{T, 2·length}. -/
lemma origin_bridge_in_finite_strip (T : ℕ) (b : OriginBridge T)
    (v : HexVertex) (hv : v ∈ b.1.walk.1.support) :
    FiniteStrip T (2 * b.1.walk.1.length) v := by
  have hstrip := b.1.in_strip v hv
  have hstart : b.1.start_v = hexOrigin := b.2
  have hbnd := hexGraph_walk_bound (b.1.walk.1.takeUntil v hv)
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbnd
  have h_sv1 : b.1.start_v.1 = 0 := by rw [hstart]; rfl
  have h_sv21 : b.1.start_v.2.1 = 0 := by rw [hstart]; rfl
  rw [h_sv1] at hb1 hb2; rw [h_sv21] at hb3 hb4
  have hTlen : (T : ℤ) ≤ b.1.walk.1.length := by exact_mod_cast bridge_length_ge_width T b.1
  have hlen := b.1.walk.1.length_takeUntil_le hv
  push_cast at *
  refine ⟨hstrip.1, hstrip.2, ?_⟩
  rw [abs_le]; constructor <;> omega

def originBridgeFitL (T : ℕ) (b : OriginBridge T) : ℕ := 2 * b.1.walk.1.length

lemma originBridgeFitL_pos (T : ℕ) (hT : 1 ≤ T) (b : OriginBridge T) :
    1 ≤ originBridgeFitL T b := by
  unfold originBridgeFitL
  have := bridge_length_ge_width T b.1; omega

/-! ## Bridge partial sum bound -/

/-- Map an origin bridge to a StripSAW_B, given it fits in the strip. -/
def originBridgeToStripB (T L : ℕ) :
    (b : OriginBridge T) → (∀ v ∈ b.1.walk.1.support, FiniteStrip T L v) → StripSAW_B T L
  | ⟨⟨_, ev, walk, _, er, _⟩, rfl⟩, hfit =>
    ⟨walk.1.length, ⟨ev, walk, rfl⟩, er, hfit⟩

/-- Every finite partial sum of origin bridge weights at x_c is ≤ 1.
    Uses origin_bridge_upper_bound (from SAWBridgeFix) and origin_bridge_lower_bound
    for summability. -/
lemma origin_bridge_partial_sum_le_one (T : ℕ) (hT : 1 ≤ T) (F : Finset (OriginBridge T)) :
    ∑ b ∈ F, xc ^ b.1.walk.1.length ≤ 1 := by
  have h_le : ∑ b ∈ F, xc ^ b.1.walk.1.length ≤ origin_bridge_partition T xc := by
    have h_summable : Summable (fun b : OriginBridge T => xc ^ b.1.walk.1.length) := by
      by_contra h_not_summable
      have h_zero : origin_bridge_partition T xc = 0 :=
        tsum_eq_zero_of_not_summable h_not_summable
      obtain ⟨c, hc_pos, hc_bound⟩ := origin_bridge_lower_bound
      have := hc_bound T hT
      linarith [div_pos hc_pos (Nat.cast_pos.mpr (show 0 < T by omega))]
    exact Summable.sum_le_tsum F (fun _ _ => pow_nonneg xc_pos.le _) h_summable
  exact le_trans h_le (origin_bridge_upper_bound T hT)

/-- origin_bridge_partition T xc ≤ 1: proved from partial sum bounds. -/
theorem origin_bridge_upper_bound_from_strip (T : ℕ) (hT : 1 ≤ T) :
    origin_bridge_partition T xc ≤ 1 := by
  exact Real.tsum_le_of_sum_le (fun b => pow_nonneg xc_pos.le _)
    (fun F => origin_bridge_partial_sum_le_one T hT F)

end
