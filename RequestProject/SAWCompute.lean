/-
# Concrete SAW computations and bridge existence

Concrete computations for the formalization of:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Content

1. **Bridge existence**: There exists at least one bridge of width 1
   starting from hexOrigin.
2. **Neighbor classification of hexOrigin**: Which neighbors have x=1.
3. **Numerical bounds on √(2+√2) and x_c**.
4. **Bridge length bounds for origin bridges**.
-/

import RequestProject.SAWBridgeFix
import RequestProject.SAWElementary
import RequestProject.SAWDecomp

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Bridge existence

The bridge of width 1 constructed in SAWBridgeFix.lean (bridge_width1)
gives bridges of width 1. The single-edge walk from (0,0,false) to
(1,0,true) is the simplest example.
-/

/-- The bridge of width 1 starting at hexOrigin. -/
def origin_bridge_1 : OriginBridge 1 :=
  ⟨bridge_width1 0, rfl⟩

/-- The origin bridge partition for width 1 includes a positive term:
    the bridge_width1 0 contributes xc^1 = xc > 0. -/
lemma origin_bridge_1_weight :
    xc ^ (origin_bridge_1.1.walk.1.length) = xc := by
  simp [origin_bridge_1, bridge_width1, width1_path, width1_walk]

/-- There exists at least one origin bridge of width 1. -/
lemma origin_bridge_1_exists : Nonempty (OriginBridge 1) :=
  ⟨origin_bridge_1⟩

/-! ## Neighbor classification of hexOrigin

The hexagonal lattice vertex hexOrigin = (0,0,false) has exactly 3 neighbors:
(0,0,true), (1,0,true), and (0,1,true). Among these, only (1,0,true) has
x-coordinate equal to 1.
-/

/-- The only neighbor of hexOrigin with x-coordinate 1 is (1,0,true). -/
lemma hexOrigin_neighbor_x1 {w : HexVertex} (h : hexGraph.Adj hexOrigin w) (hw : w.1 = 1) :
    w = (1, 0, true) := by
  unfold hexOrigin hexGraph at h
  simp only at h
  rcases w with ⟨wx, wy, wb⟩
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-- The neighbors of hexOrigin with x-coordinate 0 are (0,0,true) and (0,1,true). -/
lemma hexOrigin_neighbor_x0 {w : HexVertex} (h : hexGraph.Adj hexOrigin w) (hw : w.1 = 0) :
    w = (0, 0, true) ∨ w = (0, 1, true) := by
  unfold hexOrigin hexGraph at h
  simp only at h
  rcases w with ⟨wx, wy, wb⟩
  rcases h with ⟨h1, h2, h3 | h3 | h3⟩ | ⟨h1, h2, h3 | h3 | h3⟩ <;>
    simp_all <;> omega

/-! ## Numerical bounds on √(2+√2) and x_c -/

/-- √(2+√2) > 1. This follows from 2 + √2 > 1. -/
lemma sqrt_two_add_sqrt_two_gt_one :
    1 < Real.sqrt (2 + Real.sqrt 2) := by
  rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [Real.sqrt_nonneg 2])

/-- √(2+√2) < 2. This follows from 2+√2 < 4, i.e., √2 < 2. -/
lemma sqrt_two_add_sqrt_two_lt_two :
    Real.sqrt (2 + Real.sqrt 2) < 2 := by
  rw [Real.sqrt_lt'] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two]

/-! ## Bridge length bounds -/

/-- For an origin bridge of width T, the length is at least T. -/
lemma origin_bridge_length_ge (T : ℕ) (b : OriginBridge T) :
    T ≤ b.1.walk.1.length :=
  bridge_length_ge_width T b.1

/-! ## The partition function Z(x) is non-negative for x ≥ 0. -/

lemma Z_nonneg' {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Z x :=
  Z_nonneg hx

/-! ## Note on the bridge partition and summability

The origin_bridge_partition T xc = ∑' (b : OriginBridge T), xc^{ℓ(b)}
is the bridge partition function B_T^{x_c} from the paper.

Its key properties (B_T ≤ 1 and B_T ≥ c/T) follow from the strip
identity (Lemma 2). Without the strip identity, we cannot even
establish summability of the bridge weights, and hence cannot prove
origin_bridge_partition 1 xc > 0 (the tsum convention sets it to 0
for non-summable functions).

The abstract proof structure for the lower bound (Z(xc) = ∞) uses:
1. Strip identity → B_T ≤ 1 (hence summability)
2. Strip identity + recurrence → B_T ≥ c/T (with c > 0)
3. Harmonic series divergence → Σ B_T = ∞
4. Bridge injection → Z(xc) ≥ Σ B_T = ∞

These are all proved abstractly in SAWDecomp.lean and SAWProof.lean.
The gap is the concrete strip identity (strip_identity_concrete in
SAWFiniteStrip.lean).
-/

end
