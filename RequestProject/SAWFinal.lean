/-
# Final proof assembly: The connective constant of the honeycomb lattice

This file imports the full proof chain and assembles the final results:

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012.

## Import chain (corrected)

```
SAW.lean               — Core definitions, constants, algebraic identities
├─ SAWSubmult.lean      — Submultiplicativity: c_{n+m} ≤ c_n · c_m
│  └─ SAWMain.lean      — Fekete's lemma → connective constant is a limit
│     └─ SAWBridge.lean — Bridge defs, partition function, connective_constant_eq_from_bounds
│        └─ SAWBridgeFix.lean — OriginBridge definition
│           └─ SAWStripIdentityCorrect.lean — PaperBridge, B_paper_le_one_direct
│              └─ SAWDiagBridge.lean → SAWDiagConnection.lean → SAWDiagProof.lean
│                 └─ SAWPaperChain.lean — connective_constant_eq_corrected (main theorem)
└─ SAWDecomp.lean       — Quadratic recurrence, abstract bridge bounds
```

## Results proved here

1. `connective_constant_eq`: μ = √(2+√2) — the main theorem
2. `connective_constant_eq_inv_xc`: μ = xc⁻¹
3. `connective_constant_le_two'`: μ ≤ 2
4. `partition_function_diverges_above_xc'`: Z(x) = ∞ for x > xc
5. `partition_function_converges_below_xc'`: Z(x) < ∞ for 0 < x < xc

## Remaining sorry's

The main theorem depends on three independent sorry chains:

1. **`pair_winding_relation`** (SAWPairCancellation.lean) — The turning number
   argument for loop-reversed pairs on the hex lattice. CORRECTED to allow both
   orderings (clockwise/counterclockwise loops). The winding relation follows
   from the discrete turning number theorem (`hex_closed_trail_turning_number`
   in SAWTurningNumber.lean). Extensive winding infrastructure is proved:
   additivity, reversal, suffix trail conditions, suffix winding negation.

2. **`B_paper_le_one_strip`** (SAWStripIdentityCorrect.lean) — The core bound
   B_paper(T,L,xc) ≤ 1 from the parafermionic observable (Lemma 2 of the paper).
   This requires the discrete Stokes argument: summing the vertex relation over
   all interior vertices, cancelling interior mid-edges, and evaluating boundary
   contributions. The vertex relation (Lemma 1) is proved modulo #1.

3. **`infinite_strip_identity`** (SAWRecurrenceProof.lean) — The identity
   1 = c_α·A_inf + xc·B for the infinite strip. This follows from the finite
   strip identity (Lemma 2) by taking L→∞. Same dependency as #2.

4. **`hex_closed_trail_turning_number`** (SAWTurningNumber.lean) — NEW.
   The discrete Gauss-Bonnet theorem: a simple closed hex trail has total
   turning ±2π. This is the deepest unproved mathematical fact.

The Hammersley-Welsh decomposition chain is FULLY PROVED (sorry-free).

## Preparation files (not on critical path but needed for future steps)

The following files contain infrastructure for the discrete Stokes argument
and the turning number theorem. They are imported here to ensure they are
part of the build:
- `SAWDiscreteStokes` — Abstract discrete Stokes framework
- `SAWStokesAbstract` — Abstract combinatorial Stokes lemma
- `SAWWindingLemma` — Winding append/extension lemmas
- `SAWWindingReverse` — Additional winding reversal results
- `SAWWindingDecomp` — Winding decomposition for pair walks (suffix trail, reversal)
- `SAWTurningNumber` — Turning number theorem for hex trails (sorry'd)
- `SAWStripAlgebra` — Algebraic identities for the strip boundary evaluation
- `SAWObservableSum` — Observable as formal sum over trails
- `SAWCancellationProved` — Key helper lemmas for vertex relation
- `SAWVertexRelation` — Vertex relation infrastructure
- `SAWPairWindingRelation` — Alternative pair cancellation via winding
- `SAWHWExtraFinal` — Extra walk generating function bounds
- `SAWHWExtraSumProof` — Infrastructure for extra walk bounds
- `SAWMainNew` — Alternative proof path via infinite_strip_identity only

## Dead branches (explicitly marked)

The following sorry's are NOT on the critical path for the main theorem:
- `trail_vertex_relation` (SAWCancellationIdentity.lean) — uses StripTrail
  (non-fresh trails), superseded by `fresh_vertex_relation`
- `triplet_part_zero` / `pair_part_zero` (SAWTrailVertexRelation.lean) —
  uses non-fresh trail decomposition, superseded by fresh versions
- `strip_observable_summable` (SAWStripObservable.lean) — summability of
  strip observable, not needed for the main theorem
- `hex_simple_closed_trail_winding` (SAWWindingDiff.lean) — general turning
  number theorem, would be sufficient for `pair_winding_relation` but the
  specific pair winding is all that's needed
- `finite_strip_identity_from_vr` (SAWStripIdentityFromVR.lean) — the finite
  strip identity from the vertex relation, currently not connected to the
  main chain due to import structure; equivalent to `B_paper_le_one_strip`
-/

-- Main proof chain
import RequestProject.SAWPaperChain

-- Vertex relation chain (proved modulo pair_winding_relation)
import RequestProject.SAWStripIdentityFromVR

-- Winding infrastructure (preparation for pair_winding_relation)
import RequestProject.SAWWindingDiff
import RequestProject.SAWWindingLemma
import RequestProject.SAWWindingReverse
import RequestProject.SAWPairWindingRelation
import RequestProject.SAWPairWindingProof
import RequestProject.SAWWindingDecomp
import RequestProject.SAWTurningNumber

-- Discrete Stokes infrastructure (preparation for strip identity)
import RequestProject.SAWStripObservable
import RequestProject.SAWDiscreteStokes
import RequestProject.SAWStokesAbstract
import RequestProject.SAWStripAlgebra
import RequestProject.SAWObservableSum

-- Vertex relation infrastructure
import RequestProject.SAWCancellationProved
-- Note: SAWVertexRelation has a name conflict (redefines trueNeighbors)
-- and is a dead branch superseded by SAWObservableDef + SAWPathVertexRelation

-- Hammersley-Welsh extra bounds
import RequestProject.SAWHWExtraFinal
import RequestProject.SAWHWExtraSumProof

-- Alternative proof path
import RequestProject.SAWMainNew

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- **Main Theorem** (Duminil-Copin & Smirnov, 2012):
    The connective constant of the hexagonal lattice equals √(2+√2). -/
theorem connective_constant_eq :
    connective_constant = Real.sqrt (2 + Real.sqrt 2) :=
  connective_constant_eq_corrected

/-- Equivalent formulation: the connective constant equals 1/x_c. -/
theorem connective_constant_eq_inv_xc :
    connective_constant = xc⁻¹ := by
  rw [connective_constant_eq, xc_inv]

/-- The connective constant is at most 2.
    Immediate from the main theorem since √(2+√2) < 2. -/
theorem connective_constant_le_two' : connective_constant ≤ 2 := by
  rw [connective_constant_eq]
  exact Real.sqrt_le_iff.mpr ⟨by positivity,
    by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]⟩

/-- The partition function Z(x) diverges for x > x_c. -/
theorem partition_function_diverges_above_xc' :
    ∀ x > xc, ¬ Summable (fun n => (saw_count n : ℝ) * x ^ n) := by
  intro x hx
  have hmu_x_gt_1 : connective_constant * x > 1 := by
    rw [connective_constant_eq_inv_xc]
    rw [inv_mul_eq_div, gt_iff_lt, lt_div_iff₀] <;>
      nlinarith [xc_pos]
  have hcn_ge_mu_n : ∀ n ≥ 1, (saw_count n : ℝ) ≥ connective_constant ^ n :=
    fun n hn => saw_count_ge_cc_pow n hn
  have hcn_xn_ge_1 : ∀ n ≥ 1, (saw_count n : ℝ) * x ^ n ≥ 1 := by
    intro n hn
    calc (1 : ℝ) ≤ (connective_constant * x) ^ n := one_le_pow₀ hmu_x_gt_1.le
      _ = connective_constant ^ n * x ^ n := by ring
      _ ≤ (saw_count n : ℝ) * x ^ n :=
          mul_le_mul_of_nonneg_right (hcn_ge_mu_n n hn)
            (pow_nonneg (le_trans xc_pos.le hx.le) _)
  exact fun h => absurd h.tendsto_atTop_zero fun H =>
    absurd (le_of_tendsto_of_tendsto tendsto_const_nhds H
      (Filter.eventually_atTop.mpr ⟨1, fun n hn => hcn_xn_ge_1 n hn⟩))
      (by norm_num)

/-- The partition function Z(x) converges for 0 < x < x_c. -/
theorem partition_function_converges_below_xc' {x : ℝ}
    (hx : 0 < x) (hxc : x < xc) :
    Summable (fun n => (saw_count n : ℝ) * x ^ n) :=
  hw_summable_corrected hx hxc

end
