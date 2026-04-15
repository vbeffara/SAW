/-
# Winding properties on the honeycomb lattice

Key property: all turns on the honeycomb lattice are exactly ±1
(in units of π/3). This is the fundamental geometric fact underlying
the parafermionic observable proof.
-/

import Mathlib
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-- On the honeycomb lattice, the turn at any vertex in a self-avoiding
    walk is exactly ±1 (representing ±π/3).
    This is because the honeycomb lattice has degree 3, with edges
    separated by 2π/3, and a SAW must enter and exit via different edges. -/
lemma hexTurn_eq_pm_one (u v w : HexVertex)
    (huv : hexGraph.Adj u v) (hvw : hexGraph.Adj v w) (huw : u ≠ w) :
    hexTurn u v w = 1 ∨ hexTurn u v w = -1 := by
  unfold hexTurn hexEdgeDir; simp +decide [ huv, hvw, huw ];
  split_ifs <;> simp +decide [ * ] at *;
  all_goals unfold hexGraph at *; simp_all +decide [ SimpleGraph.adj_comm ] ;
  all_goals contrapose! huw; aesop;

end
