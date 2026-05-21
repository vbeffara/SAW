/-
# Strict Half-Plane Walk Infrastructure

Defines strict DownHP walks and proves basic properties.
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-- A SAW from paperStart where all non-start vertices have dc ∈ [-W, -1]. -/
def IsStrictDownHP (W : ℕ) (n : ℕ) (s : SAW paperStart n) : Prop :=
  ∀ v ∈ s.p.1.support, v ≠ paperStart →
    -(W : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ -1

instance (W n : ℕ) (s : SAW paperStart n) : Decidable (IsStrictDownHP W n s) := by
  unfold IsStrictDownHP; exact inferInstance

/-- Count of strict DownHP SAWs. -/
def strictHP (W n : ℕ) : ℕ :=
  Fintype.card { s : SAW paperStart n // IsStrictDownHP W n s }

/-
The only strict DownHP(0) SAW of length 0 is the trivial walk.
-/
lemma strictHP_zero_zero : strictHP 0 0 = 1 := by
  unfold strictHP;
  unfold IsStrictDownHP; simp +decide ;
  convert Fintype.card_eq_one_iff.mpr _;
  use ⟨ ⟨ paperStart, ⟨ SimpleGraph.Walk.nil, by
    simp +decide [ SimpleGraph.Walk.IsPath ] ⟩, rfl ⟩, by
    aesop ⟩;
  rintro ⟨ s, hs ⟩ ; rcases s with ⟨ w, p, l ⟩ ; rcases p with ⟨ p, hp ⟩ ; rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide ;
  · cases l;
  · cases l

/-
No strict DownHP(0) SAW of length ≥ 1 exists.
-/
lemma strictHP_zero_succ (n : ℕ) : strictHP 0 (n + 1) = 0 := by
  rw [ strictHP, Fintype.card_eq_zero_iff ];
  constructor;
  rintro ⟨ s, hs ⟩;
  have := hs ( s.p.1.getVert 1 ) ?_ ?_ <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
  · linarith;
  · grind +suggestions

end