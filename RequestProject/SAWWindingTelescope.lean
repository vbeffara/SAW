/-
# The winding of a hexagonal walk telescopes

`hexWalkWinding L` is a sum of turning angles `arg (dₖ₊₁ / dₖ)`, one per interior
vertex of `L`.  Each summand is congruent, modulo `2π`, to
`arg dₖ₊₁ - arg dₖ`, so the whole sum telescopes:

  `hexWalkWinding L ≡ arg (last direction) - arg (first direction)   (mod 2π)`.

This is `hexWalkWinding_angle_eq`, stated in `Real.Angle = ℝ / 2πℤ`.

It is exactly half of the geometric input needed by the boundary evaluation of
the strip identity: it pins the winding of a configuration modulo `2π` purely
from its final mid-edge (the first direction being the fixed initial mid-edge
`a`).  The remaining half — that the winding does not make extra full turns —
is a genuinely topological statement about self-avoiding walks in a simply
connected domain.
-/

import Mathlib
import RequestProject.SAWPairWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-- The direction of the last edge of the list `v₀ :: rest`. -/
def hexLastDir : HexVertex → List HexVertex → ℂ
  | _, [] => 1
  | v₀, [v₁] => correctHexEmbed v₁ - correctHexEmbed v₀
  | _, v₁ :: v₂ :: rest => hexLastDir v₁ (v₂ :: rest)

@[simp] lemma hexLastDir_singleton (v₀ v₁ : HexVertex) :
    hexLastDir v₀ [v₁] = correctHexEmbed v₁ - correctHexEmbed v₀ := rfl

@[simp] lemma hexLastDir_cons_cons (v₀ v₁ v₂ : HexVertex) (rest : List HexVertex) :
    hexLastDir v₀ (v₁ :: v₂ :: rest) = hexLastDir v₁ (v₂ :: rest) := rfl

/-- Consecutive vertices of the list have distinct embeddings.  This is the
only hypothesis the telescoping needs; it holds for the vertex list of any
walk, since adjacent vertices are distinct. -/
def HexDistinctChain : List HexVertex → Prop
  | [] | [_] => True
  | v₀ :: v₁ :: rest => correctHexEmbed v₀ ≠ correctHexEmbed v₁ ∧ HexDistinctChain (v₁ :: rest)

lemma HexDistinctChain.tail {v₀ : HexVertex} {rest : List HexVertex}
    (h : HexDistinctChain (v₀ :: rest)) : HexDistinctChain rest := by
  cases rest with
  | nil => trivial
  | cons v₁ r => exact h.2

lemma hexLastDir_ne_zero : ∀ (v₀ : HexVertex) (rest : List HexVertex), rest ≠ [] →
    HexDistinctChain (v₀ :: rest) → hexLastDir v₀ rest ≠ 0 := by
  intro v₀ rest
  induction rest generalizing v₀ with
  | nil => intro h; exact absurd rfl h
  | cons v₁ r ih =>
    intro _ hchain
    cases r with
    | nil => exact sub_ne_zero_of_ne (Ne.symm hchain.1)
    | cons v₂ r' => exact ih v₁ (by simp) hchain.2

/-- **The telescoping law.**  Modulo `2π`, the winding of a hexagonal walk is
the difference between the direction angles of its last and first edges. -/
theorem hexWalkWinding_angle_eq :
    ∀ (v₀ v₁ : HexVertex) (rest : List HexVertex),
      HexDistinctChain (v₀ :: v₁ :: rest) →
      ((hexWalkWinding (v₀ :: v₁ :: rest) : Real.Angle))
        = (Complex.arg (hexLastDir v₀ (v₁ :: rest)) : Real.Angle)
          - (Complex.arg (correctHexEmbed v₁ - correctHexEmbed v₀) : Real.Angle) := by
  intro v₀ v₁ rest
  induction rest generalizing v₀ v₁ with
  | nil =>
    intro _
    simp [hexWalkWinding]
  | cons v₂ r ih =>
    intro hchain
    have hd₁ : correctHexEmbed v₁ - correctHexEmbed v₀ ≠ 0 :=
      sub_ne_zero_of_ne (Ne.symm hchain.1)
    have hd₂ : correctHexEmbed v₂ - correctHexEmbed v₁ ≠ 0 :=
      sub_ne_zero_of_ne (Ne.symm hchain.2.1)
    have hstep : hexWalkWinding (v₀ :: v₁ :: v₂ :: r)
        = Complex.arg ((correctHexEmbed v₂ - correctHexEmbed v₁) /
            (correctHexEmbed v₁ - correctHexEmbed v₀))
          + hexWalkWinding (v₁ :: v₂ :: r) := rfl
    rw [hstep, Real.Angle.coe_add, ih v₁ v₂ hchain.2,
      Complex.arg_div_coe_angle hd₂ hd₁, hexLastDir_cons_cons]
    abel

/-- The vertex list of a walk is a `HexDistinctChain`. -/
lemma hexDistinctChain_of_isChain :
    ∀ (L : List HexVertex), List.IsChain hexGraph.Adj L → HexDistinctChain L := by
  intro L
  induction L with
  | nil => intro _; trivial
  | cons v₀ rest ih =>
    intro h
    cases rest with
    | nil => trivial
    | cons v₁ r =>
      obtain ⟨hadj, hrest⟩ := List.isChain_cons_cons.1 h
      exact ⟨fun heq => (hex_embed_sub_ne_zero' v₀ v₁ hadj) (by rw [heq]; ring), ih hrest⟩

lemma hexDistinctChain_of_walk_support {u w : HexVertex} (p : hexGraph.Walk u w) :
    HexDistinctChain p.support :=
  hexDistinctChain_of_isChain _ p.isChain_adj_support

/-! ## Appending a vertex -/

lemma hexLastDir_snoc : ∀ (v₀ : HexVertex) (L : List HexVertex) (b : HexVertex),
    hexLastDir v₀ (L ++ [b])
      = correctHexEmbed b - correctHexEmbed ((v₀ :: L).getLast (by simp)) := by
  intro v₀ L
  induction L generalizing v₀ with
  | nil => intro b; simp
  | cons x L' ih =>
    intro b
    obtain ⟨v₂, rest, hsplit⟩ : ∃ v₂ rest, L' ++ [b] = v₂ :: rest := by
      cases L' <;> simp
    have h1 : hexLastDir v₀ ((x :: L') ++ [b]) = hexLastDir x (L' ++ [b]) := by
      rw [List.cons_append, hsplit, hexLastDir_cons_cons, ← hsplit]
    rw [h1, ih x b, List.getLast_cons_cons]

lemma HexDistinctChain.snoc : ∀ (L : List HexVertex) (hL : L ≠ []) (b : HexVertex),
    HexDistinctChain L →
    correctHexEmbed (L.getLast hL) ≠ correctHexEmbed b →
    HexDistinctChain (L ++ [b]) := by
  intro L
  induction L with
  | nil => intro hL; exact absurd rfl hL
  | cons x L' ih =>
    intro _ b hchain hlast
    cases L' with
    | nil => exact ⟨by simpa using hlast, trivial⟩
    | cons y L'' =>
      refine ⟨hchain.1, ih (by simp) b hchain.2 ?_⟩
      rwa [List.getLast_cons_cons] at hlast

end
