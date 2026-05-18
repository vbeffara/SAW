/-
# Hammersley-Welsh Decomposition using Re coordinate

The key insight: using the Re coordinate from the hex embedding
(correctHexEmbed) resolves the bipartite structure issue for the
bridge decomposition. Re values for TRUE and FALSE vertices at the
same diagCoord are DIFFERENT, ensuring distinct bridge widths.
-/

import Mathlib
import RequestProject.SAWPaperChain

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 400000

/-! ## Re coordinate for hex vertices -/

/-- The Re coordinate of a hex vertex, scaled to integers.
    We use 2*Re from correctHexEmbed to get integer values:
    FALSE(x,y) → -3(x+y)
    TRUE(x,y)  → -3(x+y) + 2
    This avoids rational arithmetic. -/
def hexReScaled (v : HexVertex) : ℤ :=
  if v.2.2 then
    -3 * (v.1 + v.2.1) + 2
  else
    -3 * (v.1 + v.2.1)

/-- hexReScaled of paperStart = 2 -/
lemma hexReScaled_paperStart : hexReScaled paperStart = 2 := by
  simp [hexReScaled, paperStart]

/-- hexReScaled of hexOrigin = 0 -/
lemma hexReScaled_hexOrigin : hexReScaled hexOrigin = 0 := by
  simp [hexReScaled, hexOrigin]

/-- Adjacent vertices have hexReScaled differing by at most 2. -/
lemma hexReScaled_adj_bound {v w : HexVertex} (h : hexGraph.Adj v w) :
    (hexReScaled w - hexReScaled v).natAbs ≤ 2 := by
  rcases v with ⟨vx, vy, vb⟩; rcases w with ⟨wx, wy, wb⟩
  rcases h with ⟨hv, hw, h3 | h3 | h3⟩ | ⟨hv, hw, h3 | h3 | h3⟩ <;>
    obtain ⟨h1, h2⟩ := h3 <;> simp_all [hexReScaled] <;> omega

/-- hexReScaled along a walk changes by at most 2*length. -/
lemma hexReScaled_walk_bound {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexReScaled w - hexReScaled v).natAbs ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hab := hexReScaled_adj_bound h
    simp [SimpleGraph.Walk.length_cons]
    omega

/-- hexReScaled strictly changes at every step: adjacent vertices have different
    hexReScaled values. This is the key property that resolves the "flat walk"
    issue for the bridge decomposition on the hexagonal lattice.

    Proof: The adjacency rules give hexReScaled changes of exactly {-2, -1, +1, +2},
    never 0. Specifically:
    - TRUE → FALSE: changes are {-2, -2, +1}
    - FALSE → TRUE: changes are {+2, +2, -1} -/
lemma hexReScaled_adj_ne {v w : HexVertex} (h : hexGraph.Adj v w) :
    hexReScaled v ≠ hexReScaled w := by
  rcases v with ⟨vx, vy, vb⟩; rcases w with ⟨wx, wy, wb⟩
  rcases h with ⟨hv, hw, h3 | h3 | h3⟩ | ⟨hv, hw, h3 | h3 | h3⟩ <;>
    obtain ⟨h1, h2⟩ := h3 <;> simp_all [hexReScaled] <;> omega

/-- hexReScaled values are always ≡ 0 or 2 (mod 3).
    TRUE vertices have hexReScaled ≡ 2 (mod 3).
    FALSE vertices have hexReScaled ≡ 0 (mod 3). -/
lemma hexReScaled_mod3 (v : HexVertex) :
    hexReScaled v % 3 = if v.2.2 then 2 else 0 := by
  simp [hexReScaled]
  cases v.2.2 <;> simp <;> omega

/-- Bridge endpoint has hexReScaled = 3T. -/
lemma hexReScaled_bridge_endpoint {v : HexVertex}
    (hd : v.1 + v.2.1 = -(T : ℤ)) (hf : v.2.2 = false) :
    hexReScaled v = 3 * T := by
  simp [hexReScaled, hf, hd]

/-- PaperInfStrip T constraint in terms of hexReScaled:
    All vertices v satisfy 0 ≤ hexReScaled v ≤ 3T.
    (This matches the Re constraint from the continuous embedding.) -/
lemma hexReScaled_in_strip {T : ℕ} {v : HexVertex} (hv : PaperInfStrip T v) :
    0 ≤ hexReScaled v ∧ hexReScaled v ≤ 3 * T := by
  unfold PaperInfStrip at hv
  simp [hexReScaled]
  cases hb : v.2.2 <;> simp [hb] at hv ⊢ <;> omega

end
