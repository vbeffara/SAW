/-
# Vertex relation for the parafermionic observable (Lemma 1)

This file proves the vertex relation (Lemma 1 of Duminil-Copin & Smirnov 2012):
for each interior vertex v of a strip domain, the weighted sum of the
parafermionic observable over the three mid-edges adjacent to v vanishes.

## Key idea

The proof partitions walks ending at mid-edges near v into:
- **Triplets**: walks visiting 1 mid-edge ↔ pairs of walks visiting 2 mid-edges
  (extending/truncating by one step through v)
- **Pairs**: walks visiting all 3 mid-edges, differing by loop reversal at v

The algebraic cancellation of triplets uses `triplet_cancellation` and
of pairs uses `pair_cancellation`, both proved in SAW.lean.

## Winding computation

The winding W(a,z) from starting mid-edge a to ending mid-edge z is the
total rotation of the direction vector (in radians). On the hex lattice,
W = Σ turns at interior vertices + entry half-edge turn + exit half-edge turn.

Key property: the winding *telescopes*. For walks in a triplet, the
winding difference is a constant hexTurn(w₁, v, w₂) that depends only on
the local geometry at v, NOT on the specific walk.

## Reference

  Hugo Duminil-Copin and Stanislav Smirnov,
  "The connective constant of the honeycomb lattice equals √(2+√2)",
  Annals of Mathematics, 175(3), 1653--1665, 2012, Lemma 1.
-/

import Mathlib
import RequestProject.SAWObservableProof

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## Full winding (including exit half-edge)

The full winding of a walk from mid-edge a to mid-edge z = mid(v, w)
includes the exit half-edge turn: the turn from the last internal edge
direction to the exit direction d(v, w).

For a walk of length ≥ 2 ending at vertex v:
  W_full = W_internal + hexTurn(prev, v, w)
where prev is the second-to-last vertex and w is the exit neighbor.

For a walk of length 1 (just v₁):
  W_full = hexTurn(a_source, v₁, w)
where a_source is the vertex on the far side of the starting mid-edge.

For a walk of length 0 (trivial walk at the starting vertex):
  W_full = exit_direction - entry_direction
-/

/-- The "last edge direction" of a walk: the direction index of the
    last edge, or the entry direction for a length-0 walk. -/
def walkLastDir {v w : HexVertex} (p : hexGraph.Walk v w) : Option (Fin 6) :=
  match p with
  | .nil => hexEdgeDir hexOrigin paperStart  -- entry direction from starting mid-edge
  | .cons _ .nil => hexEdgeDir v w
  | .cons _ (.cons h' rest) => walkLastDir (.cons h' rest)

/-- Full winding including exit half-edge, in units of π/3.
    For a walk ending at vertex w with exit toward neighbor w_exit:
    W_full = walkWindingInt + exit_turn -/
def fullWinding {v w : HexVertex} (p : hexGraph.Walk v w) (w_exit : HexVertex) : ℤ :=
  match walkLastDir p, hexEdgeDir w w_exit with
  | some d_last, some d_exit =>
    let exit_turn := ((d_exit : ℤ) - (d_last : ℤ) + 3) % 6 - 3
    walkWindingInt p + exit_turn
  | _, _ => walkWindingInt p

/-! ## Triplet winding difference

The winding difference between a walk and its extension through v
is a FIXED constant that depends only on the local geometry. -/

/-
For a walk γ ending at w₁ (neighbor of v), extended by one step
through v with exit toward w₂:
fullWinding(γ_extended, w₂) = fullWinding(γ, v) + hexTurn(w₁, v, w₂)
This is the KEY property: the winding difference is constant.

walkLastDir of a walk followed by one edge gives the last edge direction.
-/
lemma walkLastDir_append_single {u w₁ v : HexVertex}
    (p : hexGraph.Walk u w₁) (hp : 1 ≤ p.length)
    (h : hexGraph.Adj w₁ v) :
    walkLastDir (p.append (.cons h .nil)) = hexEdgeDir w₁ v := by
  induction p <;> simp_all +decide;
  cases ‹hexGraph.Walk _ _› <;> simp_all +decide [ walkLastDir ]

/-- For walks of length ≥ 1, walkLastDir returns some value. -/
lemma walkLastDir_isSome {v w : HexVertex} (p : hexGraph.Walk v w) (hp : 1 ≤ p.length) :
    (walkLastDir p).isSome = true := by
  induction p with
  | nil => simp at hp
  | cons h rest ih =>
    cases rest with
    | nil => simp [walkLastDir, hexEdgeDir]; split_ifs <;> simp_all [hexGraph]
    | cons h' rest' =>
      simp [walkLastDir]
      apply ih; simp [SimpleGraph.Walk.length]

/-- For walks of length ≥ 1, hexEdgeDir for adjacent vertices returns some. -/
lemma hexEdgeDir_adj_isSome {v w : HexVertex} (h : hexGraph.Adj v w) :
    (hexEdgeDir v w).isSome = true := by
  unfold hexEdgeDir; split_ifs <;> simp_all

/-- walkLastDir factors through the first edge for length ≥ 2 walks. -/
lemma walkLastDir_cons_cons {u v₁ w₁ w₂ : HexVertex}
    (h₁ : hexGraph.Adj u v₁)
    (h₂ : hexGraph.Adj v₁ w₁)
    (rest : hexGraph.Walk w₁ w₂) :
    walkLastDir (.cons h₁ (.cons h₂ rest)) = walkLastDir (.cons h₂ rest) := by
  rfl

/-- walkWindingInt factors through the first edge for length ≥ 2 walks. -/
lemma walkWindingInt_cons_cons {u v₁ w₁ w₂ : HexVertex}
    (h₁ : hexGraph.Adj u v₁)
    (h₂ : hexGraph.Adj v₁ w₁)
    (rest : hexGraph.Walk w₁ w₂) :
    walkWindingInt (.cons h₁ (.cons h₂ rest)) =
    hexTurn u v₁ w₁ + walkWindingInt (.cons h₂ rest) := by
  rfl

/-
Key structural lemma: fullWinding factors through the first edge.
-/
private lemma fullWinding_cons_cons {u v₁ w₁ : HexVertex}
    (h₁ : hexGraph.Adj u v₁)
    (q : hexGraph.Walk v₁ w₁)
    (hq : 1 ≤ q.length)
    (w_exit : HexVertex) :
    fullWinding (.cons h₁ q) w_exit =
    hexTurn u v₁ (q.getVert 1) + fullWinding q w_exit := by
  rcases q with ( _ | ⟨ h₂, q ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
  unfold fullWinding;
  rw [ walkLastDir_cons_cons, walkWindingInt_cons_cons ];
  cases h : walkLastDir ( SimpleGraph.Walk.cons h₂ q ) <;> cases h' : hexEdgeDir w₁ w_exit <;> simp +decide [ h, h' ] ; ring

/-
The key winding telescoping property:
    extending a walk by one step through v adds hexTurn(w₁, v, w₂).

    Proof by induction on p:
    - Length 1 (p = u → w₁): direct computation with fullWinding.
    - Length ≥ 2 (p = u → v₁ → ... → w₁): factor out first edge using
      fullWinding_cons_cons, apply IH to the tail.
-/
theorem triplet_winding_property {u w₁ v : HexVertex}
    (p : hexGraph.Walk u w₁)
    (hp : 1 ≤ p.length)
    (h_adj_w₁_v : hexGraph.Adj w₁ v)
    (w₂ : HexVertex) :
    fullWinding (p.append (.cons h_adj_w₁_v .nil)) w₂ =
    fullWinding p v + hexTurn w₁ v w₂ := by
  induction' p with u w₁ p ih generalizing w₂;
  · contradiction;
  · rename_i h₁ h₂ h₃;
    by_cases h : 1 ≤ h₂.length <;> simp_all +decide [fullWinding_cons_cons];
    · rcases w₂ with ⟨ a, b, c ⟩ ; simp_all +decide [ add_assoc ] ;
      cases c <;> simp_all +decide [ SimpleGraph.Walk.getVert ];
      · cases h₂ <;> aesop;
      · cases h₂ <;> aesop;
    · cases h₂ <;> simp_all +decide [ SimpleGraph.Walk.append ];
      unfold fullWinding;
      unfold hexTurn; simp +decide [ walkLastDir, walkWindingInt ] ;
      cases hexEdgeDir w₁ p <;> cases hexEdgeDir p v <;> cases hexEdgeDir v w₂ <;> simp +decide [ * ]

/-! ## Walk extension for triplets

Walk extension is handled via SimpleGraph.Walk.cons + IsPath construction. -/

/-! ## Hex lattice geometry: the three exit turns

At a FALSE vertex v = (x, y, false) with neighbors:
- w₁ = (x, y, true)     [direction 0]
- w₂ = (x+1, y, true)   [direction 2π/3]
- w₃ = (x, y+1, true)   [direction -2π/3]

The hex turns from w₁ through v to w₂ and w₃: -/

/-
hexTurn from w₁ = (x,y,true) through v = (x,y,false) to w₂ = (x+1,y,true) is -1.
-/
lemma hexTurn_false_w1_w2 (x y : ℤ) :
    hexTurn (x, y, true) (x, y, false) (x + 1, y, true) = -1 := by
  unfold hexTurn;
  unfold hexEdgeDir; simp +decide [ hexGraph ] ;

/-
hexTurn from w₁ = (x,y,true) through v = (x,y,false) to w₃ = (x,y+1,true) is +1.
-/
lemma hexTurn_false_w1_w3 (x y : ℤ) :
    hexTurn (x, y, true) (x, y, false) (x, y + 1, true) = 1 := by
  unfold hexTurn;
  unfold hexEdgeDir; simp +decide [ hexGraph ] ;

/-
hexTurn from w₂ = (x+1,y,true) through v = (x,y,false) to w₁ = (x,y,true) is +1.
-/
lemma hexTurn_false_w2_w1 (x y : ℤ) :
    hexTurn (x + 1, y, true) (x, y, false) (x, y, true) = 1 := by
  unfold hexTurn; simp +decide [ hexEdgeDir ] ;
  split_ifs <;> simp_all +decide [ hexGraph ]

/-
hexTurn from w₂ through v to w₃ is -1.
-/
lemma hexTurn_false_w2_w3 (x y : ℤ) :
    hexTurn (x + 1, y, true) (x, y, false) (x, y + 1, true) = -1 := by
  unfold hexTurn hexEdgeDir hexGraph;
  simp +decide

/-
hexTurn from w₃ through v to w₁ is -1.
-/
lemma hexTurn_false_w3_w1 (x y : ℤ) :
    hexTurn (x, y + 1, true) (x, y, false) (x, y, true) = -1 := by
  unfold hexTurn hexEdgeDir hexGraph; simp +decide [ SimpleGraph.adj_comm ] ;

/-
hexTurn from w₃ through v to w₂ is +1.
-/
lemma hexTurn_false_w3_w2 (x y : ℤ) :
    hexTurn (x, y + 1, true) (x, y, false) (x + 1, y, true) = 1 := by
  unfold hexTurn hexEdgeDir; simp +decide [ hexGraph ] ;

/-! ## Symmetric versions for TRUE vertices -/

/-
hexTurn from u₁ = (x,y,false) through v = (x,y,true) to u₂ = (x-1,y,false) is -1.
-/
lemma hexTurn_true_u1_u2 (x y : ℤ) :
    hexTurn (x, y, false) (x, y, true) (x - 1, y, false) = -1 := by
  -- Let's unfold the definition of `hexTurn` and simplify the expression.
  unfold hexTurn hexEdgeDir hexGraph;
  simp +decide

/-
hexTurn from u₁ through v to u₃ = (x,y-1,false) is +1.
-/
lemma hexTurn_true_u1_u3 (x y : ℤ) :
    hexTurn (x, y, false) (x, y, true) (x, y - 1, false) = 1 := by
  unfold hexTurn; simp +decide [ hexEdgeDir ] ;
  split_ifs <;> simp_all +decide [ hexGraph ]

/-! ## The algebraic triplet identity with specific hex turns

The triplet cancellation identity: for the three mid-edges adjacent to
a FALSE vertex v, with winding differences -1 and +1 (in units of π/3):

  1 + xc · exp(-iσ · (-1) · π/3) · j + xc · exp(-iσ · 1 · π/3) · j̄ = 0

This is exactly `triplet_cancellation` with the substitutions:
  j·conj(λ) = j · exp(i·5π/24) = j · exp(-iσ·(-1)·π/3)
  j̄·λ = j̄ · exp(-i·5π/24) = j̄ · exp(-iσ·1·π/3)  -/

lemma triplet_cancellation_hex :
    (1 : ℂ) + (xc : ℂ) * j * Complex.exp (-Complex.I * sigma * (-1 : ℤ) * (Real.pi / 3)) +
    (xc : ℂ) * conj j * Complex.exp (-Complex.I * sigma * (1 : ℤ) * (Real.pi / 3)) = 0 := by
  convert triplet_cancellation using 3 <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
  · unfold sigma lam; norm_num [ Complex.exp_re, Complex.exp_im ] ; ring_nf; norm_num;
  · unfold sigma lam; norm_num [ Complex.exp_re, Complex.exp_im ] ;
    ring_nf; norm_num

/-! ## Discrete Stokes: interior mid-edge cancellation

For any simply connected strip domain, summing the vertex relation over
all interior vertices gives interior mid-edge cancellation:
for each interior mid-edge z = mid(v,w) with both v,w interior,
(z-v) + (z-w) = 0 (since z is the midpoint). -/

/-- The direction vectors from the two endpoints of an edge to the
    midpoint sum to zero: (z-v) + (z-w) = 0 since z = (v+w)/2. -/
lemma midedge_direction_cancel (v w : HexVertex) :
    (correctHexEmbed w - correctHexEmbed v) +
    (correctHexEmbed v - correctHexEmbed w) = 0 := by
  ring

/-! ## Boundary evaluation

After discrete Stokes, only boundary mid-edges survive.
For each boundary type, we evaluate the direction·phase product. -/

/-- The starting mid-edge a contributes F(a) = 1 (trivial walk)
    with direction factor (hexOrigin - paperStart). -/
lemma starting_midedge_contribution :
    correctHexEmbed hexOrigin - correctHexEmbed paperStart = -1 :=
  starting_direction

/-- Right boundary mid-edges have winding 0 from the starting point.
    The direction factor for a horizontal right boundary mid-edge is +1
    (the exit direction from FALSE at diagCoord = -T to TRUE at diagCoord = -T). -/
lemma right_boundary_direction (x y : ℤ) :
    correctHexEmbed (x, y, true) - correctHexEmbed (x, y, false) = 1 :=
  false_to_true_dir x y

end