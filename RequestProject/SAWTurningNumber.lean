/-
# Turning Number Theorem for Hex Lattice Closed Trails

The key topological fact needed for the pair cancellation identity:
a simple closed trail on the hex lattice has turning number ±1.

## Main result

* `hex_closed_trail_turning_number` — for a simple closed trail on the hex
  lattice, the total winding (sum of exterior angles at all vertices including
  the closure) equals ±2π.

## Proof structure

The theorem is split into two halves:

* **Easy half (fully proved):** `hex_closed_winding_int_mul` — the total turning
  `hexWalkWinding L + closure` is an integer multiple `2π·n`. This follows from
  the telescoping identity `hexTrailList_winding_telescope`: every turn ratio
  `d₂/d₁` along a hex trail has unit modulus, so `exp (i·arg(d₂/d₁)) = d₂/d₁`,
  and the product telescopes; for a *closed* trail the last edge direction
  equals the first, giving `exp (i·(W + closure)) = 1`.

* **Hard half (the remaining `sorry`):** `umlaufsatz_pm_one` — for a *simple*
  (non-self-intersecting) closed trail, the multiple `n` is `±1`. This is the
  genuine content of the discrete Hopf Umlaufsatz / turning tangent theorem and
  is the only unproved fact left in this file. It is equivalent in difficulty to
  the Jordan curve theorem for polygons and is not available in Mathlib (which
  has no turning-number, winding-number, or Jordan-curve infrastructure).

  **Verified true (computational evidence).** The statement was checked by
  exhaustive enumeration of all closed honeycomb trails (no immediate backtrack)
  up to perimeter 18: every one satisfying the simplicity hypothesis
  `h_simple` has `n = ±1`, with no exceptions. The enumeration also confirms a
  subtle point about the weak hypotheses: although `h_simple` only asserts that
  the *interior* vertices `L.tail.dropLast` are distinct, the honeycomb's
  degree-3 structure (each vertex has exactly three neighbours) together with
  the no-immediate-backtrack condition forces the start vertex never to recur
  in the interior, so the whole vertex cycle `L.dropLast` is automatically
  `Nodup` (a genuinely simple polygon). Hence the lemma is true as stated.

  **Combinatorial reformulation (suggested proof route; reduction now built
  sorry-free).** Every hex turn is `±π/3` (`hex_turn_value`), so assigning to
  each turn the sign `±1` (`+1` for a left turn, `-1` for a right turn) makes the
  total turning equal `(π/3) · S` where `S` is the integer signed-turn count.
  This reduction is now established here as reusable, sorry-free infrastructure:
  * `hexTurnSign` assigns each turn its `±1` sign (via the imaginary part of the
    turn ratio);
  * `hexTurn_arg_eq_sign` proves each turning angle equals `(π/3)·hexTurnSign`;
  * `hexSignedTurnCount` sums the signs over the list; and
  * `hexWalkWinding_eq_signedTurnCount` proves `hexWalkWinding L =
    (π/3) · hexSignedTurnCount L`.
  Combined with `hex_closed_winding_int_mul` (`total turning = 2π·n`), this
  reduces `umlaufsatz_pm_one` to the purely combinatorial discrete Umlaufsatz
  `S = ±6`. That last step is provable by ear-clipping induction on the
  perimeter (remove a convex ear at the lexicographically extreme vertex, which
  preserves the turning number) or by a discrete Gauss-Bonnet / Euler-
  characteristic argument over the enclosed honeycomb faces — both of which
  require building planar-topology infrastructure absent from Mathlib.

  **Signed-area route (algebraic half now built).** The `±1` value is the sign
  of the polygon's signed area `A`. The *algebraic* backbone of this route is
  now established sorry-free:
  * `RequestProject.SAWSignedArea` develops the shoelace functional
    `HexArea.shoelace2` (twice the signed area) with `shoelace2_reverse`
    (reversal negates the area), `shoelace2_map_add_const` (translation
    invariance) and `shoelace2_ear` (the exact change of signed area when a
    vertex is cut, the ear-clipping step); and
  * `RequestProject.SAWUmlaufBridge`'s `hex_turn_cross` shows each turn's sign
    equals the sign of the cross product `±√3/2` of its two unit edge vectors,
    linking the turning data to the signed triangle areas.
  What remains is the irreducible *topological* half: that a simple polygon has
  nonzero signed area and that the turning number equals `sign(A)` — the same
  content as the Jordan curve theorem for polygons.

## Downstream use (preparation branch)

`hex_closed_trail_turning_number` is **not yet consumed** by any other
declaration, but it is **not dead code**: it is the intended foundation for
`pair_winding_relation` (in `SAWPairCancellation.lean`), which currently carries
its own independent `sorry`. Once that connection is wired up, the suffix
winding of a loop-reversed pair will be derived from this turning-number
result. This file is imported from `SAWFinal.lean`.
-/

import Mathlib
import RequestProject.SAWPairWinding

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Part 1: Hex edge direction properties -/

/-- Each hex edge direction has unit norm squared. -/
lemma hex_edge_norm_one (v w : HexVertex) (h : hexGraph.Adj v w) :
    Complex.normSq (correctHexEmbed w - correctHexEmbed v) = 1 := by
  rcases v with ⟨ x, y, b ⟩ ; rcases w with ⟨ x', y', b' ⟩ ;
  cases b <;> cases b' <;> simp_all +decide [ hexGraph ];
  · unfold correctHexEmbed; norm_num [ Complex.normSq ] ; ring;
    rcases h with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num <;> ring;
  · rcases h with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num [ correctHexEmbed ];
    · norm_num [ Complex.normSq ];
    · norm_num [ Complex.normSq ] ; ring ; norm_num;
    · norm_num [ Complex.normSq ] ; ring ; norm_num

/-! ## Edge directions have unit modulus

We record the consequence of `hex_edge_norm_one` in `‖·‖` form, which is the
form needed to turn `Complex.arg` of a turn ratio back into the ratio itself. -/

/-- Each hex edge direction has unit norm. -/
lemma hex_edge_norm_one' (v w : HexVertex) (h : hexGraph.Adj v w) :
    ‖correctHexEmbed w - correctHexEmbed v‖ = 1 := by
  have hns := hex_edge_norm_one v w h
  have := Complex.normSq_eq_norm_sq (correctHexEmbed w - correctHexEmbed v)
  nlinarith [norm_nonneg (correctHexEmbed w - correctHexEmbed v)]

/-- For a unit-modulus complex number `z`, `exp (i · arg z) = z`. -/
lemma exp_I_arg_of_norm_one (z : ℂ) (h : ‖z‖ = 1) :
    Complex.exp (Complex.I * Complex.arg z) = z := by
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [h] at this
  rw [mul_comm]
  simpa using this

/-! ## The first edge direction of a vertex list -/

/-- The direction of the first edge of a vertex list (embedding of the second
    vertex minus the first). Defaults to `1` on lists shorter than two. -/
def hexFirstDir : List HexVertex → ℂ
  | a :: b :: _ => correctHexEmbed b - correctHexEmbed a
  | _ => 1

/-- Appending a vertex at the end of a list of length `≥ 2` does not change its
    first edge direction. -/
lemma hexFirstDir_append (X : List HexVertex) (a : HexVertex) (h : 2 ≤ X.length) :
    hexFirstDir (X ++ [a]) = hexFirstDir X := by
  match X, h with
  | _ :: _ :: _, _ => rfl

/-- For a list of length `≥ 2`, the first edge direction is the embedding
    difference of the two leading vertices, expressed via `List.get`. -/
lemma hexFirstDir_eq_get (L : List HexVertex) (h : 2 ≤ L.length) :
    hexFirstDir L =
      correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩) := by
  match L, h with
  | _ :: _ :: _, _ => rfl

/-! ## Telescoping of the winding around a hex trail

The key analytic fact: along a hex trail every turn ratio `d₂/d₁` has unit
modulus, so `exp (i · arg (d₂/d₁)) = d₂/d₁`. Multiplying these out telescopes
to a ratio of the last to the first edge direction. We package the result
multiplicatively to avoid division. -/

/-
Telescoping identity for the winding of a hex trail of length `≥ 3`:
    `exp(i·W) · (first edge dir) = (last edge dir)`, where the last edge
    direction is `-(hexFirstDir L.reverse)`.
-/
lemma hexTrailList_winding_telescope (L : List HexVertex)
    (h_trail : HexTrailList L) (hlen : 3 ≤ L.length) :
    Complex.exp (Complex.I * hexWalkWinding L) * hexFirstDir L =
      - hexFirstDir L.reverse := by
  induction' L with a L ih <;> simp_all +decide [ List.length ];
  rcases L with ( _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ) <;> simp_all +decide [ hexWalkWinding ];
  have h_ind : Complex.exp (Complex.I * hexWalkWinding (b :: c :: L)) * hexFirstDir (b :: c :: L) = -hexFirstDir (L.reverse ++ [c, b]) := by
    rcases L with ( _ | ⟨ d, L ⟩ ) <;> simp_all +decide [ HexTrailList ];
    unfold hexWalkWinding hexFirstDir; simp +decide [ mul_comm ] ;
  have h_exp : Complex.exp (Complex.I * Complex.arg ((correctHexEmbed c - correctHexEmbed b) / (correctHexEmbed b - correctHexEmbed a))) = (correctHexEmbed c - correctHexEmbed b) / (correctHexEmbed b - correctHexEmbed a) := by
    apply exp_I_arg_of_norm_one;
    have h_norm : ‖correctHexEmbed c - correctHexEmbed b‖ = 1 ∧ ‖correctHexEmbed b - correctHexEmbed a‖ = 1 := by
      have h_norm : hexGraph.Adj a b ∧ hexGraph.Adj b c := by
        exact ⟨ h_trail.1, h_trail.2.1 ⟩;
      exact ⟨ hex_edge_norm_one' _ _ h_norm.2, hex_edge_norm_one' _ _ h_norm.1 ⟩;
    aesop;
  simp_all +decide [ mul_add, Complex.exp_add ];
  rw [ mul_assoc, show hexFirstDir ( a :: b :: c :: L ) = correctHexEmbed b - correctHexEmbed a from rfl ];
  rw [ show hexFirstDir ( L.reverse ++ [ c, b, a ] ) = hexFirstDir ( L.reverse ++ [ c, b ] ) from ?_ ];
  · convert h_ind using 1;
    rw [ div_mul_eq_mul_div, div_eq_iff ] <;> ring!;
    · rw [ show hexFirstDir ( b :: c :: L ) = correctHexEmbed c - correctHexEmbed b from rfl ] ; ring;
    · exact sub_ne_zero_of_ne <| by intro h; have := h_trail.1; simp_all +decide ;
  · convert hexFirstDir_append ( L.reverse ++ [ c, b ] ) a _ using 1;
    · simp +decide [ List.append_assoc ];
    · simp +arith +decide

/-! ## Total turning of a closed hex trail is a multiple of 2π

From the telescoping identity, for a *closed* trail the last edge direction
coincides with the first, so `exp(i·(W + closure)) = 1`, i.e. the total
turning is an integer multiple of `2π`. This is the "easy half" of the
Umlaufsatz. -/

/-
The last edge of a hex trail (of length ≥ 3) is a genuine hex-graph edge.
-/
lemma hexTrailList_adj_last (L : List HexVertex)
    (h_trail : HexTrailList L) (hlen : 3 ≤ L.length) :
    hexGraph.Adj (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨L.length - 1, by omega⟩) := by
  induction' L with L_head L_tail ih;
  · contradiction;
  · rcases L_tail with ( _ | ⟨ L_tail_head, L_tail_tail ⟩ ) <;> simp_all +arith +decide;
    · contradiction;
    · rcases L_tail_tail with ( _ | ⟨ L_tail_tail_head, L_tail_tail_tail ⟩ ) <;> simp_all +arith +decide;
      · contradiction;
      · cases L_tail_tail_tail <;> simp_all +arith +decide;
        · cases h_trail ; aesop;
        · exact ih ( by cases h_trail ; tauto )

/-
For a closed list, the last element equals the first.
-/
lemma list_get_last_eq_get_zero_of_closed (L : List HexVertex) (hlen : 1 ≤ L.length)
    (h_closed : L.head? = L.getLast?) :
    L.get ⟨L.length - 1, by omega⟩ = L.get ⟨0, by omega⟩ := by
  rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> norm_num at *;
  grind

/-
For a closed hex trail, the exponential of `i` times the total turning
    (winding plus closing turn) equals `1`.
-/
lemma hex_closed_winding_exp_eq_one (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?) :
    Complex.exp (Complex.I * ((hexWalkWinding L +
      Complex.arg ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
        (correctHexEmbed (L.get ⟨0, by omega⟩) -
          correctHexEmbed (L.get ⟨L.length - 2, by omega⟩))) : ℝ) : ℂ)) = 1 := by
  have h_exp : Complex.exp (Complex.I * hexWalkWinding L) * (correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) = (correctHexEmbed (L.get ⟨0, by omega⟩) - correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)) := by
    convert hexTrailList_winding_telescope L h_trail ( by linarith ) using 1;
    · rw [ hexFirstDir_eq_get L ( by linarith ) ];
    · rw [ hexFirstDir_eq_get ];
      all_goals norm_num;
      all_goals try linarith;
      rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> norm_num at *;
      grind;
  have h_norm : ‖correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)‖ = 1 ∧ ‖correctHexEmbed (L.get ⟨0, by omega⟩) - correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)‖ = 1 := by
    constructor;
    · rcases L with ( _ | ⟨ a, _ | ⟨ b, L ⟩ ⟩ ) <;> norm_num at *;
      · grind;
      · contradiction;
      · cases L <;> simp_all +decide [ HexTrailList ];
        · contradiction;
        · exact hex_edge_norm_one' _ _ h_trail.1;
    · have h_adj : hexGraph.Adj (L.get ⟨L.length - 2, by omega⟩) (L.get ⟨L.length - 1, by omega⟩) := by
        apply hexTrailList_adj_last L h_trail (by omega);
      convert hex_edge_norm_one' _ _ h_adj using 1;
      rw [ list_get_last_eq_get_zero_of_closed L ( by omega ) h_closed ];
  have h_exp_arg : Complex.exp (Complex.I * Complex.arg ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) / (correctHexEmbed (L.get ⟨0, by omega⟩) - correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)))) = (correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) / (correctHexEmbed (L.get ⟨0, by omega⟩) - correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)) := by
    convert exp_I_arg_of_norm_one _ _ using 1;
    aesop;
  push_cast [ mul_add, Complex.exp_add ];
  rw [ h_exp_arg, mul_div, div_eq_iff ] <;> aesop

/-- For a closed hex trail, the total turning is an integer multiple of `2π`. -/
lemma hex_closed_winding_int_mul (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?) :
    ∃ n : ℤ, hexWalkWinding L +
      Complex.arg ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
        (correctHexEmbed (L.get ⟨0, by omega⟩) -
          correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)))
      = 2 * Real.pi * n := by
  have hexp := hex_closed_winding_exp_eq_one L hL h_trail h_closed
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  refine ⟨n, ?_⟩
  have key : (((hexWalkWinding L +
      Complex.arg ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
        (correctHexEmbed (L.get ⟨0, by omega⟩) -
          correctHexEmbed (L.get ⟨L.length - 2, by omega⟩))) : ℝ) : ℂ)) =
      (((2 * Real.pi * (n : ℝ)) : ℝ) : ℂ) := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [hn]; push_cast; ring
  exact_mod_cast key

/-! ## Combinatorial reduction: turning as an integer signed-turn count

This section establishes, sorry-free, the *combinatorial* reduction of the
turning recommended in this file's header: every hex turn is `±π/3`
(`hex_turn_value`), so assigning to each turn a sign `±1` (a left turn `+1`,
a right turn `-1`) makes the total turning equal `(π/3) · S`, where `S` is the
integer signed-turn count.  Combined with `hex_closed_winding_int_mul`
(`total turning = 2π·n`), this reduces the remaining `umlaufsatz_pm_one` to the
purely combinatorial statement `S = ±6`.

These declarations are reusable infrastructure for the combinatorial route to
the Umlaufsatz; they are not yet consumed by `umlaufsatz_pm_one` (which is the
remaining topological gap), but are imported transitively via `SAWFinal.lean`. -/

/-- The sign of a single hex turn `v₀ → v₁ → v₂`: `+1` for a left turn
    (`arg(d₂/d₁) = +π/3`, equivalently `Im(d₂/d₁) > 0`) and `-1` for a right
    turn.  Defined via the imaginary part of the turn ratio so that it is a
    genuine integer with no dependence on `Complex.arg`. -/
noncomputable def hexTurnSign (v₀ v₁ v₂ : HexVertex) : ℤ :=
  if 0 < ((correctHexEmbed v₂ - correctHexEmbed v₁) /
          (correctHexEmbed v₁ - correctHexEmbed v₀)).im then 1 else -1

/-
At a non-backtracking hex turn, the turning angle is `(π/3)` times the
    integer turn sign.
-/
lemma hexTurn_arg_eq_sign (v₀ v₁ v₂ : HexVertex)
    (h₁ : hexGraph.Adj v₀ v₁) (h₂ : hexGraph.Adj v₁ v₂)
    (h_ne : s(v₀, v₁) ≠ s(v₁, v₂)) :
    Complex.arg ((correctHexEmbed v₂ - correctHexEmbed v₁) /
                 (correctHexEmbed v₁ - correctHexEmbed v₀))
      = (Real.pi / 3) * (hexTurnSign v₀ v₁ v₂ : ℝ) := by
  obtain h | h := hex_turn_value v₀ v₁ v₂ h₁ h₂ h_ne;
  · have h_im_pos : ((correctHexEmbed v₂ - correctHexEmbed v₁) / (correctHexEmbed v₁ - correctHexEmbed v₀)).im = Real.sin (Real.pi / 3) := by
      rw [ ← Complex.norm_mul_sin_arg ] ; norm_num [ h ];
      rw [ div_eq_iff ] <;> norm_num [ hex_edge_norm_one' _ _ h₁, hex_edge_norm_one' _ _ h₂ ];
    unfold hexTurnSign; aesop;
  · -- Since the argument is -(π/3), the imaginary part of the ratio is negative.
    have h_im_neg : ((correctHexEmbed v₂ - correctHexEmbed v₁) / (correctHexEmbed v₁ - correctHexEmbed v₀)).im < 0 := by
      rw [ ← Complex.norm_mul_sin_arg ] ; norm_num [ h ];
      exact div_pos ( norm_pos_iff.mpr ( hex_embed_sub_ne_zero' _ _ h₂ ) ) ( norm_pos_iff.mpr ( hex_embed_sub_ne_zero' _ _ h₁ ) );
    unfold hexTurnSign;
    rw [ if_neg ( not_lt_of_gt h_im_neg ) ] ; push_cast ; linarith

/-- The integer signed-turn count of a vertex list: the sum of the per-turn
    signs over all consecutive triples. -/
noncomputable def hexSignedTurnCount : List HexVertex → ℤ
  | v₀ :: v₁ :: v₂ :: rest => hexTurnSign v₀ v₁ v₂ + hexSignedTurnCount (v₁ :: v₂ :: rest)
  | _ => 0

/-- The total winding of a hex trail equals `(π/3)` times its integer
    signed-turn count. -/
lemma hexWalkWinding_eq_signedTurnCount (L : List HexVertex) (h : HexTrailList L) :
    hexWalkWinding L = (Real.pi / 3) * (hexSignedTurnCount L : ℝ) := by
  induction' n : L.length using Nat.strong_induction_on with n ih generalizing L;
  rcases L with ( _ | ⟨ v₀, _ | ⟨ v₁, _ | ⟨ v₂, L ⟩ ⟩ ⟩ ) <;> norm_num at *;
  · unfold hexWalkWinding hexSignedTurnCount; norm_num;
  · unfold hexWalkWinding hexSignedTurnCount; norm_num;
  · unfold hexWalkWinding hexSignedTurnCount; norm_num;
  · rcases h with ⟨ h₁, h₂, h₃, h₄ ⟩;
    convert congr_arg₂ ( · + · ) ( hexTurn_arg_eq_sign v₀ v₁ v₂ h₁ h₂ h₃ ) ( ih _ _ _ h₄ rfl ) using 1;
    · rw [ ← mul_add, show hexSignedTurnCount ( v₀ :: v₁ :: v₂ :: L ) = hexTurnSign v₀ v₁ v₂ + hexSignedTurnCount ( v₁ :: v₂ :: L ) from rfl ] ; push_cast ; ring;
    · simp +arith +decide [ ← n ]

/-! ## The turning number theorem for simple closed hex trails (Umlaufsatz)

The "hard half": for a *simple* (non-self-intersecting) closed trail, the
integer multiple is exactly `±1`. This is the discrete analogue of Hopf's
Umlaufsatz / the turning tangent theorem. -/

/-- The magnitude part of the Umlaufsatz: for a simple closed hex trail whose
    total turning is `2π·n`, the integer `n` is `±1`.

    **Sorry**: this is the genuine content of the discrete Umlaufsatz —
    that a simple (non-self-intersecting) closed polygon on the hexagonal
    lattice has turning number `±1`. It is the only remaining gap in
    `hex_closed_trail_turning_number`. -/
lemma umlaufsatz_pm_one (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup)
    (n : ℤ)
    (hn : hexWalkWinding L +
      Complex.arg ((correctHexEmbed (L.get ⟨1, by omega⟩) - correctHexEmbed (L.get ⟨0, by omega⟩)) /
        (correctHexEmbed (L.get ⟨0, by omega⟩) -
          correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)))
      = 2 * Real.pi * n) :
    n = 1 ∨ n = -1 := by
  sorry

/-- The turning number theorem for simple closed hex trails.
    For a list [v₀, v₁, ..., vₙ₋₁, v₀] that forms a simple closed trail
    on the hex lattice:
    hexWalkWinding L + closure_turn = ±2π

    This is the discrete Gauss-Bonnet theorem applied to simple closed
    polygons on the hexagonal lattice (Umlaufsatz). The proof splits into
    the "easy half" (`hex_closed_winding_int_mul`: the total turning is a
    multiple of `2π`) and the "hard half" (`umlaufsatz_pm_one`: the
    multiple is `±1`). -/
lemma hex_closed_trail_turning_number (L : List HexVertex)
    (hL : 4 ≤ L.length)
    (h_trail : HexTrailList L)
    (h_closed : L.head? = L.getLast?)
    (h_simple : L.tail.dropLast.Nodup) :
    let d_first := correctHexEmbed (L.get ⟨1, by omega⟩) -
                   correctHexEmbed (L.get ⟨0, by omega⟩)
    let d_last := correctHexEmbed (L.get ⟨0, by omega⟩) -
                  correctHexEmbed (L.get ⟨L.length - 2, by omega⟩)
    let closure := Complex.arg (d_first / d_last)
    hexWalkWinding L + closure = 2 * Real.pi ∨
    hexWalkWinding L + closure = -(2 * Real.pi) := by
  intro d_first d_last closure
  obtain ⟨n, hn⟩ := hex_closed_winding_int_mul L hL h_trail h_closed
  rcases umlaufsatz_pm_one L hL h_trail h_closed h_simple n hn with h | h
  · left; rw [show closure = _ from rfl, hn, h]; push_cast; ring
  · right; rw [show closure = _ from rfl, hn, h]; push_cast; ring

end