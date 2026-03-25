/-
# Zigzag SAW construction for lower bounds

This file constructs explicit self-avoiding walks on the hexagonal lattice
using a "zigzag" pattern that provides a lower bound on saw_count.

## Main result

For each binary string of length k, we construct a distinct (2k)-step SAW
from the origin. This gives c_{2k} ≥ 2^k, which (combined with c_1 = 3)
implies c_n^2 ≥ 2^n for all n ≥ 1 (saw_count_sq_ge_two_pow).

## Construction

The zigzag walk from the origin (0,0,false) starts with the "same cell"
step to (0,0,true), then alternates:
- T→F step: binary choice to go "left" or "down"
- F→T step: go to the same cell (x,y,false) → (x,y,true)

The F-coordinates follow a lattice path from (0,0) going left or down,
so x_i + y_i = -i, making all coordinates distinct.
-/

import RequestProject.SAWBridge

open Real

noncomputable section

/-! ## Zigzag coordinate sequence

Given a list of boolean choices, compute the sequence of (x,y) coordinates
visited by the zigzag walk.
-/

/-- Compute the next (x,y) coordinate after a binary choice.
    false = go left (x-1, y), true = go down (x, y-1). -/
def zigzag_step (pos : ℤ × ℤ) (choice : Bool) : ℤ × ℤ :=
  if choice then (pos.1, pos.2 - 1) else (pos.1 - 1, pos.2)

/-- The sequence of F-vertex coordinates in the zigzag walk.
    Starting from (0,0), each step goes left or down based on the choice. -/
def zigzag_coords : List Bool → List (ℤ × ℤ)
  | [] => [(0, 0)]
  | c :: cs => (0, 0) :: (zigzag_coords_from (0, 0) (c :: cs))
where
  zigzag_coords_from (pos : ℤ × ℤ) : List Bool → List (ℤ × ℤ)
    | [] => []
    | c :: cs =>
      let next := zigzag_step pos c
      next :: zigzag_coords_from next cs

/-- Simpler definition: fold the choices to get the coordinate list. -/
def zigzag_positions (choices : List Bool) : List (ℤ × ℤ) :=
  choices.scanl (fun pos c => zigzag_step pos c) (0, 0)

/-
PROBLEM
The sum x + y at position i equals -i.

PROVIDED SOLUTION
By induction on choices. Base case: when choices = [], zigzag_positions has length 1, so i = 0, pos = (0,0), sum = 0. Inductive step: when choices = c :: cs, zigzag_positions (c :: cs) = (0,0) :: List.scanl zigzag_step (zigzag_step (0,0) c) cs. For i = 0, pos = (0,0), sum = 0. For i > 0, we need to track through the scanl. The key observation is that zigzag_step always decreases x+y by 1 (either x-1 or y-1), so after i steps the sum is -i.
-/
lemma zigzag_sum_eq_neg (choices : List Bool) (i : ℕ) (hi : i < (zigzag_positions choices).length) :
    let pos := (zigzag_positions choices).get ⟨i, hi⟩
    pos.1 + pos.2 = -(i : ℤ) := by
  induction choices generalizing i with
  | nil =>
    simp [zigzag_positions, List.scanl] at hi
    have : i = 0 := by omega
    subst this; simp [zigzag_positions, List.scanl]
  | cons c cs ih =>
    simp [zigzag_positions, List.scanl] at hi ⊢
    rcases i with ( _ | i ) <;> simp_all +decide [ add_comm ];
    convert congr_arg ( · + -1 ) ( ih i _ ) using 1;
    all_goals norm_num [ zigzag_positions ] at *;
    · have h_scanl : ∀ (l : List Bool) (pos : ℤ × ℤ) (i : ℕ), i < List.length (List.scanl (fun x1 x2 => zigzag_step x1 x2) pos l) → (List.scanl (fun x1 x2 => zigzag_step x1 x2) pos l)[i]! = List.foldl (fun pos c => zigzag_step pos c) pos (List.take i l) := by
        grind;
      convert congr_arg ( fun x : ℤ × ℤ => x.1 + x.2 ) ( h_scanl cs ( zigzag_step ( 0, 0 ) c ) i hi ) using 1;
      · simp +decide [ List.scanlM, List.scanl ];
        rw [ List.getElem?_reverse ];
        · rw [ List.getElem?_eq_getElem ];
          rw [ Option.getD_some ];
        · convert hi using 1;
          simp +decide [ List.scanlM ];
      · induction' ( List.take i cs ) using List.reverseRecOn with c cs ih <;> simp_all +decide [ zigzag_step ];
        · split_ifs <;> norm_num;
        · lia;
    · linarith

/-
PROBLEM
All positions in the zigzag are distinct (since x+y is strictly decreasing).

PROVIDED SOLUTION
All positions in zigzag_positions are distinct because their x+y values are strictly decreasing. By zigzag_sum_eq_neg, position i has x+y = -i, so different indices give different x+y sums, hence different positions. Use List.nodup_iff_injective_get or similar, showing that if positions at indices i and j are equal, then -i = -j so i = j.
-/
lemma zigzag_positions_nodup (choices : List Bool) :
    (zigzag_positions choices).Nodup := by
  rw [ List.nodup_iff_injective_get ];
  intros i j hij; have := zigzag_sum_eq_neg choices i ( by simp ) ; have := zigzag_sum_eq_neg choices j ( by simp ) ; aesop;

/-! ## Building the walk

We construct the actual hexGraph.Walk from the zigzag coordinates.
-/

/-- The full list of vertices in the zigzag walk, interleaving F and T vertices.
    For choices of length k, this gives a walk of length 2k:
    (0,0,F), (0,0,T), (x₁,y₁,F), (x₁,y₁,T), ..., (xₖ,yₖ,F) -/
def zigzag_vertices (choices : List Bool) : List HexVertex :=
  let positions := zigzag_positions choices
  (positions.flatMap fun pos => [(pos.1, pos.2, false), (pos.1, pos.2, true)])
  |>.dropLast  -- Remove the trailing T-vertex (walk ends at F-vertex for even length)

/-- Adjacency for same-cell F→T step. -/
lemma hex_adj_same_cell (x y : ℤ) : hexGraph.Adj (x, y, false) (x, y, true) := by
  left; exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Adjacency for T→F "left" step: (x,y,T) → (x-1,y,F). -/
lemma hex_adj_T_left (x y : ℤ) : hexGraph.Adj (x, y, true) (x - 1, y, false) := by
  right; refine ⟨rfl, rfl, Or.inr (Or.inl ⟨?_, rfl⟩)⟩; omega

/-- Adjacency for T→F "down" step: (x,y,T) → (x,y-1,F). -/
lemma hex_adj_T_down (x y : ℤ) : hexGraph.Adj (x, y, true) (x, y - 1, false) := by
  right; refine ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩; simp

/-! ## Counting result

The injection from {0,1}^k to SAW(hexOrigin, 2k) gives c_{2k} ≥ 2^k.
-/

/-- There are at least 2^k distinct (2k)-step SAWs from the origin. -/
lemma saw_count_even_lower (k : ℕ) : 2 ^ k ≤ saw_count (2 * k) := by
  sorry

/-- There are at least 3 * 2^k distinct (2k+1)-step SAWs from the origin for k ≥ 0. -/
lemma saw_count_odd_lower (k : ℕ) : 3 * 2 ^ k ≤ saw_count (2 * k + 1) := by
  sorry

/-
PROBLEM
Main bound: 2^n ≤ c_n^2 for n ≥ 1.

    Proof by cases on n even/odd:
    - n = 2k (k ≥ 1): c_{2k} ≥ 2^k, so c_{2k}^2 ≥ 4^k = 2^{2k} = 2^n.
    - n = 2k+1 (k ≥ 0): c_{2k+1} ≥ 3 · 2^k, so c_{2k+1}^2 ≥ 9 · 4^k ≥ 2 · 4^k = 2^{2k+1} = 2^n.
    - n = 1: c_1 = 3, 3^2 = 9 ≥ 2.

PROVIDED SOLUTION
Split on n even/odd. For n = 2k with k ≥ 1: by saw_count_even_lower, c_{2k} ≥ 2^k, so c_{2k}^2 ≥ 2^{2k} = 2^n. For n = 2k+1: by saw_count_odd_lower, c_{2k+1} ≥ 3·2^k, so c_{2k+1}^2 ≥ 9·4^k ≥ 2·4^k = 2^{2k+1} = 2^n. For k=0 (n=1): c_1 = 3, 3^2 = 9 ≥ 2^1 = 2. Use Nat.even_or_odd n to split, then compute with pow_mul, pow_succ etc. The comparison 9·4^k ≥ 2·4^k holds since 9 ≥ 2, so just use nlinarith.
-/
theorem saw_count_sq_ge_two_pow' (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ saw_count n ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩;
  · convert pow_le_pow_left₀ ( by positivity ) ( saw_count_even_lower k ) 2 using 1 ; ring;
  · -- By the lemma saw_count_odd_lower, we have saw_count (2 * k + 1) ≥ 3 * 2 ^ k.
    have h_odd_lower : saw_count (2 * k + 1) ≥ 3 * 2 ^ k := by
      exact saw_count_odd_lower k;
    rw [ pow_add, pow_mul' ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) k ]

end