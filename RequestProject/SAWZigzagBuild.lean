/-
# Zigzag walk construction helpers

Building the actual hexGraph.Walk for the zigzag SAW construction.
-/

import Mathlib
import RequestProject.SAWZigzag

noncomputable section

/-! ## Recursive walk construction

We build zigzag walks by induction: for each k, given a position (x,y),
we construct a (2k)-step walk from (x,y,false) that follows the zigzag pattern.
-/

/-- Build a 2k-step zigzag walk from position (x,y,false), using choices.
    Returns the walk and proves it has length 2*choices.length. -/
def buildZigzagWalk : (choices : List Bool) → (x y : ℤ) →
    { p : hexGraph.Walk (x, y, false)
        ((choices.foldl zigzag_step (x, y)).1, (choices.foldl zigzag_step (x, y)).2, false) //
      p.length = 2 * choices.length }
  | [], _, _ => ⟨.nil, by simp⟩
  | c :: cs, x, y =>
    let next := zigzag_step (x, y) c
    let rest := buildZigzagWalk cs next.1 next.2
    ⟨.cons (hex_adj_same_cell x y) (.cons (hex_adj_T_choice x y c) rest.1), by
      simp [rest.2]; ring⟩

/-- The zigzag walk from hexOrigin. -/
def zigzagSAWWalk (choices : List Bool) :
    { p : hexGraph.Walk hexOrigin
        ((choices.foldl zigzag_step (0, 0)).1, (choices.foldl zigzag_step (0, 0)).2, false) //
      p.length = 2 * choices.length } :=
  buildZigzagWalk choices 0 0

/-- The zigzag walk length. -/
lemma zigzagSAWWalk_length (choices : List Bool) :
    (zigzagSAWWalk choices).1.length = 2 * choices.length :=
  (zigzagSAWWalk choices).2

/-
PROBLEM
Support of buildZigzagWalk contains only vertices with the correct structure.

PROVIDED SOLUTION
By induction on choices.

Base case (choices = []): The walk is .nil with support [(x,y,false)]. zigzag_positions [] = [(0,0)], mapped gives [(x,y)]. So v = (x,y,false) matches pos = (x,y) with the first disjunct.

Inductive case (choices = c :: cs): The walk is
  .cons (hex_adj_same_cell x y) (.cons (hex_adj_T_choice x y c) rest)
Its support is:
  (x,y,false) :: (x,y,true) :: rest.support

For (x,y,false): zigzag_positions (c::cs) starts with (0,0), mapped gives (x,y). Match with pos=(x,y), first disjunct.

For (x,y,true): Same pos=(x,y), second disjunct.

For v ∈ rest.support: By IH applied to (buildZigzagWalk cs next.1 next.2), there exists pos' in zigzag_positions cs mapped to (·.1+next.1, ·.2+next.2) such that v matches. We need to show this pos' also appears in zigzag_positions (c::cs) mapped to (·.1+x, ·.2+y).

zigzag_positions (c::cs) = (0,0) :: List.scanl zigzag_step (zigzag_step (0,0) c) cs.
So the tail positions are exactly the positions of List.scanl zigzag_step (zigzag_step (0,0) c) cs.

The rest of the walk starts from (next.1, next.2, false) where next = zigzag_step (x,y) c. The IH gives positions from zigzag_positions cs mapped with offset (next.1, next.2). We need to connect these to zigzag_positions (c::cs) mapped with offset (x,y).

The positions in zigzag_positions cs (with offset next = zigzag_step (0,0) c + (x,y)) correspond to positions in zigzag_positions (c::cs) (with offset (x,y)). This is because zigzag_positions (c::cs) = (0,0) :: (zigzag_positions cs shifted by zigzag_step (0,0) c).

More precisely: List.scanl zigzag_step (zigzag_step (0,0) c) cs has the same elements as List.scanl zigzag_step (0,0) cs shifted by zigzag_step (0,0) c. No wait, that's not right because zigzag_step is not translation-invariant.

Hmm, actually zigzag_step IS NOT translation-invariant: zigzag_step (a+dx, b+dy) c = zigzag_step (a,b) c + (dx,dy). So List.scanl zigzag_step (pos+offset) cs = List.scanl zigzag_step pos cs + offset. This IS translation-invariant.

So: zigzag_positions cs mapped with offset next = (scanl zigzag_step (0,0) cs) mapped with (·+next). And the tail of zigzag_positions (c::cs) = scanl zigzag_step (zigzag_step (0,0) c) cs = (scanl zigzag_step (0,0) cs) mapped with (·+zigzag_step (0,0) c).

With offset (x,y), the tail positions become: (scanl zigzag_step (0,0) cs).map (·+ zigzag_step (0,0) c + (x,y)) = (scanl zigzag_step (0,0) cs).map (·+ next). And this matches the IH positions.

This is the right argument but it's quite involved to formalize.
-/
lemma buildZigzagWalk_support_structure (choices : List Bool) (x y : ℤ) :
    ∀ v ∈ (buildZigzagWalk choices x y).1.support,
      ∃ pos ∈ zigzag_positions choices |>.map (fun p => (p.1 + x, p.2 + y)),
        v = (pos.1, pos.2, false) ∨ v = (pos.1, pos.2, true) := by
  intro v hv
  induction' choices with c cs ih generalizing x y v;
  · cases hv ; aesop ( simp_config := { decide := true } ) ;
    contradiction;
  · by_cases hv' : v = (x, y, false) ∨ v = (x, y, true);
    · rcases hv' with ( rfl | rfl ) <;> simp +decide [ zigzag_positions ];
    · -- Since $v \neq (x, y, false)$ and $v \neq (x, y, true)$, we can apply the induction hypothesis to the rest of the walk.
      obtain ⟨pos, hpos⟩ : ∃ pos ∈ (buildZigzagWalk cs (zigzag_step (x, y) c).1 (zigzag_step (x, y) c).2).1.support, v = pos := by
        erw [ List.mem_cons ] at hv ; aesop;
      obtain ⟨ pos', hpos', hpos'' ⟩ := ih _ _ _ hpos.1; use pos'; simp_all +decide [ zigzag_positions ] ;
      obtain ⟨ a, b, h₁, h₂ ⟩ := hpos'; use Or.inr ⟨ a + ( zigzag_step ( 0, 0 ) c ).1, b + ( zigzag_step ( 0, 0 ) c ).2, ?_, ?_ ⟩ <;> simp_all +decide [ zigzag_step ] ;
      · have h_scanl : ∀ (l : List Bool) (pos : ℤ × ℤ), List.scanl (fun pos c => if c = true then (pos.1, pos.2 - 1) else (pos.1 - 1, pos.2)) (pos.1 + (if c = true then 0 else -1), pos.2 + (if c = true then -1 else 0)) l = List.map (fun p => (p.1 + (if c = true then 0 else -1), p.2 + (if c = true then -1 else 0))) (List.scanl (fun pos c => if c = true then (pos.1, pos.2 - 1) else (pos.1 - 1, pos.2)) pos l) := by
          intro l pos; induction l generalizing pos <;> simp_all +decide [ List.scanl ] ;
          grind +ring;
        grind +splitIndPred;
      · convert h₂ using 1 ; split_ifs <;> ring_nf;

/-
PROBLEM
The zigzag walk is a path (self-avoiding).

PROVIDED SOLUTION
By induction on choices.

Base case (choices = []): The walk is .nil, which is trivially a path.

Inductive case (choices = c :: cs): The walk is:
  (x,y,false) →[same cell] (x,y,true) →[choice c] (x',y',false) →[...rest...]→ endpoint

where (x',y') = zigzag_step (x,y) c. By IH, the rest (buildZigzagWalk cs x' y') is a path.

We need to show the full walk .cons (hex_adj_same_cell ...) (.cons (hex_adj_T_choice ...) rest) is a path. This requires:

1. rest is a path (by IH)
2. (x,y,true) is not in the support of the rest
3. (x,y,false) is not in the support of (.cons ... rest)

For (2): The rest visits vertices starting from (x',y',false) where (x',y') = zigzag_step (x,y) c. The zigzag walk from (x',y') visits positions with x+y ≤ x'+y' = (x+y) - 1. The vertex (x,y,true) has x+y which is strictly greater than any vertex visited by the rest. So (x,y,true) is not in the support.

For (3): Similarly, (x,y,false) has x+y greater than any vertex in the rest. And (x,y,false) ≠ (x,y,true) since the Bool components differ. So (x,y,false) is not in the support of the cons.

The key property used: all vertices in buildZigzagWalk cs x' y' have the property that their "generalized sum" (fst + snd for F-vertices, fst + snd for T-vertices) is ≤ x' + y' = x + y - 1 < x + y.

This is the crucial self-avoidance argument. It relies on zigzag_step always decreasing x+y by 1 (zigzag_step_sum).
-/
lemma buildZigzagWalk_isPath (choices : List Bool) (x y : ℤ) :
    (buildZigzagWalk choices x y).1.IsPath := by
  induction' choices with c choices ih generalizing x y ; simp_all ; aesop;
  -- By Lemma 2, the new walk is a path if the rest is a path and the new vertex is not in the support of the rest.
  have h_new_vertex : (x, y, true)∉((buildZigzagWalk choices (zigzag_step (x, y) c).1 (zigzag_step (x, y) c).2).1.support) := by
    -- By induction on the length of the choices list, we can show that the support of the walk is contained within the set of vertices with a generalized sum less than or equal to (zigzag_step (x, y) c).1 + (zigzag_step (x, y) c).2.
    have h_support : ∀ (choices : List Bool) (x y : ℤ), ∀ v ∈ ((buildZigzagWalk choices x y).1.support), v.1 + v.2.1 ≤ x + y := by
      intro choices x y v hv
      have h_support : ∀ (v : HexVertex), v ∈ ((buildZigzagWalk choices x y).1.support) → v.1 + v.2.1 ≤ x + y := by
        -- By definition of `zigzag_positions`, we know that every vertex in the support of the walk has a generalized sum less than or equal to `x + y`.
        intros v hv
        have h_gen_sum : ∃ pos ∈ zigzag_positions choices |>.map (fun p => (p.1 + x, p.2 + y)), v = (pos.1, pos.2, false) ∨ v = (pos.1, pos.2, true) := by
          have := buildZigzagWalk_support_structure choices x y v hv; aesop;
        generalize_proofs at *; (
        obtain ⟨ pos, hpos, rfl | rfl ⟩ := h_gen_sum <;> simp_all +decide [ zigzag_positions ] ; ring_nf ;
        · obtain ⟨ a, b, h₁, rfl ⟩ := hpos; have := zigzag_sum_eq_neg choices; simp_all +decide [ zigzag_positions ] ; ring_nf ;
          -- Since `a` and `b` are the coordinates of the vertex after `i` steps, we have `a + b = -i`.
          obtain ⟨i, hi⟩ : ∃ i ≤ choices.length, (a, b) = List.foldl (fun pos c => zigzag_step pos c) (0, 0) (List.take i choices) := by
            have h_gen_sum : ∀ {l : List Bool} {pos : ℤ × ℤ}, (a, b) ∈ List.scanl (fun pos c => zigzag_step pos c) pos l → ∃ i ≤ l.length, (a, b) = List.foldl (fun pos c => zigzag_step pos c) pos (List.take i l) := by
              intros l pos h; induction' l with c l ih generalizing pos <;> simp_all +decide [ List.scanl ] ; ring_nf ; (
              rcases h with ( ⟨ rfl, rfl ⟩ | h ) <;> [ exact ⟨ 0, by norm_num ⟩ ; exact Exists.elim ( ih _ _ h ) fun i hi => ⟨ i + 1, by linarith, by simp +decide [ List.take ] ; aesop ⟩ ] ;)
            generalize_proofs at *; (
            exact h_gen_sum h₁ |> fun ⟨ i, hi, hi' ⟩ => ⟨ i, hi, hi' ⟩)
          generalize_proofs at *; (
          grind);
        · obtain ⟨ a, b, h₁, rfl ⟩ := hpos; simp_all +decide [ List.mem_iff_get ] ; ring_nf ; (
          obtain ⟨ n, hn ⟩ := h₁; have := zigzag_sum_eq_neg ( List.take n choices ) n; simp_all +decide [ add_comm, add_left_comm ] ;
          have := this ( Nat.le_of_lt_succ ( by simpa using n.2 ) ) ; simp_all +decide [ zigzag_positions ] ; ring_nf ;
          grind))
      exact h_support v hv
    generalize_proofs at *; (
    exact fun h => by have := h_support _ _ _ _ h; norm_num [ zigzag_step ] at this; split_ifs at this <;> omega;)
  generalize_proofs at *; (
  -- By definition of `buildZigzagWalk`, the new walk is a path if the rest is a path and the new vertex is not in the support of the rest.
  have h_new_walk : (buildZigzagWalk (c :: choices) x y).1 = .cons (hex_adj_same_cell x y) (.cons (hex_adj_T_choice x y c) (buildZigzagWalk choices (zigzag_step (x, y) c).1 (zigzag_step (x, y) c).2).1) := by
    rfl
  generalize_proofs at *; (
  simp_all +decide [ SimpleGraph.Walk.isPath_def ];
  intro h; have := ih ( zigzag_step ( x, y ) c |> Prod.fst ) ( zigzag_step ( x, y ) c |> Prod.snd ) ; simp_all +decide [ List.nodup_iff_injective_get ] ;
  have := buildZigzagWalk_support_structure choices ( zigzag_step ( x, y ) c |> Prod.fst ) ( zigzag_step ( x, y ) c |> Prod.snd ) ( x, y, false ) h; simp_all +decide [ List.mem_map ] ;
  obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := this; unfold zigzag_step at *; split_ifs at * <;> simp_all
  · have := zigzag_sum_eq_neg choices 0; simp_all +decide [ zigzag_positions ] ;
    have := List.mem_iff_get.mp h₁; obtain ⟨ i, hi ⟩ := this; have := zigzag_sum_eq_neg choices i; simp_all
    unfold zigzag_positions at this; simp_all
    linarith [ this ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt i, show List.length ( List.scanl ( fun pos c => zigzag_step pos c ) ( 0, 0 ) choices ) = choices.length + 1 from by simp +decide [ List.length_scanl ] ] ) ), show ( i : ℤ ) ≥ 0 from Nat.cast_nonneg _ ];
  · have h_contra : ∀ (choices : List Bool) (i : ℕ) (hi : i < (zigzag_positions choices).length), ((zigzag_positions choices).get ⟨i, hi⟩).1 + ((zigzag_positions choices).get ⟨i, hi⟩).2 = -(i : ℤ) := by
      grind +suggestions
    generalize_proofs at *; (
    obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp h₁; specialize h_contra choices i; simp_all +decide ;
    linarith [ h_contra ( Nat.le_of_lt_succ ( by linarith [ Fin.is_lt i, show ( zigzag_positions choices ).length = choices.length + 1 from by simp +decide [ zigzag_positions ] ] ) ), show ( i : ℕ ) ≥ 0 from Nat.zero_le _ ])))

/-- The foldl endpoint is determined by choices. -/
lemma zigzag_foldl_injective (x y : ℤ) (c₁ c₂ : Bool)
    (h : zigzag_step (x, y) c₁ = zigzag_step (x, y) c₂) : c₁ = c₂ := by
  simp [zigzag_step] at h
  cases c₁ <;> cases c₂ <;> simp_all

/-
PROBLEM
The scanl of zigzag_step is injective in the choices (for same start).

PROVIDED SOLUTION
By induction on choices₁, generalizing choices₂ and pos.

Base case (choices₁ = []): h_len says choices₂ = []. Done.

Inductive case (choices₁ = c₁ :: cs₁): h_len gives choices₂ = c₂ :: cs₂ with cs₁.length = cs₂.length.

scanl f pos (c :: cs) = pos :: scanl f (f pos c) cs.

So h_eq gives:
  pos :: scanl f (zigzag_step pos c₁) cs₁ = pos :: scanl f (zigzag_step pos c₂) cs₂

By List.cons.inj, the tails are equal:
  scanl f (zigzag_step pos c₁) cs₁ = scanl f (zigzag_step pos c₂) cs₂

In particular, the heads of these tails are equal (since the scanl of a nonempty list starts with the initial value):
  zigzag_step pos c₁ = zigzag_step pos c₂

By zigzag_foldl_injective: c₁ = c₂.

Then zigzag_step pos c₁ = zigzag_step pos c₂, so:
  scanl f (zigzag_step pos c₁) cs₁ = scanl f (zigzag_step pos c₁) cs₂

By IH (with pos' = zigzag_step pos c₁): cs₁ = cs₂.

Therefore c₁ :: cs₁ = c₂ :: cs₂.
-/
lemma zigzag_scanl_injective (pos : ℤ × ℤ) (choices₁ choices₂ : List Bool)
    (h_len : choices₁.length = choices₂.length)
    (h_eq : choices₁.scanl (fun p c => zigzag_step p c) pos =
            choices₂.scanl (fun p c => zigzag_step p c) pos) :
    choices₁ = choices₂ := by
  induction' choices₁ with c₁ cs₁ ih generalizing choices₂ pos <;> induction' choices₂ with c₂ cs₂ ih' <;> simp_all +decide [ List.scanl ];
  -- By the properties of the zigzag step, we know that if the scanl of two lists are equal, then the initial steps must be equal.
  have h_initial_step : zigzag_step pos c₁ = zigzag_step pos c₂ := by
    cases cs₁ <;> cases cs₂ <;> aesop;
  exact ⟨ zigzag_foldl_injective _ _ _ _ h_initial_step, ih _ _ _ rfl ( by simpa [ h_initial_step ] using h_eq ) ⟩

/-- The zigzag SAW construction from a choice list of length k.
    Returns a SAW of length 2*k from hexOrigin. -/
def zigzagToSAW (choices : List Bool) : SAW hexOrigin (2 * choices.length) :=
  ⟨_, ⟨(buildZigzagWalk choices 0 0).1, buildZigzagWalk_isPath choices 0 0⟩,
   (buildZigzagWalk choices 0 0).2⟩

/-- The endpoint of a zigzag walk is determined by the choices. -/
lemma zigzagToSAW_endpoint (choices : List Bool) :
    (zigzagToSAW choices).w =
    ((choices.foldl zigzag_step (0, 0)).1, (choices.foldl zigzag_step (0, 0)).2, false) := by
  rfl

/-! ## Counting results using the zigzag construction -/

/-
PROBLEM
There are at least 2^k distinct (2k)-step SAWs from the origin.
    Uses the zigzag construction: an injection from Vector Bool k to SAW hexOrigin (2*k).

Do NOT use saw_count_even_lower from SAWZigzag (it is sorry'd).

PROVIDED SOLUTION
We need 2^k ≤ saw_count (2*k) = Fintype.card (SAW hexOrigin (2*k)).

Define f : {l : List Bool // l.length = k} → SAW hexOrigin (2*k) by:
  f ⟨l, hl⟩ = cast (by rw [show 2 * l.length = 2 * k from by omega]) (zigzagToSAW l)

where zigzagToSAW l : SAW hexOrigin (2 * l.length).

Show f is injective: if f ⟨l₁, h₁⟩ = f ⟨l₂, h₂⟩, then the underlying walks have the same support. From the support, we can recover the zigzag positions (even-indexed entries). Since zigzag_positions l = l.scanl zigzag_step (0,0), and zigzag_scanl_injective shows scanl is injective in the choices, we get l₁ = l₂.

Actually, a simpler injectivity argument: if zigzagToSAW l₁ cast to SAW hexOrigin (2*k) = zigzagToSAW l₂ cast to SAW hexOrigin (2*k), then in particular the endpoints are the same. But we showed foldl is NOT injective in choices... Hmm.

Wait, the SAW equality means the underlying Path is equal, which means the Walk is equal, which means the support (vertex list) is equal. From the support, the third vertex (index 2) is determined by the first choice. So if the SAWs are equal, their supports are equal, so the third vertices are equal, so the first choices are equal. By induction, all choices are equal.

More precisely: the walk's support determines the zigzag positions via even-indexed entries. Since zigzag positions are the scanl of the choices (zigzag_positions choices = choices.scanl zigzag_step (0,0)), and scanl is injective (zigzag_scanl_injective), the choices are determined.

The formal approach:
1. Fintype.card {l : List Bool // l.length = k} = 2^k (need to establish this)
2. The map is injective
3. Apply Fintype.card_le_of_injective

For step 1: {l : List Bool // l.length = k} ≃ Vector Bool k, which has card 2^k.

Actually, Vector Bool k has Fintype.card = Fintype.card Bool ^ k = 2^k.

Let me try using Vector Bool k → SAW hexOrigin (2*k) directly.

The function: given v : Vector Bool k, let l = v.toList (with l.length = k). Define zigzagToSAW l : SAW hexOrigin (2*l.length) = SAW hexOrigin (2*k). Use the cast.

Injectivity: if the SAWs are equal, the walks are equal, the supports are equal, the zigzag positions are equal (extracting from support), so the choices are equal (by zigzag_scanl_injective), so v₁.toList = v₂.toList, so v₁ = v₂.

For the card: Fintype.card (Vector Bool k) = 2^k (Fintype.card_vector).

So: 2^k = Fintype.card (Vector Bool k) ≤ Fintype.card (SAW hexOrigin (2*k)) = saw_count (2*k).

We need 2^k ≤ Fintype.card (SAW hexOrigin (2*k)).

Step 1: Define a function f : Vector Bool k → SAW hexOrigin (2*k).
  For v : Vector Bool k, let l = v.toList. Then l.length = k.
  zigzagToSAW l : SAW hexOrigin (2 * l.length) = SAW hexOrigin (2 * k).
  So f v := zigzagToSAW v.toList (after casting 2*v.toList.length to 2*k).

Step 2: f is injective.
  Suppose f v₁ = f v₂. Then zigzagToSAW v₁.toList and zigzagToSAW v₂.toList are equal (after cast).
  The underlying paths (walk + isPath proof) are equal, so the walks are equal.
  The walks have the same support. From the support we can extract that buildZigzagWalk gives the same walk, hence the same vertex sequence. In particular, the zigzag_positions are the same (they can be recovered from the support at even indices). By zigzag_scanl_injective, v₁.toList = v₂.toList. Since Vector.toList is injective (Vector.ext), v₁ = v₂.

Actually, let me try a more direct argument. Two SAWs are equal iff their w (endpoint), p (path), and l (length proof) are equal. Since the paths are paths from hexOrigin to w, and paths on a simple graph from v to w with a given support are unique, if the walks have the same support then they are the same.

But actually for SAW equality, we need the walk to be equal as a walk (not just the support). Two walks with the same support from v to w on a simple graph ARE the same walk (since a simple graph walk is determined by its vertex sequence for paths).

So if the zigzag SAWs are equal, the walks are equal, the supports are equal.

The support of buildZigzagWalk choices x y starts with (x,y,false), (x,y,true), then continues recursively. By examining the support at position 2, we get (zigzag_step (x,y) c).1, (zigzag_step (x,y) c).2, false), which determines c. By induction, the full choice list is determined.

So f is injective.

Step 3: Fintype.card (Vector Bool k) = 2^k.
  By Fintype.card_vector and Fintype.card_bool.

Therefore: 2^k = card (Vector Bool k) ≤ card (SAW hexOrigin (2*k)) = saw_count (2*k).

IMPORTANT: Do NOT use saw_count_even_lower (it's sorry'd). Use zigzagToSAW and zigzag_scanl_injective directly.

After unfold saw_count, the goal is 2^k ≤ Fintype.card (SAW hexOrigin (2*k)).

Define an injection f : Vector Bool k → SAW hexOrigin (2*k) by:
  f v := cast (by simp [v.toList_length]) (zigzagToSAW v.toList)

where the cast adjusts SAW hexOrigin (2 * v.toList.length) to SAW hexOrigin (2 * k) using v.toList_length.

Injectivity: if f v₁ = f v₂, then zigzagToSAW v₁.toList and zigzagToSAW v₂.toList are equal (modulo cast). Since the endpoints and paths are equal, the walk supports are equal. The supports encode the zigzag_positions, and by zigzag_scanl_injective, v₁.toList = v₂.toList. By Vector.toList_injective, v₁ = v₂.

Then: 2^k = Fintype.card Bool ^ k = Fintype.card (Vector Bool k) ≤ Fintype.card (SAW hexOrigin (2*k)).

Use Fintype.card_le_of_injective with f.

IMPORTANT: Do NOT use saw_count_even_lower or saw_count_odd_lower from SAWZigzag.lean (those are sorry'd!). Build the proof from zigzagToSAW and zigzag_scanl_injective.
-/
/-- Convert Fin k → Bool to List Bool of length k. -/
private def finToList (k : ℕ) (f : Fin k → Bool) : List Bool :=
  List.ofFn f

private lemma finToList_length (k : ℕ) (f : Fin k → Bool) :
    (finToList k f).length = k := by
  simp [finToList]

private lemma finToList_injective (k : ℕ) : Function.Injective (finToList k) := by
  intro f g h
  ext i
  have h1 : List.ofFn f = List.ofFn g := h
  have h2 := congr_fun (List.ofFn_injective h1) i
  exact h2

/-
PROBLEM
2^k ≤ saw_count(2k). Proved directly from zigzag construction.

PROVIDED SOLUTION
The goal is to show that the function from (Fin k → Bool) to SAW hexOrigin (2*k), defined via zigzagToSAW, is injective.

If f₁ and f₂ give the same SAW, then zigzagToSAW (finToList k f₁) and zigzagToSAW (finToList k f₂) are equal (after casting). This means the underlying walks have the same support.

The zigzag walk from choices l has support that encodes the choices: the walk visits positions that are determined by List.scanl zigzag_step (0,0) l. Specifically, buildZigzagWalk_support_structure shows every vertex in the support comes from zigzag_positions. And the path structure means the support IS exactly the zigzag_positions (both false and true variants).

Two walks from hexOrigin that are equal as hexGraph.Walk have the same support. From equal supports, we can extract that the zigzag_positions are equal. Since zigzag_positions l = l.scanl zigzag_step (0,0), and zigzag_scanl_injective shows that scanl is injective in the choices list (for same start position and same length), we get finToList k f₁ = finToList k f₂.

The key step: from h_eq (the SAWs are equal), extract that the walks are equal, then the supports are equal, then use zigzag_scanl_injective.

The SAW structure has fields w (endpoint), p (path), l (length proof). If two SAWs are equal, all fields match. In particular, p₁ = p₂ (the paths are equal). Since paths are walks + isPath, the underlying walks are equal. Equal walks have equal supports.

The support of buildZigzagWalk l 0 0 at even indices gives the zigzag_positions. More precisely, zigzag_positions l = l.scanl zigzag_step (0,0). The support starts with (0,0,false), (0,0,true), (next.1, next.2, false), (next.1, next.2, true), etc. So the even-indexed elements (indices 0, 2, 4, ...) give the false-sublattice vertices, whose (fst, snd.fst) coordinates are exactly the zigzag_positions.

From equal supports and equal lengths, we can extract equal zigzag_positions, then use zigzag_scanl_injective to get equal choice lists.

Actually, there might be a simpler approach: just show that SAW equality implies walk support equality, and the support of buildZigzagWalk determines the choices uniquely.
-/
theorem saw_count_even_lower_proved (k : ℕ) : 2 ^ k ≤ saw_count (2 * k) := by
  unfold saw_count
  have h_card : Fintype.card (Fin k → Bool) = 2 ^ k := by
    simp [Fintype.card_bool, Fintype.card_fin]
  rw [← h_card]
  apply Fintype.card_le_of_injective
    (fun f : Fin k → Bool =>
      let l := finToList k f
      have hl : l.length = k := finToList_length k f
      (show SAW hexOrigin (2 * k) from hl ▸ zigzagToSAW l))
  intro f₁ f₂ h_eq
  apply finToList_injective k
  -- The SAWs are equal, so the underlying walks/supports are equal
  -- This means the zigzag positions are the same, so the choices are the same
  have h_support_eq : (zigzagToSAW (finToList k f₁)).p.1.support = (zigzagToSAW (finToList k f₂)).p.1.support := by
    grind +ring;
  -- Since the supports are equal, the zigzag_positions must be equal.
  have h_zigzag_positions_eq : List.map (fun p => (p.1, p.2)) (zigzag_positions (finToList k f₁)) = List.map (fun p => (p.1, p.2)) (zigzag_positions (finToList k f₂)) := by
    have h_zigzag_positions_eq : ∀ (choices : List Bool), List.map (fun p => (p.1, p.2)) (zigzag_positions choices) = List.map (fun v => (v.1, v.2.1)) (List.filter (fun v => v.2.2 = false) (zigzagToSAW choices).p.1.support) := by
      intro choices
      simp [zigzagToSAW];
      induction' choices using List.reverseRecOn with choices ih <;> simp +decide [ *, zigzag_positions ] at *;
      have h_support_eq : ∀ (choices : List Bool) (x y : ℤ), List.map (fun v => (v.1, v.2.1)) (List.filter (fun v => !v.2.2) (buildZigzagWalk choices x y).1.support) = List.scanl (fun pos c => zigzag_step pos c) (x, y) choices := by
        intro choices x y; induction' choices with c choices ih generalizing x y <;> simp_all +decide [ List.scanl ] ;
        · exact Or.inl rfl;
        · convert congr_arg ( fun l => ( x, y ) :: l ) ( ih ( zigzag_step ( x, y ) c |>.1 ) ( zigzag_step ( x, y ) c |>.2 ) ) using 1;
      rw [ h_support_eq ];
    rw [ h_zigzag_positions_eq, h_zigzag_positions_eq, h_support_eq ];
  apply zigzag_scanl_injective (0, 0) (finToList k f₁) (finToList k f₂);
  · simp +decide [ finToList ];
  · unfold zigzag_positions at h_zigzag_positions_eq; aesop;

/-
PROBLEM
3 · 2^k ≤ saw_count(2k+1). Each of the 3 neighbors of hexOrigin
    can start a zigzag walk of 2k additional steps.

The endpoint's same-cell true vertex is not in the zigzag walk support.
    This is the key fact for extending zigzag walks by one step.

PROVIDED SOLUTION
3 * 2^k ≤ saw_count(2k+1). The idea: hexOrigin = (0,0,false) has 3 neighbors in hexGraph: (0,0,true), (1,0,true), (0,1,true). For each neighbor v, a zigzag walk of 2k steps from v gives a (2k+1)-step SAW from hexOrigin.

More precisely: hexOrigin has 3 neighbors. For each neighbor, there are at least 2^k SAWs of length 2k starting from that neighbor (by the even lower bound, applied at the shifted position). But we need to be careful since saw_count counts walks from hexOrigin specifically.

Alternatively: saw_count(2k+1) ≥ 3 * saw_count(2k) / (some constant). Actually by submultiplicativity in reverse, c_{n+1} ≥ c_n is not generally true.

Simpler approach: Each (2k+1)-step SAW from hexOrigin starts with one step to a neighbor, then continues with a 2k-step walk. Each neighbor contributes at least saw_count_equiv(2k) walks (where saw_count_equiv counts from that specific neighbor). By the vertex-independence of saw_count (saw_count_vertex_indep), this equals saw_count(2k). But walks from different first neighbors might overlap (same walk counted differently).

Actually the key fact is: the number of (n+1)-step SAWs from hexOrigin equals the sum over neighbors v of hexOrigin of the number of n-step SAWs from v that avoid hexOrigin. This is ≥ the number of n-step SAWs from v times... no, this doesn't simplify.

Let me try a direct injection approach. We need 3 * 2^k ≤ saw_count(2k+1).

Define an injection from Fin 3 × (Fin k → Bool) → SAW hexOrigin (2k+1).

For (i, f):
- i ∈ Fin 3 determines the first step direction (to one of hexOrigin's 3 neighbors)
- f determines the zigzag choices for the remaining 2k steps

hexOrigin = (0,0,false) has neighbors (0,0,true), (1,0,true), (0,1,true).

After stepping to neighbor v = (0,0,true), (1,0,true), or (0,1,true), we need a 2k-step SAW from v. The zigzag construction gives a 2k-step SAW from any position (x,y,false). But our neighbor v has type true!

For a true-vertex v = (a,b,true), the neighbors are (a,b,false), (a-1,b,false), (a,b-1,false). So from v, the next step goes to one of these false-vertices. Then we can do a zigzag walk from that false-vertex.

So the (2k+1)-step walk from hexOrigin would be:
hexOrigin → neighbor_i (true) → neighbor_j (false) → zigzag...

That's 1 + 1 + 2(k-1) = 2k steps, not 2k+1. Hmm.

Actually: the (2k+1)-step walk should have exactly 2k+1 steps. Starting from hexOrigin:
- Step 1: hexOrigin → neighbor (true vertex), 1 step
- Steps 2 to 2k+1: zigzag of 2k steps from the true neighbor

But zigzag starts from a false vertex! The zigzag construction uses (x,y,false) as start.

Alternative: build a (2k+1)-step walk as 1 step + 2k-step zigzag from the first true neighbor, but we need the zigzag to start from a true vertex... which doesn't match.

Actually wait, from the true neighbor v = (a,b,true), the first zigzag step would go to (a,b,false) (within the same cell). Then (a,b,false) → (a,b,true) is a same-cell step, which is NOT what we want.

Hmm, this is more subtle. Let me think differently.

The zigzag construction builds walks of EVEN length. For ODD length 2k+1, we need an extra step. We can prepend one step from hexOrigin to a neighbor.

hexOrigin = (0,0,false), neighbors: (0,0,true), (1,0,true), (0,1,true).

For each neighbor v, construct a 2k-step zigzag from v. But v is a true vertex, so we need a zigzag construction that starts from a true vertex.

Actually the existing zigzag goes: (x,y,false) → (x,y,true) → (x',y',false) → ...

So starting from (0,0,true), we need: (0,0,true) → (x',y',false) → (x',y',true) → ...

From (0,0,true), the neighbors are (0,0,false), (-1,0,false), (0,-1,false). If we pick one of these, say (-1,0,false), then continue with a 2(k-1)-step zigzag from (-1,0,false), that gives a 2k-step walk from (0,0,true), and prepending the step hexOrigin→(0,0,true) gives a (2k+1)-step walk from hexOrigin.

But then total length = 1 + 1 + 2(k-1) = 2k. We need 2k+1, not 2k.

Hmm. Let me reconsider.

A (2k+1)-step walk from hexOrigin:
- Step 1: (0,0,false) → v (1 step)
- Steps 2 through 2k+1: a 2k-step walk from v

The 2k-step walk from v must be self-avoiding and avoid hexOrigin.

If v is a true neighbor, the 2k-step walk from v: starts at v (true), each pair of steps goes true→false→true. So 2k steps gives k pairs.

From v = (0,0,true): step to (choice among false neighbors) then zigzag. But we need 2k steps from v, not 2k-2.

From v = (0,0,true), 2k steps:
- Step 1: (0,0,true) → w₁ (false),
- Steps 2-2k: (2k-1)-step walk from w₁ (false vertex)
No, (2k-1) is odd, not matching zigzag pattern.

Actually the walk from v = (0,0,true) with 2k steps would go: v → w₁(false) → w₁(true) → w₂(false) → w₂(true) → ... giving k pairs from true to false to true.

But the existing zigzag construction builds walks from false vertices. For a true vertex start, we'd need a shifted version.

OK this is getting complicated. Let me just use a simpler bound.

saw_count(2k+1) ≥ 3 * 2^k.

By submultiplicativity (or rather its consequence):
saw_count(n+1) ≥ saw_count(n) since each n-step SAW extends to at least one (n+1)-step SAW (because hexGraph is 3-regular and connected, and at most 1 neighbor is the previous vertex, and at most 1 is already visited for a walk of length ≥ 2... actually this isn't always true).

Hmm, actually saw_count is NOT necessarily monotone. A SAW might get stuck.

Better approach:
saw_count(1) = 3 (three neighbors of hexOrigin).
saw_count(2k+1) ≥ saw_count(1) * saw_count(2k) / saw_count(0) by submultiplicativity? No, that's wrong.

Actually by submultiplicativity: c_{m+n} ≤ c_m * c_n.

So c_{2k+1} ≤ c_1 * c_{2k} = 3 * c_{2k}. That's the WRONG direction!

We need c_{2k+1} ≥ 3 * 2^k. We know c_{2k} ≥ 2^k. And c_1 = 3. We need a LOWER bound for c_{2k+1}.

Approach: c_{2k+1} = number of (2k+1)-step SAWs from hexOrigin. Each such walk starts with a first step to one of 3 neighbors, then continues with 2k more steps that don't revisit hexOrigin.

So c_{2k+1} = #{(2k+1)-step SAWs} = Σ_{v ~ hexOrigin} #{(v, 2k-step SAW from v avoiding hexOrigin)}.

Now, for any SAW of length 2k from v that never returns to hexOrigin, prepending the edge hexOrigin→v gives a (2k+1)-step SAW from hexOrigin. So we need to lower bound the number of 2k-step SAWs from v that avoid hexOrigin.

For our zigzag construction: the zigzag walk from (0,0,false) visits positions with x+y = 0, -1, -2, ..., -k. hexOrigin = (0,0,false) has x+y = 0. After the first step to a neighbor, we're at x+y ≤ 1 (for true neighbors: (0,0,true) has x+y=0, (1,0,true) has x+y=1, (0,1,true) has x+y=1).

Hmm, this is getting complicated. Let me try yet another approach.

Direct injection: Fin 3 × (Fin k → Bool) → SAW hexOrigin (2k+1).

For neighbor index i ∈ {0,1,2} and choices f : Fin k → Bool:
- i=0: first step to (0,0,true), then 2k-step zigzag from (0,0,true)
- i=1: first step to (1,0,true), then 2k-step zigzag from (1,0,true)
- i=2: first step to (0,1,true), then 2k-step zigzag from (0,1,true)

The 2k-step zigzag from a true vertex (a,b,true):
Step 1: go to some false neighbor, e.g., (a-1,b,false) or (a,b-1,false)
Then 2(k-1) steps of zigzag...

No, this doesn't give exactly 2k steps from a true vertex with the binary choice structure.

Let me try a completely different approach. The 3 neighbors of hexOrigin all go to true vertices. From each true vertex, I go to a false vertex (3 choices, but I fix one), giving 3 possible starting (false) vertices for a 2(k-1)-step zigzag. Then total length = 1 + 1 + 2(k-1) = 2k. Not 2k+1.

Alternatively: extend each 2k-step zigzag SAW by one step. For a 2k-step SAW ending at some vertex w, extend by one step to a neighbor of w that hasn't been visited. This gives at least one (2k+1)-step SAW for each 2k-step SAW.

More precisely: for each 2k-step SAW γ, the endpoint w has 3 neighbors. At most 1 was visited by γ (the previous vertex). So at least 2 extensions exist. But different 2k-step SAWs might extend to the same (2k+1)-step SAW (same walk, different truncation).

Actually, no: a (2k+1)-step SAW has a unique (2k)-step prefix (the first 2k steps). So distinct 2k-step SAWs give distinct (2k+1)-step SAWs after extending. Each 2k-step SAW extends to AT LEAST 1 (actually at least 2 for k ≥ 1) distinct (2k+1)-step SAWs.

Wait, can a 2k-step SAW get stuck? Can w have all 3 neighbors already visited? On the hex lattice (3-regular), w has 3 neighbors. The walk visits at most 2k+1 vertices. If 3 of w's neighbors are visited and w is the endpoint, then w must be surrounded. On the hex lattice, it's possible for a walk to get stuck (visit all 3 neighbors of the endpoint). But only if the walk has length ≥ 3 (since the endpoint needs all 3 neighbors visited, and each neighbor is distinct, so at least 3 vertices other than w are visited as neighbors, plus at least the starting vertex, so length ≥ 4).

For our zigzag walks specifically: the endpoint of a 2k-step zigzag from hexOrigin is ((zigzag choices).1, (zigzag choices).2, false). The positions have x+y = -k. The neighbors of this false vertex are 3 true vertices. The zigzag walk visits vertices with x+y between 0 and -k. The last visited position has x+y = -k. The true neighbors have x+y = -k or -k+1 or -k+1 (depending on the specific neighbor). Are any of these visited?

The zigzag walk visits true vertices at positions with x+y between 0 and -k+1. So a true neighbor with x+y = -k would NOT have been visited (the smallest x+y for a true vertex is -k+1). So at least 1 neighbor is unvisited!

Hmm, but I need to be more precise. The neighbors of (a,b,false) are (a,b,true), (a+1,b,true), (a,b+1,true). Wait no: from the hexGraph definition:

(x,y,false) is adjacent to (x,y,true), (x+1,y,true), (x,y+1,true).

So the three neighbors of the endpoint (x_end, y_end, false) are:
- (x_end, y_end, true): x+y = x_end + y_end = -k
- (x_end+1, y_end, true): x+y = x_end + y_end + 1 = -k+1
- (x_end, y_end+1, true): x+y = x_end + y_end + 1 = -k+1

The zigzag walk visits true vertices at steps 1, 3, ..., 2k-1. At step 2i-1, the true vertex has x+y = -(i-1) (since false vertex at step 2(i-1) has x+y = -(i-1), and the true vertex in the same cell has the same x+y). Wait, that depends on which true vertex.

Actually from the zigzag construction: at step 2i, we're at (x_i, y_i, false) with x_i + y_i = -i. At step 2i+1, we're at (x_i, y_i, true) with x_i + y_i = -i.

So true vertices have x+y = 0, -1, ..., -(k-1).

The neighbor (x_end, y_end, true) has x+y = -k. Since -k is NOT in {0, -1, ..., -(k-1)} (assuming k ≥ 1), this neighbor is NOT visited.

So the zigzag endpoint always has at least 1 unvisited neighbor!

This means: for each 2k-step zigzag SAW, we can extend it by 1 step to a (2k+1)-step SAW. The extension to (x_end, y_end, true) is unique for each zigzag walk (since x_end, y_end are determined by the choices).

So: number of (2k+1)-step SAWs ≥ number of 2k-step zigzag SAWs = 2^k.

But we need 3 * 2^k, not just 2^k.

For the factor 3: the 3 neighbors of hexOrigin are (0,0,true), (1,0,true), (0,1,true). For each neighbor, we can extend the walk by going hexOrigin → neighbor first, giving 3 * (number of 2k-step SAWs from neighbor that avoid hexOrigin).

Hmm, let me think about this differently.

For the factor 3: consider the 3 first-step choices from hexOrigin. After the first step, we're at a true vertex. Then we need a 2k-step SAW from that true vertex.

A 2k-step SAW from a true vertex (a,b,true): goes to one of 3 false neighbors (a,b,false), (a-1,b,false), (a,b-1,false), then continues with a (2k-1)-step walk. But again, 2k-1 is odd, not matching zigzag.

Alternatively, from (a,b,true), do 2 steps: (a,b,true) → one of {(a,b,false), (a-1,b,false), (a,b-1,false)} → (same false vertex's same-cell true neighbor). That's 2 steps from true to true. Then do 2(k-1) more steps of zigzag.

From (a,b,true):
- Step 1: → (a,b,false), Step 2: → (a,b,true)... wait, that goes back to start!
- Step 1: → (a-1,b,false), Step 2: → (a-1,b,true). This is 2 steps, ending at a true vertex with x+y = (a-1)+b = a+b-1.
- Step 1: → (a,b-1,false), Step 2: → (a,b-1,true). This is 2 steps, ending at a true vertex with x+y = a+b-1.

OK so from (a,b,true), we can do 2 steps to get to a position with x+y decreased by 1. Then do 2(k-1) more steps. Total = 2 + 2(k-1) = 2k steps. ✓

But wait, step 1 → (a-1,b,false), step 2 → (a-1,b,true) uses a same-cell edge. But step 2 could also be → (a-1+1,b,true) = (a,b,true) using a different edge, going back! We need to be careful to avoid revisiting.

Actually, (a-1,b,false) has 3 neighbors: (a-1,b,true), (a,b,true), (a-1,b+1,true). If we go to (a-1,b,true) (same cell) or (a-1,b+1,true), we don't revisit. But going to (a,b,true) would revisit!

So from (a,b,true) → (a-1,b,false), we can continue to either:
- (a-1,b,true): OK, not visited
- (a-1,b+1,true): OK, not visited
- (a,b,true): BAD, already visited

So we have 2 choices (binary), giving a zigzag. Then from the new true vertex, repeat.

This is essentially the same zigzag construction but starting from a true vertex!

For 2k-step walks from true vertex (a,b,true):
Step 1: → (a-1,b,false) or (a,b-1,false)  [2 choices, not going back to (a,b,false) since we might come from there]

Hmm, actually from (a,b,true), the first step has 3 choices: (a,b,false), (a-1,b,false), (a,b-1,false). But one of these might be the vertex we came from.

OK this is getting very complicated. Let me just try the subagent with the simpler approach:

3 * 2^k ≤ c_{2k+1} because:
- c_1 = 3, c_{2k} ≥ 2^k (by even lower bound)
- For each 1-step SAW (3 choices) and each 2k-step SAW (≥ 2^k choices), their concatenation gives a (2k+1)-step SAW, BUT only if the 2k-step SAW starts where the 1-step SAW ends, and doesn't revisit any vertex of the 1-step SAW.

By submultiplicativity: c_{2k+1} ≤ c_1 * c_{2k}. Wrong direction again.

OK I think the simplest correct proof is:

c_{2k+1} ≥ 3 * c_{2k} ... WAIT, is this true?

c_1 = 3, c_0 = 1. 3*c_0 = 3 = c_1. ✓
c_3 ≥ 3*c_2? c_2 = 6, c_3 = 12 (?). 3*6 = 18 > 12. So FALSE.

Hmm. So c_{2k+1} ≥ 3 * c_{2k} is NOT true in general!

Then how to get 3 * 2^k ≤ c_{2k+1}?

We have c_{2k} ≥ 2^k. And c_{2k+1} ≥ ... we need a direct construction of 3 * 2^k many (2k+1)-step SAWs.

For each of the 3 neighbors of hexOrigin and each binary choice string of length k, construct a unique (2k+1)-step SAW.

Approach:
- Choose neighbor v ∈ {(0,0,true), (1,0,true), (0,1,true)} (3 choices)
- First step: hexOrigin → v
- From v (true vertex), go to a specific false vertex w depending on v:
  - v = (0,0,true) → w = (0,-1,false) or (-1,0,false)
  - v = (1,0,true) → w = (1,-1,false) or (0,0,false)... wait (0,0,false) = hexOrigin! Can't revisit.

So from v = (1,0,true), the false neighbors are (1,0,false), (0,0,false), (1,-1,false). Can't go to (0,0,false) = hexOrigin. So go to (1,0,false) or (1,-1,false). Then do 2(k-1) zigzag steps from there.

Total steps: 1 (to true) + 1 (to false) + 2(k-1) (zigzag) = 2k steps. Need 2k+1!

Hmm, one off. Let me redo:

(2k+1)-step walk:
- Step 1: hexOrigin → v (true), 1 step
- Steps 2 to 2k+1: 2k steps from v

From v (true vertex), 2k steps. We need a zigzag-like construction for 2k steps from a TRUE vertex.

From v = (a,b,true):
- Step 1: → false neighbor w₁ (avoiding hexOrigin)
- Step 2: → true neighbor of w₁ (same cell = (w₁.x, w₁.y, true))
- Steps 3-4: from (w₁.x, w₁.y, true), go to a false neighbor, then same cell true
- ... continue for k pairs of steps

So 2k steps from a true vertex gives a walk visiting k+1 true vertices and k false vertices.

But step 2 goes to (w₁.x, w₁.y, true), which might be v again! From v = (a,b,true), step 1 → w₁ where w₁ ∈ {(a,b,false), (a-1,b,false), (a,b-1,false)}. Step 2 → (w₁.x, w₁.y, true).

If w₁ = (a,b,false): step 2 → (a,b,true) = v. BAD!
If w₁ = (a-1,b,false): step 2 → (a-1,b,true). OK.
If w₁ = (a,b-1,false): step 2 → (a,b-1,true). OK.

So from v, we must avoid going to (a,b,false) first. That leaves 2 choices for w₁. Then from w₁ we go to (w₁.x, w₁.y, true), and then it's a standard zigzag from there.

So from v (true vertex), with the constraint of not going to (v.x, v.y, false):
- 2 choices for w₁
- Then zigzag from (w₁.x, w₁.y, true): at each subsequent step, 2 choices (the two false neighbors that don't go back)

Wait, this isn't quite right. From (w₁.x, w₁.y, true), the next step goes to one of 3 false neighbors. We need to avoid the one we came from (w₁.x, w₁.y, false? No, we came FROM (w₁.x, w₁.y, false)). Wait, actually we're AT (w₁.x, w₁.y, true), and we came from (w₁.x, w₁.y, false). So we shouldn't go back to (w₁.x, w₁.y, false). The other 2 false neighbors are fair game (as long as they haven't been visited).

So from each true vertex in the walk, there are 2 valid next-step choices (avoiding the false vertex we just came through). Each pair of steps (true→false→true) gives 2 choices. So in 2k steps from a true vertex (with the first constraint), we get... hmm, let me count.

From v (true): 2 choices for step 1 (to a false vertex, avoiding (v.x,v.y,false) or hexOrigin)
Step 2: from w₁ (false) to (w₁.x, w₁.y, true) (same cell, 1 choice)
Steps 3-4: from (w₁.x, w₁.y, true), 2 choices for step 3 (avoiding return), 1 choice for step 4
...
Steps 2i-1 to 2i: 2 choices for odd step, 1 choice for even step
...

Wait, I was confusing myself. The zigzag construction alternates: false → true (same cell) → false (2 choices). So from a false vertex:
- Step 1: same cell true vertex (1 choice)
- Step 2: to a false vertex (2 choices, binary)

From a true vertex:
- Step 1: to a false vertex (2 choices, avoiding the same-cell false)
- Step 2: same cell true vertex (1 choice)

In 2k steps from a true vertex:
- k pairs of (true→false, false→true)
- Each pair has 2 choices for the first step
- Total: 2^k choices

Then: 3 * 2^k total, with 3 neighbor choices and 2^k zigzag choices each.

But we need injectivity! Different (neighbor, choices) must give different SAWs.

For the same neighbor v: different choices give different false vertices at step 1, hence different walk supports. So injectivity within each neighbor is clear.

For different neighbors v₁ ≠ v₂: the second vertex of the walk is different (v₁ ≠ v₂). So the walks are different.

Hence we have an injection Fin 3 × (Fin k → Bool) → SAW hexOrigin (2k+1), giving 3 * 2^k ≤ c_{2k+1}.

But formalizing this requires building a 2k-step walk from a true vertex with the zigzag structure. The existing infrastructure only builds walks from false vertices.

This is getting very involved. Let me just try the subagent and see if it can handle it.

We need 3 * 2^k ≤ saw_count(2k+1).

Key approach: Use saw_count_submult' and saw_count_even_lower_proved.

By submultiplicativity: saw_count(m+n) ≤ saw_count(m) * saw_count(n)
Setting m=1, n=2k: saw_count(2k+1) ≤ saw_count(1) * saw_count(2k) = 3 * saw_count(2k)
This is the WRONG direction (upper bound, not lower bound).

Correct approach: We need a LOWER bound. Use saw_count(2k+1) ≥ saw_count(1) * 2^k / c_0. No, that's wrong too.

Alternative: show that c_{n+1} ≥ c_n for all n. This would give c_{2k+1} ≥ c_{2k} ≥ 2^k. But we need 3 * 2^k.

Actually, let's just use: c_{2k+1} ≥ c_1 * c_{2k} / c_0 is not valid.

Correct approach: Each (2k+1)-step SAW starts with a first step (3 choices from hexOrigin). After the first step to a neighbor v, the remaining 2k steps form a walk from v that doesn't revisit hexOrigin. We need to count these.

For each of the 3 neighbors v of hexOrigin, the number of 2k-step SAWs from v that avoid hexOrigin is at least 2^k (by the zigzag construction starting from v, which visits positions with x+y strictly less than v's x+y, hence never returning to hexOrigin).

Wait, actually the zigzag from hexOrigin itself visits positions with x+y going from 0 downward. If we shift: a zigzag from neighbor v = (a,b,true) would need to be a 2k-step walk from a true vertex.

Hmm, actually there's a much simpler approach. Notice that saw_count 1 = 3 and by the definition of SAW, c_{2k+1} is the number of (2k+1)-step SAWs. Any (2k+1)-step SAW has a unique initial 1-step prefix (giving 3 possible first steps). For each (2k)-step SAW gamma starting from hexOrigin, we can extend it by 1 step as follows: the endpoint of gamma has at least 1 unvisited neighbor (because the hex lattice is infinite and connected, and the walk visits finitely many vertices). So c_{2k+1} ≥ c_{2k} ≥ 2^k. But 2^k is not enough, we need 3 * 2^k.

Let me try: each (2k)-step SAW from hexOrigin ending at w can be extended to at least 1 (2k+1)-step SAW. Also, each 1-step SAW (hexOrigin → v) can be extended to at least 2^k (2k+1)-step SAWs (by appending a 2k-step zigzag from v, shifted appropriately). But zigzag walks start from false vertices and v is true.

Actually let me try yet another approach. We have saw_count_submult': c_{m+n} ≤ c_m * c_n. In particular, c_{2k+1} ≤ c_1 * c_{2k} ≤ 3 * c_{2k}. This is the wrong direction.

What about the other direction? Is there a super-multiplicativity result?

There is no super-multiplicativity in general. But we can use a direct construction.

For n = 2k+1: consider the 3 * 2^k many (2k+1)-step SAWs constructed as follows. For each neighbor v_i (i=0,1,2) and each choice string f : Fin k → Bool:

hexOrigin → v_i → buildZigzagWalk(f)(shifted to start from v_i's position)

The zigzag from v_i: v_i is a true vertex. From v_i, we take 1 step to a false neighbor (deterministic, always go to a specific one), then do a standard zigzag of 2(k-1) steps. But 1 + 1 + 2(k-1) = 2k, so total = 1 + 2k = 2k+1. ✓

Wait! From hexOrigin to v_i (1 step), then from v_i, do 2k more steps (k pairs of true→false→true with binary choices). But v_i is true, so the first sub-step is true→false (2 valid choices), then false→true (1 choice, same cell). Each pair = 2 choices. k pairs = 2^k choices. Total steps from v_i = 2k. Grand total = 1 + 2k = 2k+1. ✓

For the injectivity: different i give different second vertices (v_i), so different SAWs. Same i, different f: the zigzag positions are different, so the walks are different. ✓

For the self-avoidance: hexOrigin is not revisited because the zigzag from v_i moves to positions with strictly decreasing x+y (starting from v_i.x + v_i.y), and hexOrigin has x+y = 0. We need v_i.x + v_i.y ≤ 1, and after 1 step from v_i, x+y decreases. So all subsequent vertices have x+y ≤ v_i.x + v_i.y - 1.

For v_0 = (0,0,true): x+y = 0. After step 1 from v_0, x+y = -1. Subsequent x+y ≤ -1 < 0 = hexOrigin's x+y. But the step from v_0 to a false neighbor: if we go to (-1,0,false) or (0,-1,false), both have x+y = -1. Then same cell true = (-1,0,true) or (0,-1,true), x+y = -1. So hexOrigin at x+y = 0 is NOT revisited. ✓

But wait, v_0 = (0,0,true) has neighbor (0,0,false) = hexOrigin! We must NOT step from v_0 back to hexOrigin. So from v_0, we must go to (-1,0,false) or (0,-1,false) (2 choices), not (0,0,false). This is fine as long as we exclude the "go back to (0,0,false)" option.

For v_1 = (1,0,true): neighbors are (1,0,false), (0,0,false), (1,-1,false). The neighbor (0,0,false) = hexOrigin. So from v_1, we must NOT go to hexOrigin. Go to (1,0,false) or (1,-1,false) (2 choices). ✓

For v_2 = (0,1,true): neighbors are (0,1,false), (-1,1,false), (0,0,false). Again (0,0,false) = hexOrigin. Go to (0,1,false) or (-1,1,false) (2 choices). ✓

So from each v_i, the first step has 2 choices (avoiding hexOrigin). But we said each pair of steps has 2 choices, and k pairs give 2^k choices. The first pair from v_i has only the "don't go back" constraint and the subsequent "don't go back to previous" constraint. Since both constraints eliminate exactly 1 of the 3 options, we always have 2 choices per pair. ✓

So we have 3 * 2^k distinct (2k+1)-step SAWs.

But this is hard to formalize. Let me try a much simpler approach that the subagent might be able to handle:

saw_count(n+1) ≥ saw_count(n) for all n, because each n-step SAW can be extended by at least 1 step (the hex lattice is 3-regular and infinite, so the endpoint always has at least 1 unvisited neighbor).

If this is true, then c_{2k+1} ≥ c_{2k} ≥ 2^k. But we need 3 * 2^k, which is stronger.

Hmm. Actually, c_1 = 3 and c_0 = 1, so c_1 = 3 * c_0. And c_3 ≥ c_2 ≥ 6 = 3*2. 3 * 2^1 = 6 ≤ 12 = c_3. We need 3 * 2^k ≤ c_{2k+1}.

Alternative: show saw_count(n+1) ≥ 2 * saw_count(n) for n ≥ 1. This would give c_{2k+1} ≥ 2 * c_{2k} ≥ 2 * 2^k = 2^{k+1} ≥ 3 * 2^k for k ≥ ... no, 2^{k+1} ≥ 3 * 2^k iff 2 ≥ 3. False.

OK the direct approach won't work with simple monotonicity. We really need 3 * 2^k.

Let me try to use a simpler argument: c_{2k+1} ≥ c_1 * c_{2k} - (overlap). Actually by the inclusion-exclusion type argument, c_{m+n} ≥ c_m * c_n / c_max or something? No, that's not a standard result.

Actually, we have the simple fact: each SAW of length n+1 from hexOrigin restricts (by taking the first step) to a choice of neighbor (3 choices) followed by an n-step SAW from that neighbor not revisiting hexOrigin. So:

c_{n+1} = Σ_{v ~ hexOrigin} |{n-step SAWs from v avoiding hexOrigin}|

For the zigzag construction from each neighbor, all 2^k zigzag SAWs avoid hexOrigin (as argued above). So:

c_{2k+1} ≥ 3 * 2^k (since each of 3 neighbors contributes at least 2^k walks... but wait, the zigzag construction gives 2^k walks from HEXORIGIN, not from each neighbor).

The zigzag from hexOrigin: 2^k walks of length 2k. Each starts at hexOrigin = (0,0,false). The first step goes to (0,0,true). Then from there, the walk uses choices.

For 2k-step walks from the NEIGHBOR (0,0,true), avoiding hexOrigin: we need a zigzag starting from (0,0,true), not from hexOrigin. This is a different construction.

OK, I think the cleanest formal approach is:

Actually, I just had a much better idea. We can prove 3 * 2^k ≤ c_{2k+1} by noting:

c_{2k+1} ≥ c_{2k} (extending each 2k-step SAW by 1 step)
c_{2k} ≥ 2^k (proved)

But c_{2k} might only give c_{2k+1} ≥ c_{2k} ≥ 2^k, and 2^k < 3*2^k.

We need a fundamentally different argument.

Actually, wait. I realize that we can use submultiplicativity plus the lower bound differently.

We have: c_{2k+1} ≥ some explicit lower bound.

For k=0: c_1 = 3 = 3*2^0. ✓
For k≥1: c_{2k+1} ≥ c_{2k+1}... we need to construct the walks directly.

OK, let me just try the subagent with a cleaner approach. The idea: prepend one of 3 initial steps to the zigzag construction. From hexOrigin, go to neighbor v_i, then construct a shifted zigzag from v_i. The shifted zigzag avoids hexOrigin.

But I realize this requires building the shifted zigzag, which requires significant infrastructure.

Let me try the simplest possible approach: maybe c_{2k+1} ≥ 3 * c_{2k} is actually true on this graph? Let me check computationally.

c_0 = 1, c_1 = 3. 3*c_0 = 3 = c_1. ✓
c_2 = 6, c_3 = ?. 3*c_2 = 18. Is c_3 ≥ 18?

On the hex lattice, from hexOrigin: 3 choices for step 1, from each true vertex: 2 choices for step 2 (to a false vertex, not going back), from each false vertex: 2 choices for step 3 (to a true vertex, not going back... wait, a false vertex has 3 true neighbors, and only 1 was just visited, so 2 choices). So c_3 ≥ 3 * 2 * 2 = 12.

Actually c_3 = 12 exactly? Let me check. From (0,0,false):
Step 1: 3 choices → (0,0,true), (1,0,true), (0,1,true)
From (0,0,true): step 2 → (0,-1,false) or (-1,0,false) [not (0,0,false) = hexOrigin]
From (1,0,true): step 2 → (1,0,false) or (1,-1,false) [not (0,0,false) = hexOrigin]
From (0,1,true): step 2 → (0,1,false) or (-1,1,false) [not (0,0,false) = hexOrigin]
Each: 2 choices.
From each false vertex: 3 true neighbors, 1 just visited, possibly more already visited?

From (0,-1,false): neighbors (0,-1,true), (1,-1,true), (0,0,true). (0,0,true) was visited at step 1! So only 2 choices.
From (-1,0,false): neighbors (-1,0,true), (0,0,true), (-1,1,true). (0,0,true) visited! So 2 choices.
Etc.

So c_3 = 3 * 2 * 2 = 12. And 3 * c_2 = 3 * 6 = 18 > 12. So c_3 < 3 * c_2!

So the "naive" c_{2k+1} ≥ 3 * c_{2k} is FALSE.

We need 3 * 2^k ≤ c_{2k+1}, and we verified 3 * 2 = 6 ≤ 12 = c_3. ✓

For k=2: 3 * 4 = 12 ≤ c_5. We need to check c_5 ≥ 12, which should be true since c_5 ≥ c_3 * c_2 / ... hmm, no submultiplicativity doesn't help here.

Actually, c_5 ≥ c_4 ≥ 2^2 = 4. And we need c_5 ≥ 12. Is c_5 ≥ 12?

The hex lattice grows, so c_5 should be large. c_4 ≥ 2^2 = 4, but in reality c_4 is much larger (probably c_4 = 30 or similar on the hex lattice).

OK, I think the right approach is to just try the subagent with a constraint: DO NOT use saw_count_odd_lower from SAWZigzag.lean. Build the proof from scratch.

We need 3 * 2^k ≤ saw_count(2*k+1).

Key insight: Every (2*k)-step SAW from hexOrigin can be extended by at least 1 step (since the hex lattice is 3-regular and infinite, the endpoint of a finite SAW always has at least 1 unvisited neighbor). Moreover, every 1-step SAW from hexOrigin is a unique first step to one of 3 neighbors.

But the best approach is: the number of (n+1)-step SAWs from hexOrigin is at least the number of n-step SAWs, since every n-step SAW can be extended.

So c_{2k+1} ≥ c_{2k} ≥ 2^k. But we need 3 * 2^k, not 2^k.

Better approach: Every (2k+1)-step SAW starts with a first step to one of 3 neighbors of hexOrigin. So c_{2k+1} = Σ_{v ~ hexOrigin} |{(2k)-step SAWs from v avoiding hexOrigin}|.

For each neighbor v of hexOrigin, we need at least 2^k such walks. The zigzag construction gives 2^k (2k)-step SAWs from hexOrigin. If we SHIFT these zigzag walks to start from a neighbor v instead, and verify they avoid hexOrigin, we get 2^k walks per neighbor.

Specifically: translate the zigzag SAW by shifting the start from hexOrigin = (0,0,false) to an adjacent position. But hexOrigin's neighbors are TRUE vertices, and zigzag starts from FALSE vertices.

Alternative cleaner approach: use submultiplicativity.
c_{2k} * c_1 ≥ c_{2k+1}? No, submultiplicativity gives c_{m+n} ≤ c_m * c_n (wrong direction).

Actually, the cleanest approach for formalizing: note that c_1 = 3 and c_{2k} ≥ 2^k (by saw_count_even_lower_proved). Then use the fact that each SAW of length n from hexOrigin can be extended by at least 1 step. More precisely, we can prepend a step.

Actually, for (2k+1)-step SAWs, each one has a unique last step. Removing the last step gives a (2k)-step SAW. So c_{2k+1} ≥ c_{2k} (every (2k)-step SAW extends to at least 1 (2k+1)-step SAW). This gives c_{2k+1} ≥ 2^k.

For the factor 3: each (2k+1)-step SAW has a unique first step (to one of 3 neighbors). Each (2k+1)-step SAW restricts to a unique pair (first step, remaining 2k steps). Two SAWs with different first steps are always different.

For each of the 3 first-step choices, we need to count (2k)-step SAWs from that neighbor avoiding hexOrigin. The zigzag construction from hexOrigin gives SAWs that go to (0,0,true) first, then zigzag. These SAWs, prepended with the step hexOrigin→(0,0,true), give (2k+1)-step SAWs.

But this only gives 2^k SAWs for ONE neighbor, not all 3.

For the other 2 neighbors: we can use analogous zigzag constructions. Specifically:
- From (1,0,true): prepend hexOrigin→(1,0,true) to a shifted zigzag
- From (0,1,true): prepend hexOrigin→(0,1,true) to a shifted zigzag

But the shifted zigzags need to be formally constructed.

Actually, there's a much simpler approach. Use the existing zigzag construction with a modified first step.

The zigzag walk has the form: (0,0,F) → (0,0,T) → (zigzag continues).
This is a (2k)-step walk, giving c_{2k} ≥ 2^k.

For (2k+1)-step walks: consider walks of the form:
(0,0,F) → v_i → (zigzag from v_i)

where v_i is one of the 3 neighbors and the zigzag from v_i is a (2k)-step path.

The (2k)-step zigzag from hexOrigin has the structure:
Step 0: (0,0,F) = hexOrigin
Step 1: (0,0,T)
Step 2: choice → (-1,0,F) or (0,-1,F)
Step 3: same cell T
...

A (2k+1)-step walk prepending hexOrigin → v_i:
hexOrigin → v_i → (2k steps from v_i)

For v_i = (0,0,T): the (2k) steps from (0,0,T) would go to one of its F neighbors (avoiding hexOrigin = (0,0,F)), then continue. This gives 2^k walks (2 choices at each of k zigzag steps, but the first choice avoids hexOrigin).

Wait, from (0,0,T), the F neighbors are (0,0,F) = hexOrigin, (-1,0,F), (0,-1,F). Avoiding hexOrigin leaves 2 choices. Then from each F vertex, same-cell T gives 1 choice, then 2 choices for the next F, etc. So k pairs of steps give 2^k choices (but the first step had 2 instead of 2, so it still works).

So from each v_i, we get 2^k distinct (2k)-step walks (avoiding hexOrigin). Since the 3 v_i's are different, the resulting (2k+1)-step walks are all distinct. Total: 3 * 2^k.

But formalizing this requires building the shifted zigzag, which is substantial work. Let me try a different approach.

SIMPLEST PROOF: Induction on k.
Base case k=0: 3 * 2^0 = 3 = c_1 = saw_count 1. ✓ (saw_count_one)
Inductive step: Assume c_{2k+1} ≥ 3 * 2^k. Show c_{2(k+1)+1} = c_{2k+3} ≥ 3 * 2^{k+1} = 6 * 2^k.

Hmm, we'd need c_{2k+3} ≥ 2 * c_{2k+1}, which requires showing each (2k+1)-step SAW extends to at least 2 (2k+3)-step SAWs. That's hard.

OK let me try yet another angle. Since c_{2k+1} ≤ c_1 * c_{2k} = 3 * c_{2k} (submult), and c_{2k} ≥ 2^k, this gives c_{2k+1} ≤ 3 * c_{2k}. WRONG DIRECTION.

For the LOWER bound, maybe use: c_{2k+1} ≥ c_{2k} because each SAW can be extended. And c_{2k} ≥ 2^k. So c_{2k+1} ≥ 2^k. But we need 3 * 2^k.

Also c_1 = 3, c_3 ≥ c_2 ≥ 2^1 = 2. And c_2 = 6. So c_3 ≥ 6. Is c_3 ≥ 6 ≥ 3*2 = 6? Equality! So it's tight.

Since the subagent is much stronger at proof search, let me just give it the statement and let it try. Maybe it can find a way to use the existing infrastructure.

Use submultiplicativity in the form c_{1 + 2k} ≥ c_1 · c_{2k} / c_0? No, submultiplicativity goes the wrong way.

Instead, use: c_{2k+1} ≥ c_1 · c_{2k} is NOT true from submultiplicativity.

Better approach: c_{2k+1} ≥ c_{2k} because every 2k-step SAW can be extended by at least one step (the hex lattice is infinite and 3-regular, so the endpoint always has at least one unvisited neighbor... actually this might be hard to prove).

Alternative: Use saw_count_step_le_mul_three in reverse? No, that gives upper bounds.

Simplest approach: For k=0, this is c_1 = 3 ≥ 3 (saw_count_one). For k ≥ 1, use submultiplicativity: c_{2k+1} = c_{(2k) + 1}, and by saw_count_submult': c_{2k+1} ≤ c_{2k} · c_1. But this is an UPPER bound.

Actually, saw_count_vertex_independent gives c_n(v) = c_n for all v. Use this: each (2k+1)-step SAW from hexOrigin starts with one step to a neighbor, then continues as a 2k-step walk. The 3 neighbors of hexOrigin are all distinct. From each neighbor v, there are at least 2^k walks of length 2k that avoid hexOrigin and are self-avoiding (by an adapted zigzag construction). Since the walks from different neighbors start at different first vertices, they give different (2k+1)-step SAWs.

But we need: from each neighbor v of hexOrigin, the number of 2k-step SAWs from v that don't revisit hexOrigin is ≥ 2^k.

For the neighbor v = (0, 0, true), its three neighbors are hexOrigin = (0,0,false), (-1,0,false), (0,-1,false). The zigzag construction from v (avoiding hexOrigin) starts from (0,0,true) and goes to either (-1,0,false) or (0,-1,false), then continues zigzagging. This gives 2^k walks.

This is complex to formalize. Let me try the subagent with a simpler approach.

Actually, use: saw_count (2*k+1) ≥ saw_count (2*k) (every SAW can be extended by one step), and saw_count (2*k) ≥ 2^k (from saw_count_even_lower_proved). Then 3 * 2^k ≤ c_{2k+1} requires c_{2k+1} ≥ 3 · c_{2k} which is false.

Let me try: c_{2k+1} ≥ c_1 · ... No.

How about: c_{2*k+1} ≥ c_{2*(k-1)+1} · c_2 / c_1? No.

Actually, the simplest approach is: build 3 · 2^k distinct (2k+1)-step SAWs directly. For each of the 3 neighbors of hexOrigin and each binary string of length k, construct a (2k+1)-step SAW:
1. Step from hexOrigin to neighbor v_i (3 choices)
2. Do a k-step zigzag from v_i (2^k choices)

The 2k+1 steps = 1 + 2k. We need the zigzag from each v_i to NOT revisit hexOrigin.

For v_1 = (0, 0, true): zigzag goes to (-1, 0, false) or (0, -1, false), then continues. The zigzag from (0,0,true) produces vertices with x+y ≤ -1 (for F-vertices after the first step), so never returns to hexOrigin = (0,0,false) which has x+y = 0.

So the zigzag from v_i avoids hexOrigin as long as the starting vertex v_i satisfies: all subsequent F-vertices have x+y < 0.

From (0,0,true), zigzag_step gives (-1,0) or (0,-1), both with x+y = -1. Subsequent steps decrease x+y further. So all F-vertices have x+y ≤ -1 < 0, avoiding hexOrigin.

Similarly for the other two neighbors. This gives an injection from {1,2,3} × {0,1}^k → SAW hexOrigin (2k+1). So c_{2k+1} ≥ 3 · 2^k.

But formalizing this requires building the extended zigzag walks, which is substantial. Let me try the subagent and see if it can handle it.

Actually, maybe there's a simpler proof using existing infrastructure. We have saw_count_even_lower_proved : 2^k ≤ saw_count (2*k). And from saw_count_submult': c_{n+m} ≤ c_n · c_m. So c_{2k+1} = c_{1 + 2k} and we can't use submultiplicativity directly.

But: c_{2k+1} ≥ c_{2k} since every SAW can be extended. Actually we need to prove this. On the infinite hex lattice, every SAW endpoint has at least one unvisited neighbor (since the graph is infinite and the SAW visits finitely many vertices). So c_{n+1} ≥ c_n. This gives c_{2k+1} ≥ c_{2k} ≥ 2^k. But we need 3 · 2^k, not just 2^k.

For the factor 3: c_{2k+1} ≥ c_1 · c_{2k} is FALSE (submultiplicativity gives the UPPER bound c_{1+2k} ≤ c_1 · c_{2k}).

Hmm, try: c_{2k+1} ≥ 3 · c_{2k} / something? No.

Let me try the saw_count_even_lower_proved approach combined with extensions from the 3 neighbors: just try sorry and let the subagent attempt it.

The endpoint of the zigzag walk is (ep.1, ep.2, false) where ep = choices.foldl zigzag_step (0,0). We need to show (ep.1, ep.2, true) is NOT in the walk support.

By buildZigzagWalk_support_structure, every vertex v in the support has v = (pos.1, pos.2, false) or v = (pos.1, pos.2, true) for some pos in zigzag_positions choices (= choices.scanl zigzag_step (0,0)).

If (ep.1, ep.2, true) were in the support, there would exist some pos in zigzag_positions with pos = (ep.1, ep.2). Now ep = choices.foldl zigzag_step (0,0), and zigzag_positions = choices.scanl zigzag_step (0,0). The last element of scanl is equal to foldl. But the TRUE vertices in the walk only correspond to the first k positions (indices 0 to k-1), not the last position (index k).

More precisely: the walk visits (pos_i.1, pos_i.2, true) for i = 0, ..., k-1, and (pos_i.1, pos_i.2, false) for i = 0, ..., k. The endpoint corresponds to pos_k. We need (ep.1, ep.2) = (pos_k.1, pos_k.2) to NOT equal any pos_i for i < k.

By zigzag_positions_nodup, all positions are distinct. The endpoint pos_k is the last element. So pos_k ≠ pos_i for all i < k. This means (ep.1, ep.2, true) ≠ (pos_i.1, pos_i.2, true) for all i < k, so it's not among the true vertices in the support.

Key lemmas: buildZigzagWalk_support_structure, zigzag_positions_nodup, zigzag_sum_eq_neg (the sum x+y at position i is -i, so different indices give different sums).
-/
lemma zigzag_endpoint_true_not_in_support (choices : List Bool) :
    let ep := choices.foldl zigzag_step (0, 0)
    (ep.1, ep.2, true) ∉ (buildZigzagWalk choices 0 0).1.support := by
  induction' choices using List.reverseRecOn with choices ih <;> simp_all +decide [ List.foldl ];
  -- By definition of `buildZigzagWalk`, the support of the new walk includes the support of the previous walk plus the new steps.
  have h_support : (buildZigzagWalk (choices ++ [ih]) 0 0).val.support = (buildZigzagWalk choices 0 0).val.support ++ (buildZigzagWalk [ih] (List.foldl zigzag_step (0, 0) choices).1 (List.foldl zigzag_step (0, 0) choices).2).val.support.tail := by
    induction' choices using List.reverseRecOn with choices ih <;> simp_all +decide [ List.foldl ];
    · cases ih <;> rfl;
    · have h_support : ∀ (choices : List Bool) (x y : ℤ) (ih : Bool), (buildZigzagWalk (choices ++ [ih]) x y).val.support = (buildZigzagWalk choices x y).val.support ++ (buildZigzagWalk [ih] (List.foldl zigzag_step (x, y) choices).1 (List.foldl zigzag_step (x, y) choices).2).val.support.tail := by
        intros choices x y ih; induction' choices with choices ih generalizing x y <;> simp_all +decide [ List.foldl ] ;
        · cases ih <;> rfl;
        · rename_i k hk₁ hk₂;
          convert congr_arg ( fun l => [ ( x, y, false ) ] ++ [ ( x, y, true ) ] ++ l ) ( hk₂ ( zigzag_step ( x, y ) choices |>.1 ) ( zigzag_step ( x, y ) choices |>.2 ) ) using 1;
      convert h_support ( choices ++ [ ih ] ) 0 0 _ using 1;
  cases ih <;> simp_all +decide [ zigzag_step ];
  · constructor;
    · intro h
      have h_support : ∀ v ∈ (buildZigzagWalk choices 0 0).val.support, ∃ pos ∈ zigzag_positions choices |>.map (fun p => (p.1 + 0, p.2 + 0)), v = (pos.1, pos.2, false) ∨ v = (pos.1, pos.2, true) := by
        convert buildZigzagWalk_support_structure choices 0 0 using 1
      generalize_proofs at *;
      obtain ⟨ pos, hpos, hpos' ⟩ := h_support _ h; simp_all +decide [ zigzag_positions ] ;
      have h_scanl : ∀ (choices : List Bool) (pos : ℤ × ℤ), (List.foldl zigzag_step pos choices).1 + (List.foldl zigzag_step pos choices).2 = pos.1 + pos.2 - choices.length := by
        intro choices pos; induction' choices using List.reverseRecOn with choices ih <;> simp_all +decide [ zigzag_step ] ; ring;
        split_ifs <;> linarith! [ zigzag_step_sum ( List.foldl zigzag_step pos choices ) ih ] ;
      generalize_proofs at *; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have := h_support _ _ |>.2 h; simp_all +decide [ List.mem_iff_get ] ;
      obtain ⟨ n, hn ⟩ := this; have := h_scanl ( List.take n choices ) 0 0; simp_all +decide ;
      grind;
    · erw [ List.mem_cons, List.mem_singleton ] ; aesop ( simp_config := { decide := true } ) ;
  · constructor;
    · intro h;
      have := buildZigzagWalk_support_structure choices 0 0 _ h; simp_all +decide [ zigzag_positions ] ;
      have := zigzag_sum_eq_neg choices ( List.idxOf ( ( List.foldl zigzag_step ( 0, 0 ) choices ).1, ( List.foldl zigzag_step ( 0, 0 ) choices ).2 - 1 ) ( List.scanl ( fun pos c => zigzag_step pos c ) ( 0, 0 ) choices ) ) ?_ <;> simp_all +decide [ List.idxOf_lt_length_iff ];
      any_goals exact Nat.le_of_lt_succ ( List.idxOf_lt_length_iff.mpr this |> Nat.lt_of_lt_of_le <| by simp +decide [ zigzag_positions ] );
      have := zigzag_sum_eq_neg choices ( List.length choices ) ?_ <;> simp_all +decide [ zigzag_positions ];
      grind;
    · erw [ List.mem_cons, List.mem_singleton ] ; aesop ( simp_config := { decide := true } ) ;

/-- Extend a zigzag SAW by one step to the same-cell true vertex. -/
def extendZigzagSAW (choices : List Bool) : SAW hexOrigin (2 * choices.length + 1) :=
  let w := buildZigzagWalk choices 0 0
  let ep := choices.foldl zigzag_step (0, 0)
  let adj : hexGraph.Adj _ _ := hex_adj_same_cell ep.1 ep.2
  let hp := buildZigzagWalk_isPath choices 0 0
  let hnin := zigzag_endpoint_true_not_in_support choices
  ⟨(ep.1, ep.2, true),
   ⟨w.1.concat adj, hp.concat hnin adj⟩,
   by simp [SimpleGraph.Walk.length_concat, w.2]⟩

/-- 2^n ≤ c_n² for all n.
    By submultiplicativity: c_n² = c_n · c_n ≥ c_{n+n} = c_{2n} ≥ 2^n.
    This bypasses the need for saw_count_odd_lower entirely. -/
theorem saw_count_sq_ge_two_pow_proved (n : ℕ) (_hn : 1 ≤ n) :
    2 ^ n ≤ saw_count n ^ 2 := by
  have h_submult := saw_count_submult' n n
  have h_even := saw_count_even_lower_proved n
  calc 2 ^ n ≤ saw_count (2 * n) := h_even
    _ = saw_count (n + n) := by ring_nf
    _ ≤ saw_count n * saw_count n := h_submult
    _ = saw_count n ^ 2 := by ring

end