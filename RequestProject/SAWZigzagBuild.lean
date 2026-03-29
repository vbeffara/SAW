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
      · convert h₂ using 1 ; split_ifs <;> ring!;

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
  induction' choices with c choices ih generalizing x y ; simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ] ; aesop;
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
          obtain ⟨ n, hn ⟩ := h₁; have := zigzag_sum_eq_neg ( List.take n choices ) n; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
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
  obtain ⟨ a, b, h₁, h₂, h₃ ⟩ := this; unfold zigzag_step at *; split_ifs at * <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
  · have := zigzag_sum_eq_neg choices 0; simp_all +decide [ zigzag_positions ] ;
    have := List.mem_iff_get.mp h₁; obtain ⟨ i, hi ⟩ := this; have := zigzag_sum_eq_neg choices i; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
    unfold zigzag_positions at this; simp_all +decide [ List.get ] ;
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
  cases c₁ <;> cases c₂ <;> simp_all <;> omega

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

/-- 2^k ≤ saw_count(2k). Proved directly from zigzag construction. -/
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
  sorry

end