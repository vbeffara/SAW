/-
# Submultiplicativity of self-avoiding walk counts

This file proves that the number of self-avoiding walks on the hexagonal
lattice is submultiplicative: c_{n+m} ≤ c_n · c_m.

The proof uses:
1. Walk splitting: any walk of length n+m can be split at step n
2. Graph automorphisms: translation and sublattice flip
3. Vertex independence: the SAW count is the same from any vertex
-/

import RequestProject.SAW

open Real Complex ComplexConjugate Filter Topology

noncomputable section

/-! ## Graph automorphisms of the hexagonal lattice -/

/-- Translation of a hex vertex by (dx, dy). This is a graph automorphism. -/
def hexTranslate (dx dy : ℤ) (v : HexVertex) : HexVertex :=
  (v.1 + dx, v.2.1 + dy, v.2.2)

/-
PROBLEM
Translation preserves adjacency.

PROVIDED SOLUTION
Unfold hexTranslate and hexGraph. The adjacency conditions involve equalities on coordinates like v.1 = w.1 or v.1 + 1 = w.1. Adding dx and dy to both sides preserves these equalities. Split into cases on the Bool components and use omega.
-/
lemma hexTranslate_adj (dx dy : ℤ) (v w : HexVertex) :
    hexGraph.Adj v w ↔ hexGraph.Adj (hexTranslate dx dy v) (hexTranslate dx dy w) := by
      unfold hexGraph hexTranslate; simp
      grind +ring

/-
PROBLEM
Translation is injective.

PROVIDED SOLUTION
Unfold hexTranslate. If (v.1 + dx, v.2.1 + dy, v.2.2) = (w.1 + dx, w.2.1 + dy, w.2.2), then v.1 = w.1, v.2.1 = w.2.1, v.2.2 = w.2.2, so v = w.
-/
lemma hexTranslate_injective (dx dy : ℤ) : Function.Injective (hexTranslate dx dy) := by
  intro v w h;
  unfold hexTranslate at *; aesop;

/-
PROBLEM
Inverse of translation.

PROVIDED SOLUTION
Unfold hexTranslate. (v.1 + dx + (-dx), v.2.1 + dy + (-dy), v.2.2) = (v.1, v.2.1, v.2.2) = v. Use omega or ring for the integer arithmetic.
-/
lemma hexTranslate_inv (dx dy : ℤ) (v : HexVertex) :
    hexTranslate (-dx) (-dy) (hexTranslate dx dy v) = v := by
      unfold hexTranslate; aesop;

/-- The sublattice flip: (x, y, b) ↦ (-x, -y, !b).
    This is a graph automorphism that exchanges the two sublattices. -/
def hexFlip (v : HexVertex) : HexVertex := (-v.1, -v.2.1, !v.2.2)

/-
PROBLEM
The flip preserves adjacency.

PROVIDED SOLUTION
Unfold hexFlip and hexGraph. Need to show adjacency is preserved by (x,y,b) ↦ (-x,-y,!b). Case split on the Bool values of v and w. For v=(x,y,false), w=(x',y',true): hexGraph says (x=x' ∧ y=y') ∨ (x+1=x' ∧ y=y') ∨ (x=x' ∧ y+1=y'). After flip: hexFlip v = (-x,-y,true), hexFlip w = (-x',-y',false). hexGraph for (true, false) says ((-x')=(-x) ∧ (-y')=(-y)) ∨ ((-x')+1=(-x) ∧ (-y')=(-y)) ∨ ((-x')=(-x) ∧ (-y')+1=(-y)). The first case: x=x' ∧ y=y' ↔ -x'=-x ∧ -y'=-y. The second case: x+1=x' ↔ -x'+1=-x (since x+1=x' means -x'=-x-1, so -x'+1=-x). Third case: y+1=y' ↔ -y'+1=-y. So the conditions match. Use omega for each case.
-/
lemma hexFlip_adj (v w : HexVertex) :
    hexGraph.Adj v w ↔ hexGraph.Adj (hexFlip v) (hexFlip w) := by
      unfold hexGraph hexFlip;
      grind +ring

/-
PROBLEM
The flip is an involution.

PROVIDED SOLUTION
For any v = (x, y, b), hexFlip (hexFlip v) = hexFlip (-x, -y, !b) = (x, y, !!b) = (x, y, b) = v. Use simp with Bool.not_not.
-/
lemma hexFlip_involutive : Function.Involutive hexFlip := by
  exact fun v => by cases v; simp +decide [ hexFlip ] ;

/-- The flip is injective. -/
lemma hexFlip_injective : Function.Injective hexFlip :=
  hexFlip_involutive.injective

/-
PROBLEM
hexFlip maps origin to (0, 0, true).

PROVIDED SOLUTION
hexFlip (0, 0, false) = (-0, -0, !false) = (0, 0, true). Just unfold and simp.
-/
lemma hexFlip_origin : hexFlip hexOrigin = (0, 0, true) := by
  rfl

/-! ## Walk and path mapping under automorphisms -/

/-- Map a walk under translation. -/
def hexTranslate_walk (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    hexGraph.Walk (hexTranslate dx dy v) (hexTranslate dx dy w) := by
  induction p with
  | nil => exact .nil
  | cons hadj _ ih => exact .cons ((hexTranslate_adj dx dy _ _).mp hadj) ih

/-
PROBLEM
Translated walk has the same length.

PROVIDED SOLUTION
By induction on the walk p. For nil, both lengths are 0. For cons, both sides increase by 1, and we use the induction hypothesis.
-/
lemma hexTranslate_walk_length (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexTranslate_walk dx dy p).length = p.length := by
      -- We can prove this by induction on the walk p.
      induction' p with v w p ih;
      · rfl;
      · unfold hexTranslate_walk; aesop;

/-
PROBLEM
Translation preserves the path property.

PROVIDED SOLUTION
By induction on p. Need to show support is nodup. The translated walk has support obtained by applying hexTranslate to each vertex. Since hexTranslate is injective (hexTranslate_injective), applying an injective function to a nodup list gives a nodup list (List.Nodup.map).
-/
lemma hexTranslate_walk_isPath (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) : (hexTranslate_walk dx dy p).IsPath := by
      -- The support of the translated walk is the image of the support of the original walk under the function (fun x => hexTranslate dx dy x).
      have h_support_image : (hexTranslate_walk dx dy p).support = List.map (fun x => hexTranslate dx dy x) p.support := by
        induction' p with v w p ih <;> simp_all +decide [ List.map, hexTranslate_walk ];
      simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      exact List.Nodup.map ( fun x y hxy => by unfold hexTranslate at hxy; aesop ) hp

/-- Map a walk under the flip. -/
def hexFlip_walk {v w : HexVertex} (p : hexGraph.Walk v w) :
    hexGraph.Walk (hexFlip v) (hexFlip w) := by
  induction p with
  | nil => exact .nil
  | cons hadj _ ih => exact .cons ((hexFlip_adj _ _).mp hadj) ih

/-
PROBLEM
Flipped walk has the same length.

PROVIDED SOLUTION
By induction on the walk p. Same as hexTranslate_walk_length.
-/
lemma hexFlip_walk_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexFlip_walk p).length = p.length := by
      -- We can prove this by induction on the length of the walk.
      induction' p with v w p ih;
      · rfl;
      · simp_all +decide [ hexFlip_walk ]

/-
PROBLEM
Flip preserves the path property.

PROVIDED SOLUTION
The support of hexFlip_walk is the map of hexFlip over the support of p. Since hexFlip is injective and p.support is nodup (because p is a path), the mapped list is also nodup. First prove that support of hexFlip_walk p equals List.map hexFlip p.support by induction on p. Then use List.Nodup.map with hexFlip_injective.
-/
lemma hexFlip_walk_isPath {v w : HexVertex} (p : hexGraph.Walk v w)
    (hp : p.IsPath) : (hexFlip_walk p).IsPath := by
      have h_support : (hexFlip_walk p).support = List.map hexFlip p.support := by
        induction' p with v w p ih <;> simp_all +decide [ List.map, hexFlip_walk ];
      simp_all +decide [ SimpleGraph.Walk.isPath_def ];
      exact List.Nodup.map ( by exact hexFlip_injective ) hp

/-! ## SAW count is vertex-independent -/

/-- Translate a SAW from vertex v to a SAW from the translated vertex. -/
def saw_translate (dx dy : ℤ) (v : HexVertex) (n : ℕ) (s : SAW v n) :
    SAW (hexTranslate dx dy v) n :=
  ⟨hexTranslate dx dy s.w,
   ⟨hexTranslate_walk dx dy s.p.1, hexTranslate_walk_isPath dx dy s.p.1 s.p.2⟩,
   by rw [hexTranslate_walk_length]; exact s.l⟩

/-
PROBLEM
The support of a translated walk equals the map of hexTranslate over the original support.

PROVIDED SOLUTION
By induction on p. For nil: support is [v], map is [hexTranslate dx dy v]. The translated walk is nil with support [hexTranslate dx dy v]. For cons h q: support is v :: q.support, map is hexTranslate dx dy v :: map of q.support. The translated walk is cons _ (hexTranslate_walk dx dy q), whose support is hexTranslate dx dy v :: (hexTranslate_walk dx dy q).support. By IH, (hexTranslate_walk dx dy q).support = q.support.map (hexTranslate dx dy).
-/
lemma hexTranslate_walk_support (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexTranslate_walk dx dy p).support = p.support.map (hexTranslate dx dy) := by
      induction p <;> simp_all +decide [ hexTranslate_walk ]

/-
PROBLEM
hexTranslate_walk is injective: if two walks from the same endpoints translate to the same walk,
    they are equal.

PROVIDED SOLUTION
Use hexTranslate_walk_support. From h, the supports are equal: p.support.map (hexTranslate dx dy) = q.support.map (hexTranslate dx dy). Since hexTranslate is injective, List.map_injective gives p.support = q.support. Then use the fact that on a simple graph, a walk between fixed endpoints is determined by its support (for paths this is clear; for general walks we can also use that consecutive vertices must be adjacent and there's only one edge between adjacent vertices in a simple graph).
-/
lemma hexTranslate_walk_injective (dx dy : ℤ) {v w : HexVertex}
    (p q : hexGraph.Walk v w)
    (h : hexTranslate_walk dx dy p = hexTranslate_walk dx dy q) : p = q := by
      -- Since hexTranslate is injective, if the translated walks are equal, then their supports must be equal.
      have h_support : p.support = q.support := by
        have h_support : p.support.map (hexTranslate dx dy) = q.support.map (hexTranslate dx dy) := by
          rw [ ← hexTranslate_walk_support, ← hexTranslate_walk_support, h ];
        exact List.map_injective_iff.mpr ( hexTranslate_injective dx dy ) h_support;
      exact SimpleGraph.Walk.ext_support h_support

/-
PROBLEM
The support of a flipped walk equals the map of hexFlip over the original support.

PROVIDED SOLUTION
By induction on p, same as hexTranslate_walk_support.
-/
lemma hexFlip_walk_support {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexFlip_walk p).support = p.support.map hexFlip := by
      induction p <;> simp_all +decide [ hexFlip_walk ]

/-
PROBLEM
hexFlip_walk is injective.

PROVIDED SOLUTION
Same approach as hexTranslate_walk_injective. Use hexFlip_walk_support and hexFlip_injective.
-/
lemma hexFlip_walk_injective {v w : HexVertex}
    (p q : hexGraph.Walk v w)
    (h : hexFlip_walk p = hexFlip_walk q) : p = q := by
      apply_fun (fun x => x.support) at h;
      rw [ hexFlip_walk_support, hexFlip_walk_support ] at h;
      have h_support : p.support = q.support := by
        exact List.map_injective_iff.mpr ( hexFlip_injective ) h;
      exact SimpleGraph.Walk.ext_support h_support

/-
PROBLEM
The SAW translation map is injective.

PROVIDED SOLUTION
Suppose saw_translate dx dy v n s₁ = saw_translate dx dy v n s₂. Unfolding saw_translate, this means the endpoints and paths are equal after translation. Since hexTranslate is injective, s₁.w = s₂.w. For the paths: the translated walks hexTranslate_walk dx dy s₁.p.1 = hexTranslate_walk dx dy s₂.p.1, so by hexTranslate_walk_injective, s₁.p.1 = s₂.p.1. Then use ext/cases on the SAW structure to conclude s₁ = s₂.
-/
lemma saw_translate_injective (dx dy : ℤ) (v : HexVertex) (n : ℕ) :
    Function.Injective (saw_translate dx dy v n) := by
      intro s₁ s₂ h_eq;
      unfold saw_translate at h_eq;
      rcases s₁ with ⟨ ⟨ w₁, p₁ ⟩, hp₁ ⟩ ; rcases s₂ with ⟨ ⟨ w₂, p₂ ⟩, hp₂ ⟩ ; simp_all
      cases p₁ ; cases p₂ ; simp_all +decide [ hexTranslate ];
      cases hp₁ ; cases hp₂ ; simp_all +decide [ hexTranslate_walk ];
      convert hexTranslate_walk_injective dx dy _ _ _ using 1;
      rotate_left;
      exact v
      exact ( w₁, ‹_›, ‹_› );
      exact ‹hexGraph.Walk v ( w₁, _, _ ) ›.copy ( by simp ) ( by simp +decide [ h_eq ] );
      exact ‹hexGraph.Walk v ( w₂, _, _ ) ›.copy ( by simp  ) ( by simp +decide [ h_eq ] );
      · aesop;
      · aesop

/-
PROBLEM
For same-sublattice vertices, SAW counts are equal (by translation).

PROVIDED SOLUTION
Use Fintype.card_eq.mpr to show a bijection between SAW (x, y, b) n and SAW (0, 0, b) n. The bijection is given by saw_translate (-x) (-y). The forward map sends SAW (x,y,b) to SAW (x+(-x), y+(-y), b) = SAW (0,0,b). The inverse is saw_translate x y. Use saw_translate_injective for injectivity. For surjectivity: any SAW from (0,0,b) can be translated to SAW from (x,y,b) by saw_translate x y, then translating back by (-x,-y) gives the original. Use Fintype.card_le_of_injective in both directions.
-/
lemma saw_count_same_sublattice (x y : ℤ) (b : Bool) (n : ℕ) :
    Fintype.card (SAW (x, y, b) n) = Fintype.card (SAW (0, 0, b) n) := by
      apply le_antisymm;
      · have h_card_le : Fintype.card (SAW (x, y, b) n) ≤ Fintype.card (SAW (0, 0, b) n) := by
          have : Function.Injective (saw_translate (-x) (-y) (x, y, b) n) := by
            exact saw_translate_injective (-x) (-y) (x, y, b) n
          convert Fintype.card_le_of_injective _ this using 1;
          unfold hexTranslate; aesop;
        exact h_card_le;
      · convert Fintype.card_le_of_injective _ ( saw_translate_injective x y ( 0, 0, b ) n ) using 1;
        unfold hexTranslate; aesop;

/-- Flip a SAW: maps SAW from v to SAW from hexFlip v. -/
def saw_flip {v : HexVertex} {n : ℕ} (s : SAW v n) :
    SAW (hexFlip v) n :=
  ⟨hexFlip s.w,
   ⟨hexFlip_walk s.p.1, hexFlip_walk_isPath s.p.1 s.p.2⟩,
   by rw [hexFlip_walk_length]; exact s.l⟩

/-
PROBLEM
saw_flip is injective.

PROVIDED SOLUTION
Same approach as saw_translate_injective. If saw_flip s₁ = saw_flip s₂, then hexFlip s₁.w = hexFlip s₂.w, so s₁.w = s₂.w by hexFlip_injective. And hexFlip_walk s₁.p.1 = hexFlip_walk s₂.p.1, so s₁.p.1 = s₂.p.1 by hexFlip_walk_injective. Then use ext.
-/
lemma saw_flip_injective {v : HexVertex} {n : ℕ} :
    Function.Injective (@saw_flip v n) := by
      intro s₁ s₂ h_eq;
      cases s₁ ; cases s₂ ; simp_all
      injection h_eq;
      have h_flip_eq : ∀ {v w : HexVertex}, hexFlip v = hexFlip w → v = w := by
        unfold hexFlip; aesop;
      have h_flip_walk_eq : ∀ {v w : HexVertex} {p q : hexGraph.Walk v w}, hexFlip_walk p = hexFlip_walk q → p = q := by
        exact fun {v w} {p q} a => hexFlip_walk_injective p q a;
      grind

/-
PROBLEM
For opposite-sublattice vertices, SAW counts are equal (by flip).

PROVIDED SOLUTION
Apply le_antisymm with two injections. Forward: saw_flip maps SAW (0,0,true) n to SAW (hexFlip (0,0,true)) n. Since hexFlip (0,0,true) = hexFlip (hexFlip hexOrigin) = hexOrigin (by hexFlip_involutive), we can cast to SAW hexOrigin n. Use saw_flip_injective. Backward: saw_flip maps SAW hexOrigin n to SAW (hexFlip hexOrigin) n = SAW (0,0,true) n (by hexFlip_origin). Use saw_flip_injective. Use Fintype.card_le_of_injective in both directions.
-/
lemma saw_count_flip (n : ℕ) :
    Fintype.card (SAW (0, 0, true) n) = saw_count n := by
      apply le_antisymm;
      · convert Fintype.card_le_of_injective _ ( saw_flip_injective ) using 1;
      · -- By Lemma~\ref{lem:saw_flip_injective}, we can use `saw_flip` as the worlds `SAW hexOrigin n → SAW (0,0,true n)` for Fintype.card_le_of_injective.
        apply Fintype.card_le_of_injective saw_flip saw_flip_injective

/-
PROBLEM
SAW count is the same from any vertex.

PROVIDED SOLUTION
Decompose v = (x, y, b). If b = false, use saw_count_same_sublattice to get card(SAW (x,y,false) n) = card(SAW (0,0,false) n) = saw_count n. If b = true, use saw_count_same_sublattice to get card(SAW (x,y,true) n) = card(SAW (0,0,true) n) and then saw_count_flip to get card(SAW (0,0,true) n) = saw_count n.
-/
lemma saw_count_vertex_independent (v : HexVertex) (n : ℕ) :
    Fintype.card (SAW v n) = saw_count n := by
      -- Decouple theroles of length and adjacency in the walk.
      cases' v with x y b; (
      cases' y with y b; cases' b with b; (
      convert saw_count_same_sublattice x y false n using 1);
      rw [ ← saw_count_flip, saw_count_same_sublattice ]);

/-! ## Walk splitting -/

/-
PROBLEM
Take the first n steps of a path preserves the path property.

PROVIDED SOLUTION
By induction on p. For nil: take n of nil is nil, which is a path. For cons h q: if n = 0, take 0 gives nil (a path). If n = succ k, take gives cons h (q.take k). By IH, q.take k is a path. We need to show u ∉ (q.take k).support. Since p = cons h q is a path, u ∉ q.support (by support_nodup). Since (q.take k).support is a subset of q.support (or rather, a prefix), u ∉ (q.take k).support either. Actually, we can show that support of (q.take k) is a sublist of support of q by induction, and then use that u ∉ q.support implies u ∉ (q.take k).support.
-/
lemma walk_take_isPath {v w : V} [DecidableEq V] {G : SimpleGraph V}
    (p : G.Walk v w) (hp : p.IsPath) (n : ℕ) :
    (p.take n).IsPath := by
      cases' hp with hp₁ hp₂;
      have h_support : ∀ {p : G.Walk v w}, p.support.Nodup → ∀ n, List.Nodup (List.take (n + 1) p.support) := by
        exact fun { p } hp n => hp.sublist ( List.take_sublist _ _ );
      have := @h_support p hp₂ n; simp_all +decide [ SimpleGraph.Walk.isPath_def ] ;
      convert h_support hp₂ n using 1;
      exact SimpleGraph.Walk.take_support_eq_support_take_succ p n

/-
PROBLEM
Drop the first n steps of a path preserves the path property.

PROVIDED SOLUTION
By induction on p. For nil: drop n of nil is nil, which is a path. For cons h q: if n = 0, drop 0 gives cons h q (which is already a path by hp). If n = succ k, drop gives q.drop k. Since p = cons h q is a path, q is also a path (by IsPath.of_cons). By IH, q.drop k is a path.
-/
lemma walk_drop_isPath {v w : V} [DecidableEq V] {G : SimpleGraph V}
    (p : G.Walk v w) (hp : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath := by
      induction' p with _ _ _ _ ih generalizing n;
      · cases n <;> aesop;
      · cases n <;> simp_all +decide [ SimpleGraph.Walk.drop, SimpleGraph.Walk.cons_isPath_iff ]

/-! ## The submultiplicativity injection -/

/-
PROBLEM
The submultiplicativity of SAW counts: c_{n+m} ≤ c_n · c_m.
    This follows from the injection that splits an (n+m)-step SAW at step n
    and translates the second half to start from the origin.

PROVIDED SOLUTION
We need to show saw_count (n + m) ≤ saw_count n * saw_count m, i.e. Fintype.card (SAW hexOrigin (n+m)) ≤ Fintype.card (SAW hexOrigin n) * Fintype.card (SAW hexOrigin m).

Build an injection f : SAW hexOrigin (n+m) → SAW hexOrigin n × SAW hexOrigin m, then use Fintype.card_le_of_injective and Fintype.card_prod.

The injection: given s : SAW hexOrigin (n+m), let p = s.p.1 (the walk of length n+m). Let u = p.getVert n (the vertex at step n).
- First component: SAW hexOrigin n. Take p.take n. This has length min(n, n+m) = n (since n ≤ n+m). It's a path by walk_take_isPath.
- Second component: SAW hexOrigin m. Take p.drop n. This is a walk from u to s.w of length (n+m) - n. But we need length = m exactly. The length of p.drop n is p.length - n = (n+m) - n = m (using s.l). It's a path by walk_drop_isPath. It's a SAW from u, not from origin. Use saw_count_vertex_independent to know the counts are the same, but for the injection we need to actually translate the walk. Use hexTranslate or hexFlip + hexTranslate to move u to hexOrigin.

Actually, for the injection approach, we don't need to translate. We need an injection into SAW hexOrigin n × SAW hexOrigin m. The first factor is fine. For the second, we need to map SAW u m → SAW hexOrigin m injectively, and we already have this through translation.

Define f(s) = (first_part, translate(second_part)). Injectivity: if f(s₁) = f(s₂), then the first parts are equal, so s₁ and s₂ agree on the first n+1 vertices. In particular u₁ = u₂ (same intermediate vertex). Then the second parts agree after translation, so the translations are equal, and since translation is injective, the second parts are equal. Together, s₁ = s₂.

Key technical details:
- Walk.take_length: (p.take n).length = min n p.length. Since s.l : p.length = n + m and n ≤ n + m, this equals n.
- Walk.drop_length: (p.drop n).length = p.length - n. Since p.length = n + m, this equals m.
- The intermediate vertex u = p.getVert n. For translating to origin, need to figure out u's coordinates and translate by -u.

Actually, this is getting complex. Let me use a different, simpler approach: just use Fintype.card_le_of_injective with an injection that maps s to (SAW from origin of length n, SAW from the intermediate vertex of length m) and then use saw_count_vertex_independent for the counting.

Actually, the simplest approach: build the injection into (SAW hexOrigin n) × Σ (u : HexVertex), SAW u m, and then bound the cardinality using saw_count_vertex_independent.

Or even better: use Fintype.card_le_of_injective to inject SAW hexOrigin (n+m) into SAW hexOrigin n × SAW hexOrigin m. For the second factor, translate the walk from u to the origin using hexTranslate (-u.1) (-u.2.1) (and hexFlip if u is on the wrong sublattice).
-/
/-- Split an (n+m)-step SAW into (n-step SAW, m-step SAW from endpoint). -/
def sawSplit (n m : ℕ) (s : SAW hexOrigin (n + m)) :
    (Σ (s₁ : SAW hexOrigin n), SAW s₁.w m) :=
  let p := s.p.1
  let u := p.getVert n
  let p1 := p.take n
  let p2 := p.drop n
  let hp1 : p1.IsPath := walk_take_isPath p s.p.2 n
  let hp2 : p2.IsPath := walk_drop_isPath p s.p.2 n
  have hlp : p.length = n + m := s.l
  let hl1 : p1.length = n := by rw [SimpleGraph.Walk.take_length]; omega
  let hl2 : p2.length = m := by rw [SimpleGraph.Walk.drop_length]; omega
  let first : SAW hexOrigin n := ⟨u, ⟨p1, hp1⟩, hl1⟩
  let second : SAW u m := ⟨s.w, ⟨p2, hp2⟩, hl2⟩
  ⟨first, second⟩

/-
PROBLEM
sawSplit is injective.

PROVIDED SOLUTION
If sawSplit n m s₁ = sawSplit n m s₂, then the first components (SAW hexOrigin n) and second components are equal (as dependent pairs in a sigma type).

First components equal: s₁.p.1.take n and s₂.p.1.take n give the same SAW from origin of length n. This means the walks agree on the first n+1 vertices.

Second components equal (after transport along the first component equality): the drop-n parts agree too.

Together: s₁.p.1 = s₁.p.1.take n ++ s₁.p.1.drop n and similarly for s₂. Since both halves agree, the full walks agree.

Key Mathlib lemma: SimpleGraph.Walk.take_append_drop_eq or similar, which says p = (p.take n).append (p.drop n).

Actually the simplest proof: unfold sawSplit and note that the sigma pair determines (first, second) which together determine the full walk p (since p.take n and p.drop n determine p by take_append_drop). Then p determines s.
-/
lemma sawSplit_injective (n m : ℕ) :
    Function.Injective (sawSplit n m) := by
      unfold sawSplit;
      intro s₁ s₂ h_eq
      obtain ⟨p1, p2⟩ := s₁
      obtain ⟨q1, q2⟩ := s₂
      simp at h_eq
      generalize_proofs at *;
      have h_path_eq : (p2.1 : hexGraph.Walk hexOrigin p1) = (p2.1.take n).append (p2.1.drop n) ∧ (q2.1 : hexGraph.Walk hexOrigin q1) = (q2.1.take n).append (q2.1.drop n) := by
        bound
      generalize_proofs at *; (
      grind +ring)

/-
PROBLEM
The number of m-step SAWs from any vertex equals saw_count m.

PROVIDED SOLUTION
Use Fintype.card_sigma to compute card(Σ s₁, SAW s₁.w m) = Σ_{s₁ : SAW hexOrigin n} card(SAW s₁.w m). By saw_count_vertex_independent, each card(SAW s₁.w m) = saw_count m. So the sum becomes Σ_{s₁} saw_count m = card(SAW hexOrigin n) * saw_count m = saw_count n * saw_count m.

Use Finset.sum_const to simplify. The key is Fintype.card_sigma and then rewriting each fiber cardinality using saw_count_vertex_independent.
-/
lemma saw_card_sigma (n m : ℕ) :
    Fintype.card (Σ (s₁ : SAW hexOrigin n), SAW s₁.w m) = saw_count n * saw_count m := by
      rw [ Fintype.card_sigma ];
      rw [ Finset.sum_congr rfl fun i hi => saw_count_vertex_independent _ _ ] ; norm_num [ mul_comm ];
      exact mul_comm _ _

/-
PROBLEM
The submultiplicativity of SAW counts: c_{n+m} ≤ c_n · c_m.

PROVIDED SOLUTION
Use Fintype.card_le_of_injective with sawSplit_injective to get saw_count (n+m) ≤ card(Σ s₁, SAW s₁.w m). Then use saw_card_sigma to rewrite the RHS as saw_count n * saw_count m.
-/
lemma saw_count_submult' : ∀ n m, saw_count (n + m) ≤ saw_count n * saw_count m := by
  intro n m
  calc saw_count (n + m)
      = Fintype.card (SAW hexOrigin (n + m)) := rfl
    _ ≤ Fintype.card (Σ (s₁ : SAW hexOrigin n), SAW s₁.w m) :=
        Fintype.card_le_of_injective _ (sawSplit_injective n m)
    _ = saw_count n * saw_count m := saw_card_sigma n m

end
