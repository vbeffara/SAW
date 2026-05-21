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


lemma hexTranslate_adj (dx dy : ℤ) (v w : HexVertex) :
    hexGraph.Adj v w ↔ hexGraph.Adj (hexTranslate dx dy v) (hexTranslate dx dy w) := by
      unfold hexGraph hexTranslate; simp
      grind +ring


lemma hexTranslate_injective (dx dy : ℤ) : Function.Injective (hexTranslate dx dy) := by
  intro v w h;
  unfold hexTranslate at *; aesop;


lemma hexTranslate_inv (dx dy : ℤ) (v : HexVertex) :
    hexTranslate (-dx) (-dy) (hexTranslate dx dy v) = v := by
      unfold hexTranslate; aesop;

/-- The sublattice flip: (x, y, b) ↦ (-x, -y, !b).
    This is a graph automorphism that exchanges the two sublattices. -/
def hexFlip (v : HexVertex) : HexVertex := (-v.1, -v.2.1, !v.2.2)


lemma hexFlip_adj (v w : HexVertex) :
    hexGraph.Adj v w ↔ hexGraph.Adj (hexFlip v) (hexFlip w) := by
      unfold hexGraph hexFlip;
      grind +ring


lemma hexFlip_involutive : Function.Involutive hexFlip := by
  exact fun v => by cases v; simp +decide [ hexFlip ] ;

/-- The flip is injective. -/
lemma hexFlip_injective : Function.Injective hexFlip :=
  hexFlip_involutive.injective


lemma hexFlip_origin : hexFlip hexOrigin = (0, 0, true) := by
  rfl

/-! ## Walk and path mapping under automorphisms -/

/-- Map a walk under translation. -/
def hexTranslate_walk (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    hexGraph.Walk (hexTranslate dx dy v) (hexTranslate dx dy w) := by
  induction p with
  | nil => exact .nil
  | cons hadj _ ih => exact .cons ((hexTranslate_adj dx dy _ _).mp hadj) ih


lemma hexTranslate_walk_length (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexTranslate_walk dx dy p).length = p.length := by
      -- We can prove this by induction on the walk p.
      induction' p with v w p ih;
      · rfl;
      · unfold hexTranslate_walk; aesop;


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


lemma hexFlip_walk_length {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexFlip_walk p).length = p.length := by
      -- We can prove this by induction on the length of the walk.
      induction' p with v w p ih;
      · rfl;
      · simp_all +decide [ hexFlip_walk ]


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


lemma hexTranslate_walk_support (dx dy : ℤ) {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexTranslate_walk dx dy p).support = p.support.map (hexTranslate dx dy) := by
      induction p <;> simp_all +decide [ hexTranslate_walk ]


lemma hexTranslate_walk_injective (dx dy : ℤ) {v w : HexVertex}
    (p q : hexGraph.Walk v w)
    (h : hexTranslate_walk dx dy p = hexTranslate_walk dx dy q) : p = q := by
      -- Since hexTranslate is injective, if the translated walks are equal, then their supports must be equal.
      have h_support : p.support = q.support := by
        have h_support : p.support.map (hexTranslate dx dy) = q.support.map (hexTranslate dx dy) := by
          rw [ ← hexTranslate_walk_support, ← hexTranslate_walk_support, h ];
        exact List.map_injective_iff.mpr ( hexTranslate_injective dx dy ) h_support;
      exact SimpleGraph.Walk.ext_support h_support


lemma hexFlip_walk_support {v w : HexVertex} (p : hexGraph.Walk v w) :
    (hexFlip_walk p).support = p.support.map hexFlip := by
      induction p <;> simp_all +decide [ hexFlip_walk ]


lemma hexFlip_walk_injective {v w : HexVertex}
    (p q : hexGraph.Walk v w)
    (h : hexFlip_walk p = hexFlip_walk q) : p = q := by
      apply_fun (fun x => x.support) at h;
      rw [ hexFlip_walk_support, hexFlip_walk_support ] at h;
      have h_support : p.support = q.support := by
        exact List.map_injective_iff.mpr ( hexFlip_injective ) h;
      exact SimpleGraph.Walk.ext_support h_support


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


lemma saw_count_flip (n : ℕ) :
    Fintype.card (SAW (0, 0, true) n) = saw_count n := by
      apply le_antisymm;
      · convert Fintype.card_le_of_injective _ ( saw_flip_injective ) using 1;
      · -- By Lemma~\ref{lem:saw_flip_injective}, we can use `saw_flip` as the worlds `SAW hexOrigin n → SAW (0,0,true n)` for Fintype.card_le_of_injective.
        apply Fintype.card_le_of_injective saw_flip saw_flip_injective


lemma saw_count_vertex_independent (v : HexVertex) (n : ℕ) :
    Fintype.card (SAW v n) = saw_count n := by
      -- Decouple theroles of length and adjacency in the walk.
      cases' v with x y b; (
      cases' y with y b; cases' b with b; (
      convert saw_count_same_sublattice x y false n using 1);
      rw [ ← saw_count_flip, saw_count_same_sublattice ]);

/-! ## Walk splitting -/


lemma walk_take_isPath {v w : V} [DecidableEq V] {G : SimpleGraph V}
    (p : G.Walk v w) (hp : p.IsPath) (n : ℕ) :
    (p.take n).IsPath := by
      cases' hp with hp₁ hp₂;
      have h_support : ∀ {p : G.Walk v w}, p.support.Nodup → ∀ n, List.Nodup (List.take (n + 1) p.support) := by
        exact fun { p } hp n => hp.sublist ( List.take_sublist _ _ );
      have := @h_support p hp₂ n; simp_all +decide [ SimpleGraph.Walk.isPath_def ] ;
      convert h_support hp₂ n using 1;
      exact SimpleGraph.Walk.take_support_eq_support_take_succ p n


lemma walk_drop_isPath {v w : V} [DecidableEq V] {G : SimpleGraph V}
    (p : G.Walk v w) (hp : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath := by
      induction' p with _ _ _ _ ih generalizing n;
      · cases n <;> aesop;
      · cases n <;> simp_all +decide [ SimpleGraph.Walk.drop, SimpleGraph.Walk.cons_isPath_iff ]

/-! ## The submultiplicativity injection -/


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


lemma saw_card_sigma (n m : ℕ) :
    Fintype.card (Σ (s₁ : SAW hexOrigin n), SAW s₁.w m) = saw_count n * saw_count m := by
      rw [ Fintype.card_sigma ];
      rw [ Finset.sum_congr rfl fun i hi => saw_count_vertex_independent _ _ ] ; norm_num [ mul_comm ];
      exact mul_comm _ _


lemma saw_count_submult' : ∀ n m, saw_count (n + m) ≤ saw_count n * saw_count m := by
  intro n m
  calc saw_count (n + m)
      = Fintype.card (SAW hexOrigin (n + m)) := rfl
    _ ≤ Fintype.card (Σ (s₁ : SAW hexOrigin n), SAW s₁.w m) :=
        Fintype.card_le_of_injective _ (sawSplit_injective n m)
    _ = saw_count n * saw_count m := saw_card_sigma n m

end
