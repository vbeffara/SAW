/-
# Winding Decomposition for Pair Walks

Decomposes the winding of a pair walk into prefix + junction + suffix components.
This is the key infrastructure for proving `pair_winding_relation`.

## Main results

* `hexWalkWinding_append_overlap` — winding additivity when splitting at a 2-vertex overlap
* `hexWalkWinding_cons3` — winding of [a, b, c, ...] = turn at b + winding of [b, c, ...]
-/

import Mathlib
import RequestProject.SAWPairCancellation

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 6400000

/-! ## Winding additivity -/

/-- hexWalkWinding of (a :: b :: c :: rest) decomposes as turn at b + winding of remainder -/
lemma hexWalkWinding_cons3 (a b c : HexVertex) (rest : List HexVertex) :
    hexWalkWinding (a :: b :: c :: rest) =
    Complex.arg ((correctHexEmbed c - correctHexEmbed b) /
                 (correctHexEmbed b - correctHexEmbed a)) +
    hexWalkWinding (b :: c :: rest) := by
  simp [hexWalkWinding]

/-
Winding additivity: splitting a list at a 2-vertex overlap.
    hexWalkWinding (L₁ ++ L₂.drop 2) = hexWalkWinding L₁ + hexWalkWinding L₂
    when L₁ ends with [a, b] and L₂ starts with [a, b, ...]
-/
lemma hexWalkWinding_split (L₁ : List HexVertex) (a b : HexVertex) (L₂ : List HexVertex)
    (hL₁ : L₁ = L₁.dropLast ++ [a, b])
    (h_len : 2 ≤ L₁.length) :
    hexWalkWinding (L₁ ++ L₂) =
    hexWalkWinding L₁ + hexWalkWinding (a :: b :: L₂) := by
  grind

/-! ## Pair winding decomposition

For a FreshIncomingPair walk γ at (v, k):
- Full support: prefix.support ++ [exit_nbr, w₁, ..., wₘ, k_nbr, v]
- = prefix.support ++ suffix_tail

Where:
- prefix.support = [paperStart, ..., v]
- suffix = [v, exit_nbr, w₁, ..., wₘ, k_nbr, v]
- suffix_tail = suffix.tail = [exit_nbr, w₁, ..., wₘ, k_nbr, v]

The winding decomposes as:
W_orig = hexWalkWinding(prefix.support) + hexWalkWinding(pₙ :: suffix)

where pₙ is the vertex before v in the prefix.
-/

/-
The inner loop of a pair walk forms a hex trail list.
-/
lemma pair_inner_loop_trail {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    HexTrailList ((pairPrefix hv_ne γ).support ++
      [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
      (pairInner hv_ne γ).support.tail ++ [v]) := by
  have h_hex_trail : HexTrailList (γ.1.walk.support ++ [v]) := by
    convert walk_support_is_hex_trail_list' ( γ.1.walk.append ( SimpleGraph.Walk.cons γ.1.adj SimpleGraph.Walk.nil ) ) _ using 1;
    · simp +decide [ SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons ];
    · have := γ.1.is_trail; simp_all +decide [ SimpleGraph.Walk.isTrail_def ] ;
      have := γ.1.fresh; simp_all +decide [ List.nodup_append ] ;
      exact fun x hx => by rintro rfl; exact this hx;
  have h_walk_support : γ.1.walk.support = (pairPrefix hv_ne γ).support ++ [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++ (pairInner hv_ne γ).support.tail := by
    rw [ pairDecomp ];
    all_goals norm_num [ SimpleGraph.Walk.support_append ];
    all_goals norm_cast;
    exact?;
  aesop

/-
The reversed inner loop also forms a hex trail list.
-/
lemma pair_inner_loop_trail_rev {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv : PaperFinStrip T L v)
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    HexTrailList ((pairPrefix hv_ne γ).support ++
      [hexNeighbors3 v k] ++
      (pairInner hv_ne γ).reverse.support.tail ++ [v]) := by
  have h_trail : (pairInvol hv hv_ne γ).1.walk.IsTrail := by
    exact pairInvol hv hv_ne γ |>.1 |>.2;
  have h_support : (pairInvol hv hv_ne γ).1.walk.support ++ [v] = (pairPrefix hv_ne γ).support ++ [hexNeighbors3 v k] ++ (pairInner hv_ne γ).reverse.support.tail ++ [v] := by
    convert congr_arg ( fun x : List HexVertex => x ++ [ v ] ) ( show ( pairInvol hv hv_ne γ ).1.walk.support = ( pairPrefix hv_ne γ ).support ++ [ hexNeighbors3 v k ] ++ ( pairInner hv_ne γ ).reverse.support.tail from ?_ ) using 1;
    unfold pairInvol;
    unfold pairInvolWalk; simp +decide [ mkPairedWalk ] ;
    simp +decide [ SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons ];
    rw [ List.dropLast_append_getLast? ];
    cases h : ( pairInner hv_ne γ ).support <;> simp_all +decide [ SimpleGraph.Walk.support ];
    rw [ ← h ];
    rw [ List.getLast?_eq_some_getLast ];
    all_goals norm_num [ ← h ];
  convert walk_support_is_hex_trail_list' _ _ using 1;
  convert h_support.symm using 1;
  rotate_left;
  exact paperStart;
  exact v;
  exact ( pairInvol hv hv_ne γ ).1.walk.append ( SimpleGraph.Walk.cons ( hexNeighbors3_adj v ( pairExitIdx hv_ne γ ) |> SimpleGraph.Adj.symm ) SimpleGraph.Walk.nil );
  · simp_all +decide [ SimpleGraph.Walk.isTrail_def ];
    grind +suggestions;
  · simp +decide [ SimpleGraph.Walk.support_append ]

/-
The closed suffix [v, exit_nbr, ..., k_nbr, v] forms a hex trail list.
-/
lemma pair_suffix_hex_trail {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    HexTrailList ([v] ++ [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
      (pairInner hv_ne γ).support.tail ++ [v]) := by
  have := pairDecomp hv_ne γ;
  have := walk_support_is_hex_trail_list' γ.1.walk γ.1.is_trail; simp_all +decide [ SimpleGraph.Walk.support_append ] ;
  have h_tail : (pairPrefix hv_ne γ).support.getLast? = some v := by
    have h_last : ∀ {u v : HexVertex} (walk : hexGraph.Walk u v), walk.support.getLast? = some v := by
      intros u v walk; induction walk <;> simp +decide [ * ] ;
      grind;
    exact h_last _
  generalize_proofs at *;
  rcases n : ( pairPrefix hv_ne γ ).support with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ List.getLast? ];
  · cases h : ( pairPrefix hv_ne γ ) <;> simp_all +decide [ SimpleGraph.Walk.support ];
    grobner;
  · have h_tail : HexTrailList (v :: hexNeighbors3 v (pairExitIdx hv_ne γ) :: (pairInner hv_ne γ).support.tail ++ [v]) := by
      have := pair_inner_loop_trail hv_ne γ
      cases l <;> simp_all +decide [ List.getLast ];
      · cases ‹HexTrailList ( a :: v :: hexNeighbors3 v ( pairExitIdx hv_ne γ ) :: ( ( pairInner hv_ne γ ).support.tail ++ [ v ] ) ) › ; aesop ( simp_config := { singlePass := true } ) ;
      · rename_i k hk₁ hk₂ hk₃;
        have h_tail : ∀ {L₁ L₂ : List HexVertex}, HexTrailList (L₁ ++ L₂) → L₁ ≠ [] → HexTrailList (L₁.getLast! :: L₂) := by
          intros L₁ L₂ hL₁L₂ hL₁_nonempty
          induction' L₁ with a L₁ ih generalizing L₂ <;> simp_all +decide [ List.getLast! ];
          cases L₁ <;> simp_all +decide [ List.getLast ];
          cases ‹List HexVertex› <;> simp_all +decide [ HexTrailList ];
          cases L₂ <;> simp_all +decide [ HexTrailList ]
        generalize_proofs at *; (
        specialize @h_tail ( a :: b :: hk₁ :: hk₂ ) ( hexNeighbors3 v ( pairExitIdx hv_ne γ ) :: ( ( pairInner hv_ne γ ).support.tail ++ [ v ] ) ) ; simp_all +decide [ List.getLast! ] ;)
    generalize_proofs at *; exact h_tail;

/-
The reversed suffix [v, k_nbr, ..., exit_nbr, v] forms a hex trail list.
-/
lemma pair_suffix_hex_trail_rev {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    HexTrailList ([v] ++ [hexNeighbors3 v k] ++
      (pairInner hv_ne γ).reverse.support.tail ++ [v]) := by
  have h_reverse : ∀ (L : List HexVertex), HexTrailList L → HexTrailList L.reverse := by
    intro L hL
    induction' n : L.length with n ih generalizing L;
    · cases L <;> trivial;
    · rcases L with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, L ⟩ ⟩ ⟩ ) <;> simp_all +decide [ HexTrailList ];
      have h_rev_trail : HexTrailList (L.reverse ++ [c, b]) → HexTrailList (L.reverse ++ [c, b, a]) := by
        induction' L.reverse with d L ih <;> simp_all +decide [ HexTrailList ];
        · exact ⟨ hL.2.1.symm, hL.1.symm, by aesop ⟩;
        · cases L <;> simp_all +decide [ HexTrailList ];
          cases ‹List HexVertex› <;> simp_all +decide [ HexTrailList ];
          aesop;
      grind;
  convert h_reverse _ ( pair_suffix_hex_trail hv_ne γ ) using 1;
  simp +zetaDelta at *;
  have h_support : (pairInner hv_ne γ).support = hexNeighbors3 v (pairExitIdx hv_ne γ) :: (pairInner hv_ne γ).support.tail := by
    rcases h : ( pairInner hv_ne γ ).support with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide;
    · have h_support : (pairInner hv_ne γ).support.head? = some (hexNeighbors3 v (pairExitIdx hv_ne γ)) := by
        have h_support : ∀ (u v : HexVertex) (w : hexGraph.Walk u v), w.support.head? = some u := by
          intros u v w; induction w <;> simp +decide [ * ] ;
        exact h_support _ _ _;
      grind;
    · grind +suggestions;
  have h_support : (pairInner hv_ne γ).support.getLast? = some (hexNeighbors3 v k) := by
    have h_support : ∀ (u v : HexVertex) (p : hexGraph.Walk u v), p.support.getLast? = some v := by
      intros u v p; induction p <;> simp +decide [ *, List.getLast? ] ;
    exact h_support _ _ _;
  rw [ List.getLast?_eq_some_iff ] at h_support;
  grind

/-
The suffix length is at least 3 (for the reversal to work).
-/
lemma pair_suffix_length {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    3 ≤ ([v] ++ [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
      (pairInner hv_ne γ).support.tail ++ [v]).length := by
  simp +arith +decide [ List.length_append ]

/-
The reversed suffix is the reverse of the original suffix.
-/
lemma pair_suffix_reverse {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    ([v] ++ [hexNeighbors3 v k] ++
      (pairInner hv_ne γ).reverse.support.tail ++ [v]).reverse =
    [v] ++ [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
      (pairInner hv_ne γ).support.tail ++ [v] := by
  cases h : ( pairInner hv_ne γ ).support <;> simp_all +decide [ List.reverse_append ];
  have h_tail : (pairInner hv_ne γ).support.head! = hexNeighbors3 v (pairExitIdx hv_ne γ) := by
    have := pairSuffix_spec hv_ne γ; simp_all +decide [ List.head! ] ;
    grind +suggestions;
  have h_tail : (pairInner hv_ne γ).support.getLast! = hexNeighbors3 v k := by
    have h_tail : ∀ {u w : HexVertex} {p : hexGraph.Walk u w}, p.support.getLast! = w := by
      intros u w p; induction p <;> simp +decide [ *, List.getLast! ] ;
    exact h_tail;
  cases ‹List HexVertex› <;> simp_all +decide [ List.getLast! ];
  induction ‹List HexVertex› using List.reverseRecOn <;> aesop

/-
The winding of the reversed suffix is the negation.
-/
lemma pair_suffix_winding_neg {T L : ℕ} {v : HexVertex} {k : Fin 3}
    (hv_ne : v ≠ paperStart)
    (γ : FreshIncomingPair T L v k) :
    hexWalkWinding ([v] ++ [hexNeighbors3 v k] ++
      (pairInner hv_ne γ).reverse.support.tail ++ [v]) =
    -hexWalkWinding ([v] ++ [hexNeighbors3 v (pairExitIdx hv_ne γ)] ++
      (pairInner hv_ne γ).support.tail ++ [v]) := by
  rw [ ← pair_suffix_reverse, hexWalkWinding_reverse_list' ];
  · ring;
  · exact?;
  · simp +arith +decide [ List.length_append ]

end