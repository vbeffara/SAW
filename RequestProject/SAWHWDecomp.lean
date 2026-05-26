/-
# Walk Decomposition for Hammersley-Welsh

Infrastructure for decomposing SAWs at the minimum dc vertex,
used to prove `saw_neg_le_hp_conv`.

The key decomposition: every SAW from paperStart visiting dc < 0 can be
split at the first minimum dc vertex into a prefix and suffix. After
reverse+translate+flip (prefix) and translate+flip (suffix), both become
SAWs from paperStart in strip [-N, 0].
-/

import Mathlib
import RequestProject.SAWDiagProof
import RequestProject.SAWSubmult
import RequestProject.SAWHWStructural
import RequestProject.SAWHWMinDC
import RequestProject.SAWHWHalfPlane

open Real Complex ComplexConjugate Filter Topology

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Key equalities for translate+flip at minimum dc vertex -/

/-- For a FALSE vertex v, hexFlip (hexTranslate (-v.1) (-v.2.1) v) = paperStart. -/
lemma flip_translate_false_eq_paperStart (v : HexVertex) (hv : v.2.2 = false) :
    hexFlip (hexTranslate (-v.1) (-v.2.1) v) = paperStart := by
  rcases v with ⟨a, b, c⟩; simp at hv; subst hv
  simp [hexTranslate, hexFlip, paperStart]

/-- DC value after translate(-a,-b) then flip: becomes -(dc_orig - (a+b)). -/
lemma dc_after_flip_translate (a b : ℤ) (v : HexVertex) :
    (hexFlip (hexTranslate (-a) (-b) v)).1 + (hexFlip (hexTranslate (-a) (-b) v)).2.1 =
    -(v.1 + v.2.1 - (a + b)) := by
  simp [hexTranslate, hexFlip]; ring

/-! ## Walk.copy preserves IsPath -/

private lemma walk_copy_isPath' {G : SimpleGraph V} {u v u' v' : V}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (hp : p.IsPath) :
    (p.copy hu hv).IsPath := by
  subst hu; subst hv; rwa [SimpleGraph.Walk.copy_rfl_rfl]

/-! ## Prefix transform: take, reverse, translate, flip -/

/-- The prefix transform for the neg_dc decomposition.
    Given a walk p from paperStart, splits at index i (where v_i is FALSE at minimum dc),
    reverses the prefix, translates to put v_i at origin, and flips.
    Result: walk from paperStart. -/
def prefixTransform {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    hexGraph.Walk paperStart
      (hexFlip (hexTranslate (-(p.getVert i).1) (-(p.getVert i).2.1) paperStart)) :=
  let pref := p.take i
  let rev := pref.reverse
  let translated := hexTranslate_walk (-(p.getVert i).1) (-(p.getVert i).2.1) rev
  let flipped := hexFlip_walk translated
  flipped.copy (flip_translate_false_eq_paperStart _ hfalse) rfl

/-- The suffix transform: translate the suffix to put v_i at origin, then flip.
    Result: walk from paperStart. -/
def suffixTransform {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    hexGraph.Walk paperStart
      (hexFlip (hexTranslate (-(p.getVert i).1) (-(p.getVert i).2.1) w)) :=
  let suff := p.drop i
  let translated := hexTranslate_walk (-(p.getVert i).1) (-(p.getVert i).2.1) suff
  let flipped := hexFlip_walk translated
  flipped.copy (flip_translate_false_eq_paperStart _ hfalse) rfl

/-! ## Length preservation -/

lemma prefixTransform_length {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    (prefixTransform p i hi hfalse).length = i := by
  simp [prefixTransform, SimpleGraph.Walk.length_reverse,
        hexTranslate_walk_length, hexFlip_walk_length,
        SimpleGraph.Walk.take_length, min_eq_left hi]

lemma suffixTransform_length {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    (suffixTransform p i hi hfalse).length = p.length - i := by
  simp [suffixTransform, hexTranslate_walk_length, hexFlip_walk_length,
        SimpleGraph.Walk.drop_length]

/-! ## IsPath preservation -/

lemma prefixTransform_isPath {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (hp : p.IsPath) (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    (prefixTransform p i hi hfalse).IsPath := by
  unfold prefixTransform
  apply walk_copy_isPath'
  exact hexFlip_walk_isPath _ (hexTranslate_walk_isPath _ _ _
    ((walk_take_isPath p hp i).reverse))

lemma suffixTransform_isPath {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (hp : p.IsPath) (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    (suffixTransform p i hi hfalse).IsPath := by
  unfold suffixTransform
  apply walk_copy_isPath'
  exact hexFlip_walk_isPath _ (hexTranslate_walk_isPath _ _ _
    (walk_drop_isPath p hp i))

/-! ## Strip constraints -/

/-- Prefix transform stays in strip [-N, 0]. -/
lemma prefixTransform_strip {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (hp : p.IsPath) (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false)
    (hmin : ∀ j, j ≤ p.length →
      (p.getVert i).1 + (p.getVert i).2.1 ≤ (p.getVert j).1 + (p.getVert j).2.1)
    (N : ℕ) (hN : i ≤ N) :
    ∀ v ∈ (prefixTransform p i hi hfalse).support,
      -(N : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 := by
  intro v hv
  have h_support : v ∈ (hexFlip_walk (hexTranslate_walk (-(p.getVert i).1) (-(p.getVert i).2.1) (p.take i).reverse)).support := by
    unfold prefixTransform at hv; aesop;
  rw [ hexFlip_walk_support, hexTranslate_walk_support ] at h_support;
  simp +zetaDelta at *;
  rcases h_support with ⟨ a, b, h | h ⟩ <;> simp_all +decide [ hexFlip, hexTranslate ];
  · have h_support : ∃ j ≤ i, (p.getVert j).1 + (p.getVert j).2.1 = a + b := by
      have h_support : ∀ {u v : HexVertex} {p : hexGraph.Walk u v}, (a, b, false) ∈ p.support → ∃ j ≤ p.length, (p.getVert j).1 + (p.getVert j).2.1 = a + b := by
        intros u v p hp; induction' p with u v p ih <;> simp_all +decide [ SimpleGraph.Walk.support ] ;
        · grind;
        · rcases hp with ( rfl | hp ) <;> [ exact ⟨ 0, by norm_num ⟩ ; exact Exists.elim ( ‹ ( a, b, false ) ∈ _ → ∃ j ≤ _, _› hp ) fun j hj => ⟨ j + 1, by linarith, by aesop ⟩ ];
      obtain ⟨ j, hj₁, hj₂ ⟩ := h_support h.1;
      use j;
      simp_all +decide [ SimpleGraph.Walk.take ];
    obtain ⟨ j, hj₁, hj₂ ⟩ := h_support;
    have := walk_getVert_dc_diff' p j i hj₁ ( by linarith ) ; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
    constructor <;> push_cast [ ← h.2 ] <;> linarith [ hmin j ( by linarith ), hmin i ( by linarith ) ];
  · have h_support : ∃ j ≤ i, (p.getVert j).1 + (p.getVert j).2.1 = a + b := by
      have h_support : ∀ {u : HexVertex} {w : HexVertex} {p : hexGraph.Walk u w}, ∀ v ∈ p.support, ∃ j ≤ p.length, (p.getVert j) = v := by
        intros u w p v hv; induction p <;> simp_all +decide [ SimpleGraph.Walk.cons ] ;
        rcases hv with ( rfl | hv ) <;> [ exact ⟨ 0, by norm_num ⟩ ; exact Exists.elim ( ‹v ∈ _ → ∃ j ≤ _, _› hv ) fun j hj => ⟨ j + 1, by linarith, by aesop ⟩ ];
      obtain ⟨ j, hj₁, hj₂ ⟩ := h_support _ h.1; use j; aesop;
    obtain ⟨ j, hj₁, hj₂ ⟩ := h_support;
    have := walk_getVert_dc_diff' p j i hj₁ ( by linarith ) ; simp_all +decide [ add_comm ] ;
    grind

/-- Suffix transform stays in strip [-N, 0]. -/
lemma suffixTransform_strip {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (hp : p.IsPath) (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false)
    (hmin : ∀ j, j ≤ p.length →
      (p.getVert i).1 + (p.getVert i).2.1 ≤ (p.getVert j).1 + (p.getVert j).2.1)
    (N : ℕ) (hN : p.length - i ≤ N) :
    ∀ v ∈ (suffixTransform p i hi hfalse).support,
      -(N : ℤ) ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ 0 := by
  intro v hv
  have h_v_infstrip_bounds : ∀ u ∈ (p.drop i).support, -N ≤ ( -(u.1 - (p.getVert i).1) ) + ( -(u.2.1 - (p.getVert i).2.1) ) ∧ ( -(u.1 - (p.getVert i).1) ) + ( -(u.2.1 - (p.getVert i).2.1) ) ≤ 0 := by
    intro u hu
    obtain ⟨j, hj⟩ : ∃ j, i ≤ j ∧ j ≤ p.length ∧ u = p.getVert j := by
      simp_all +decide [ SimpleGraph.Walk.mem_support_iff_exists_getVert ];
      grind;
    have := walk_getVert_dc_diff p i j hj.1 hj.2.1; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
    constructor <;> linarith [ hmin j hj.2.1 ];
  obtain ⟨u, hu⟩ : ∃ u ∈ (p.drop i).support, v = hexFlip (hexTranslate (-(p.getVert i).1) (-(p.getVert i).2.1) u) := by
    unfold suffixTransform at hv; simp_all +decide [ hexTranslate_walk_support, hexFlip_walk_support ] ;
    grind +splitImp;
  convert h_v_infstrip_bounds u hu.1 using 1 <;> simp +decide [ hu.2, hexFlip, hexTranslate ] ; ring;
  grind

/-! ## Support-level injectivity -/

/-- Support of prefix transform is the reverse of the support of take i,
    mapped by hexFlip ∘ hexTranslate. -/
lemma prefixTransform_support {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    (prefixTransform p i hi hfalse).support =
    ((p.take i).support.reverse.map
      (fun v => hexFlip (hexTranslate (-(p.getVert i).1) (-(p.getVert i).2.1) v))) := by
  simp [prefixTransform, hexFlip_walk_support, hexTranslate_walk_support,
        SimpleGraph.Walk.support_reverse, List.map_reverse]

/-- Support of suffix transform is the support of drop i,
    mapped by hexFlip ∘ hexTranslate. -/
lemma suffixTransform_support {w : HexVertex} (p : hexGraph.Walk paperStart w)
    (i : ℕ) (hi : i ≤ p.length)
    (hfalse : (p.getVert i).2.2 = false) :
    (suffixTransform p i hi hfalse).support =
    ((p.drop i).support.map
      (fun v => hexFlip (hexTranslate (-(p.getVert i).1) (-(p.getVert i).2.1) v))) := by
  simp [suffixTransform, hexFlip_walk_support, hexTranslate_walk_support]

/-- The transform hexFlip ∘ hexTranslate(-a,-b) is injective. -/
lemma flipTranslate_injective (a b : ℤ) :
    Function.Injective (fun v : HexVertex => hexFlip (hexTranslate (-a) (-b) v)) := by
  intro v₁ v₂ h
  have := hexFlip_injective h
  exact hexTranslate_injective (-a) (-b) this

/-
If the prefix and suffix transforms have the same supports, and the
    split indices are the same, then the original walks have the same support.
-/
lemma decomp_support_injective {w₁ w₂ : HexVertex}
    (p₁ : hexGraph.Walk paperStart w₁) (p₂ : hexGraph.Walk paperStart w₂)
    (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hl : p₁.length = p₂.length)
    (i : ℕ) (hi₁ : i ≤ p₁.length) (hi₂ : i ≤ p₂.length)
    (hf₁ : (p₁.getVert i).2.2 = false) (hf₂ : (p₂.getVert i).2.2 = false)
    (hvi : p₁.getVert i = p₂.getVert i)
    (h_prefix_support :
      (prefixTransform p₁ i hi₁ hf₁).support =
      (prefixTransform p₂ i hi₂ hf₂).support)
    (h_suffix_support :
      (suffixTransform p₁ i hi₁ hf₁).support =
      (suffixTransform p₂ i hi₂ hf₂).support) :
    p₁.support = p₂.support := by
  -- Using the fact that the support of a walk is the union of the supports of its prefix and suffix, we can conclude that the supports of p₁ and p₂ are equal.
  have h_support_union : (p₁.take i).support ++ (p₁.drop i).support.tail = p₁.support ∧ (p₂.take i).support ++ (p₂.drop i).support.tail = p₂.support := by
    constructor <;> rw [ ← SimpleGraph.Walk.support_append ] <;> aesop;
  have h_support_prefix : (p₁.take i).support.reverse = (p₂.take i).support.reverse := by
    have h_support_eq : (p₁.take i).support.reverse.map (fun v => hexFlip (hexTranslate (-(p₁.getVert i).1) (-(p₁.getVert i).2.1) v)) = (p₂.take i).support.reverse.map (fun v => hexFlip (hexTranslate (-(p₂.getVert i).1) (-(p₂.getVert i).2.1) v)) := by
      rw [prefixTransform_support, prefixTransform_support] at h_prefix_support ; aesop;
    exact List.map_injective_iff.mpr ( flipTranslate_injective _ _ ) <| by aesop;
  have h_support_suffix : (p₁.drop i).support = (p₂.drop i).support := by
    have h_support_suffix : (p₁.drop i).support.map (fun v => hexFlip (hexTranslate (-(p₁.getVert i).1) (-(p₁.getVert i).2.1) v)) = (p₂.drop i).support.map (fun v => hexFlip (hexTranslate (-(p₂.getVert i).1) (-(p₂.getVert i).2.1) v)) := by
      convert h_suffix_support using 1 <;> simp +decide [ suffixTransform_support, hvi ];
    exact List.map_injective_iff.mpr ( flipTranslate_injective _ _ ) <| by aesop;
  aesop

end