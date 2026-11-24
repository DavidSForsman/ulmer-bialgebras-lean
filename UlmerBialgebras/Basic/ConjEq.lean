module

public import Foundations.CategoryTheory.Bicategory.StrictCoherence
public import Mathlib.CategoryTheory.EqToHom

/-!
# Morphisms equal up to `eqToHom`

`UlmerBialgebras.ConjEq u v` says that `u : X ⟶ Y` and `v : X' ⟶ Y'` agree after composing with
`eqToHom`s on both sides. Its calculus keeps proofs about 2-cells between 1-cells that are equal
but not syntactically equal (such as interpretations of terms) free of dependent rewriting.

## Main results

* `UlmerBialgebras.ConjEq`: the relation, with `ConjEq.trans`, `ConjEq.comp`, `ConjEq.eq`.
* `UlmerBialgebras.ConjEq.whiskerLeft`, `UlmerBialgebras.ConjEq.whiskerRight`: whiskering
  preserves it.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], §2–3
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory
open scoped CategoryTheory.Bicategory

section ConjEqCalculus

variable {C : Type*} [Category C]

/-- `u` and `v` agree up to composing with `eqToHom`s on both sides. -/
def ConjEq {X Y X' Y' : C} (u : X ⟶ Y) (v : X' ⟶ Y') : Prop :=
  ∃ (p : X = X') (q : Y' = Y), u = eqToHom p ≫ v ≫ eqToHom q

namespace ConjEq

variable {X Y Z X' Y' Z' X'' Y'' W : C}

/-- Introduce `ConjEq u v` from an equation `u = eqToHom p ≫ v ≫ eqToHom q`. -/
lemma intro {u : X ⟶ Y} {v : X' ⟶ Y'} {p : X = X'} {q : Y' = Y}
    (h : u = eqToHom p ≫ v ≫ eqToHom q) : ConjEq u v :=
  ⟨p, q, h⟩

/-- Two `eqToHom`s between equal pairs of objects are `ConjEq`. -/
lemma eqToHom_eqToHom (p : X = Y) (q : X' = Y') (hX : X = X') :
    ConjEq (eqToHom p) (eqToHom q) := by
  subst hX q p
  exact ⟨rfl, rfl, by simp⟩

/-- Identities on equal objects are `ConjEq`. -/
lemma id_id (e : X = X') : ConjEq (𝟙 X) (𝟙 X') := by
  subst e
  exact ⟨rfl, rfl, by simp⟩

/-- Equal morphisms are `ConjEq`. -/
lemma of_eq {u v : X ⟶ Y} (h : u = v) : ConjEq u v :=
  ⟨rfl, rfl, by simp [h]⟩

/-- `eqToHom p ≫ v ≫ eqToHom q` is `ConjEq` to `v`. -/
lemma conj (p : X = X') (q : Y' = Y) (v : X' ⟶ Y') : ConjEq (eqToHom p ≫ v ≫ eqToHom q) v :=
  ⟨p, q, rfl⟩

/-- `ConjEq` is symmetric. -/
lemma symm {u : X ⟶ Y} {v : X' ⟶ Y'} (h : ConjEq u v) : ConjEq v u := by
  obtain ⟨p, q, rfl⟩ := h
  exact ⟨p.symm, q.symm, by simp⟩

/-- `ConjEq` is transitive. -/
lemma trans {u : X ⟶ Y} {v : X' ⟶ Y'} {w : X'' ⟶ Y''} (h₁ : ConjEq u v) (h₂ : ConjEq v w) :
    ConjEq u w := by
  obtain ⟨p, q, rfl⟩ := h₁
  obtain ⟨p', q', rfl⟩ := h₂
  exact ⟨p.trans p', q'.trans q, by simp⟩

/-- `ConjEq` is compatible with composition: `u ~ u'` and `v ~ v'` give `u ≫ v ~ u' ≫ v'`. -/
lemma comp {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X' ⟶ Y'} {v' : Y' ⟶ Z'} (hu : ConjEq u u')
    (hv : ConjEq v v') : ConjEq (u ≫ v) (u' ≫ v') := by
  obtain ⟨p, q, rfl⟩ := hu
  obtain ⟨p', q', rfl⟩ := hv
  exact ⟨p, q', by simp⟩

/-- Precomposing with an `eqToHom` preserves `ConjEq`: `u ~ u'` gives `eqToHom r ≫ u ~ u'`. -/
lemma eqToHom_comp {u : X ⟶ Y} {u' : X' ⟶ Y'} (hu : ConjEq u u') (r : W = X) :
    ConjEq (eqToHom r ≫ u) u' := by
  obtain ⟨p, q, rfl⟩ := hu
  exact ⟨r.trans p, q, by simp⟩

/-- Postcomposing with an `eqToHom` preserves `ConjEq`: `u ~ u'` gives `u ≫ eqToHom r ~ u'`. -/
lemma comp_eqToHom {u : X ⟶ Y} {u' : X' ⟶ Y'} (hu : ConjEq u u') (r : Y = W) :
    ConjEq (u ≫ eqToHom r) u' := by
  obtain ⟨p, q, rfl⟩ := hu
  exact ⟨p, q.trans r, by simp⟩

/-- `ConjEq` between morphisms with the same source and target is equality. -/
lemma eq {u v : X ⟶ Y} (h : ConjEq u v) : u = v := by
  obtain ⟨p, q, rfl⟩ := h
  simp

/-- `ConjEq u v` implies `HEq u v`. -/
lemma heq {u : X ⟶ Y} {v : X' ⟶ Y'} (h : ConjEq u v) : HEq u v := by
  obtain ⟨p, q, rfl⟩ := h
  subst p; subst q
  simp

/-- If `u ~ u'` and `v ~ v'` (with `u, v` and `u', v'` parallel), then `u = v ↔ u' = v'`. -/
lemma eq_iff {u v : X ⟶ Y} {u' v' : X' ⟶ Y'} (hu : ConjEq u u') (hv : ConjEq v v') :
    u = v ↔ u' = v' := by
  obtain ⟨p, q, rfl⟩ := hu
  obtain ⟨p', q', rfl⟩ := hv
  subst p; subst q
  simp

/-- If `u ~ u'` and `v ~ v'`, then `u = v` iff `v'` equals `u'` conjugated by the given `eqToHom`s.
-/
lemma eq_iff_conj {u v : X ⟶ Y} {u' : X' ⟶ Y'} {v' : X'' ⟶ Y''} (hu : ConjEq u u')
    (hv : ConjEq v v') (r : X'' = X') (s : Y' = Y'') :
    u = v ↔ v' = eqToHom r ≫ u' ≫ eqToHom s := by
  obtain ⟨p, q, rfl⟩ := hu
  obtain ⟨p', q', rfl⟩ := hv
  subst p; subst q; subst r; subst s
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact eq_comm

/-- If `v ~ w`, then `v` is an `eqToHom` (as `eqToHom r = v`) iff `w` is one (as `w = eqToHom P`).
-/
lemma eqToHom_eq_iff {v : X ⟶ Y} {w : X' ⟶ Y'} (h : ConjEq v w) (r : X = Y) (P : X' = Y') :
    eqToHom r = v ↔ w = eqToHom P := by
  obtain ⟨p, q, rfl⟩ := h
  subst p; subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- `ConjEq` morphisms are simultaneously isomorphisms. -/
lemma isIso_iff {u : X ⟶ Y} {v : X' ⟶ Y'} (h : ConjEq u v) : IsIso u ↔ IsIso v := by
  obtain ⟨p, q, rfl⟩ := h
  subst p; subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- `ConjEq` morphisms are simultaneously of the form `eqToHom e`. -/
lemma exists_eqToHom_iff {u : X ⟶ Y} {v : X' ⟶ Y'} (h : ConjEq u v) :
    (∃ e, u = eqToHom e) ↔ ∃ e, v = eqToHom e := by
  obtain ⟨p, q, rfl⟩ := h
  subst p; subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end ConjEq

end ConjEqCalculus

section Whiskering

variable {Obj : Type u} [Bicategory.{w, v} Obj]

namespace ConjEq

variable {x a b c d : Obj}

/-- Right whiskering by a 1-cell `h` preserves `ConjEq` of 2-cells. -/
lemma whiskerRight {f g f' g' : a ⟶ b} {u : f ⟶ g} {u' : f' ⟶ g'} (hu : ConjEq u u')
    (h : b ⟶ c) : ConjEq (u ▷ h) (u' ▷ h) := by
  obtain ⟨p, q, rfl⟩ := hu
  exact ⟨congr($p ≫ h), congr($q ≫ h), by simp⟩

/-- Left whiskering by a 1-cell `k` preserves `ConjEq` of 2-cells. -/
lemma whiskerLeft (k : x ⟶ a) {f g f' g' : a ⟶ b} {u : f ⟶ g} {u' : f' ⟶ g'}
    (hu : ConjEq u u') : ConjEq (k ◁ u) (k ◁ u') := by
  obtain ⟨p, q, rfl⟩ := hu
  exact ⟨congr(k ≫ $p), congr(k ≫ $q), by simp⟩

/-- Left whiskering a 2-cell `u` by equal 1-cells `k = k'` gives `ConjEq` 2-cells. -/
lemma whiskerLeft_congr' {k k' : x ⟶ a} (e : k = k') {f g : a ⟶ b} (u : f ⟶ g) :
    ConjEq (k ◁ u) (k' ◁ u) := by
  subst e
  exact of_eq rfl

variable [Bicategory.Strict Obj]

/-- `𝟙 a ◁ u` is `ConjEq` to `u`. -/
lemma id_whiskerLeft {f g : a ⟶ b} (u : f ⟶ g) : ConjEq (𝟙 a ◁ u) u :=
  ⟨Category.id_comp f, (Category.id_comp g).symm, Bicategory.Strict.id_whiskerLeft u⟩

/-- `(k ≫ l) ◁ u` is `ConjEq` to `k ◁ (l ◁ u)`. -/
lemma whiskerLeft_comp₁ (k : x ⟶ a) (l : a ⟶ b) {f g : b ⟶ c} (u : f ⟶ g) :
    ConjEq ((k ≫ l) ◁ u) (k ◁ (l ◁ u)) :=
  ⟨Category.assoc k l f, (Category.assoc k l g).symm, Bicategory.Strict.comp_whiskerLeft k l u⟩

/-- `u ▷ (h ≫ k)` is `ConjEq` to `(u ▷ h) ▷ k`. -/
lemma whiskerRight_comp₁ {f g : a ⟶ b} (u : f ⟶ g) (h : b ⟶ c) (k : c ⟶ d) :
    ConjEq (u ▷ (h ≫ k)) ((u ▷ h) ▷ k) :=
  ⟨(Category.assoc f h k).symm, Category.assoc g h k, Bicategory.Strict.whiskerRight_comp u h k⟩

/-- `k ◁ (u ▷ h)` is `ConjEq` to `(k ◁ u) ▷ h`. -/
lemma whiskerLeft_whiskerRight (k : x ⟶ a) {f g : a ⟶ b} (u : f ⟶ g) (h : b ⟶ c) :
    ConjEq (k ◁ (u ▷ h)) ((k ◁ u) ▷ h) :=
  ⟨(Category.assoc k f h).symm, Category.assoc k g h, Bicategory.Strict.whisker_assoc k u h⟩

end ConjEq

variable [Bicategory.Strict Obj]

/-- Whiskering by a 1-cell `p` with a section `s` (`s ≫ p = id`) is injective. -/
lemma whiskerLeft_cancel_of_section {X Y Z : Obj} (p : X ⟶ Y) (s : Y ⟶ X)
    (h : s ≫ p = 𝟙 Y) {f g : Y ⟶ Z} {u u' : f ⟶ g} (H : p ◁ u = p ◁ u') : u = u' := by
  have key : ∀ w : f ⟶ g, w = eqToHom (by rw [← Category.assoc, h, Category.id_comp]) ≫ (s ◁ (p ◁
    w)) ≫
      eqToHom (by rw [← Category.assoc, h, Category.id_comp]) := by
    intro w
    rw [Bicategory.Strict.comp_whiskerLeft', Bicategory.whiskerLeft_congr' h,
      Bicategory.Strict.id_whiskerLeft]
    simp
  rw [key u, key u', H]

end Whiskering

end UlmerBialgebras
