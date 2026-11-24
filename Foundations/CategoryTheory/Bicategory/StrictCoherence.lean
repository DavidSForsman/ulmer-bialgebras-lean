module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Coherence in a strict bicategory, with `eqToHom`

In a strict bicategory (`CategoryTheory.Bicategory.Strict`) the associators and unitors are
`eqToIso`s. The whiskering laws of a bicategory then become equations between 2-cells transported
along equalities of 1-cells. This file states them in that form, under the names of the
corresponding general lemmas of `CategoryTheory.Bicategory`:

* `Bicategory.Strict.id_whiskerLeft`: `𝟙 a ◁ η = eqToHom _ ≫ η ≫ eqToHom _`;
* `Bicategory.Strict.whiskerRight_id`: `η ▷ 𝟙 b = eqToHom _ ≫ η ≫ eqToHom _`;
* `Bicategory.Strict.comp_whiskerLeft`: `(f ≫ g) ◁ η = eqToHom _ ≫ f ◁ g ◁ η ≫ eqToHom _`;
* `Bicategory.Strict.whiskerRight_comp`: `η ▷ (h ≫ k) = eqToHom _ ≫ (η ▷ h) ▷ k ≫ eqToHom _`;
* `Bicategory.Strict.whisker_assoc`: `f ◁ (η ▷ k) = eqToHom _ ≫ (f ◁ η) ▷ k ≫ eqToHom _`;

and the converse forms, primed; and the same five as heterogeneous equalities, with the suffix
`_heq` (`Bicategory.Strict.id_whiskerLeft_heq`: `HEq (𝟙 a ◁ η) η`, and so on).
`Bicategory.whiskerLeft_congr` and `Bicategory.whiskerRight_congr` transport a whiskering along an
equality of the whiskering 1-cell, in any bicategory.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2.1
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

/-- Transporting a left whiskering along an equality of the whiskering 1-cell. -/
lemma whiskerLeft_congr {f f' : a ⟶ b} (e : f = f') {g h : b ⟶ c} (η : g ⟶ h) :
    f' ◁ η = eqToHom (by rw [e]) ≫ f ◁ η ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- Transporting a left whiskering along an equality of the whiskering 1-cell; the converse
form of `Bicategory.whiskerLeft_congr`. -/
lemma whiskerLeft_congr' {f f' : a ⟶ b} (e : f = f') {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ η = eqToHom (by rw [e]) ≫ f' ◁ η ≫ eqToHom (by rw [e]) := by
  subst e; simp

/-- Transporting a right whiskering along an equality of the whiskering 1-cell. -/
lemma whiskerRight_congr {f g : a ⟶ b} (η : f ⟶ g) {h h' : b ⟶ c} (e : h = h') :
    η ▷ h' = eqToHom (by rw [e]) ≫ η ▷ h ≫ eqToHom (by rw [e]) := by
  subst e; simp

namespace Strict

variable [Bicategory.Strict B] {d : B}

/-- Whiskering by an identity 1-cell on the left, in a strict bicategory. -/
lemma id_whiskerLeft {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η = eqToHom (Strict.id_comp f) ≫ η ≫ eqToHom (Strict.id_comp g).symm := by
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso]

/-- Whiskering by an identity 1-cell on the right, in a strict bicategory. -/
lemma whiskerRight_id {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b = eqToHom (Strict.comp_id f) ≫ η ≫ eqToHom (Strict.comp_id g).symm := by
  simp [Bicategory.whiskerRight_id, Strict.rightUnitor_eqToIso]

/-- Left whiskering by a composite, in a strict bicategory. -/
lemma comp_whiskerLeft (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ⟶ k) :
    (f ≫ g) ◁ η =
      eqToHom (Strict.assoc f g h) ≫ f ◁ g ◁ η ≫ eqToHom (Strict.assoc f g k).symm := by
  simp [Bicategory.comp_whiskerLeft, Strict.associator_eqToIso]

/-- Successive left whiskerings, in a strict bicategory; the converse form of
`Bicategory.Strict.comp_whiskerLeft`. -/
lemma comp_whiskerLeft' (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ⟶ k) :
    f ◁ g ◁ η =
      eqToHom (Strict.assoc f g h).symm ≫ (f ≫ g) ◁ η ≫ eqToHom (Strict.assoc f g k) := by
  rw [comp_whiskerLeft]; simp

/-- Right whiskering by a composite, in a strict bicategory. -/
lemma whiskerRight_comp {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) (k : c ⟶ d) :
    η ▷ (h ≫ k) =
      eqToHom (Strict.assoc f h k).symm ≫ (η ▷ h) ▷ k ≫ eqToHom (Strict.assoc g h k) := by
  simp [Bicategory.whiskerRight_comp, Strict.associator_eqToIso]

/-- Successive right whiskerings, in a strict bicategory; the converse form of
`Bicategory.Strict.whiskerRight_comp`. -/
lemma whiskerRight_comp' {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) (k : c ⟶ d) :
    (η ▷ h) ▷ k =
      eqToHom (Strict.assoc f h k) ≫ η ▷ (h ≫ k) ≫ eqToHom (Strict.assoc g h k).symm := by
  rw [whiskerRight_comp]; simp

/-- Left and right whiskering commute, in a strict bicategory. -/
lemma whisker_assoc (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) (k : c ⟶ d) :
    f ◁ (η ▷ k) =
      eqToHom (Strict.assoc f g k).symm ≫ (f ◁ η) ▷ k ≫ eqToHom (Strict.assoc f h k) := by
  simp [Bicategory.whisker_assoc, Strict.associator_eqToIso]

/-- Left and right whiskering commute, in a strict bicategory; the converse form of
`Bicategory.Strict.whisker_assoc`. -/
lemma whisker_assoc' (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) (k : c ⟶ d) :
    (f ◁ η) ▷ k =
      eqToHom (Strict.assoc f g k) ≫ f ◁ (η ▷ k) ≫ eqToHom (Strict.assoc f h k).symm := by
  rw [whisker_assoc]; simp

/-- Whiskering by an identity 1-cell on the left, up to heterogeneous equality. -/
lemma id_whiskerLeft_heq {f g : a ⟶ b} (α : f ⟶ g) : HEq (𝟙 a ◁ α) α :=
  (conj_eqToHom_iff_heq _ _ (Strict.id_comp f) (Strict.id_comp g)).1
    (Strict.id_whiskerLeft α)

/-- Whiskering by an identity 1-cell on the right, up to heterogeneous equality. -/
lemma whiskerRight_id_heq {f g : a ⟶ b} (α : f ⟶ g) : HEq (α ▷ 𝟙 b) α :=
  (conj_eqToHom_iff_heq _ _ (Strict.comp_id f) (Strict.comp_id g)).1
    (Strict.whiskerRight_id α)

/-- Left whiskering by a composite, up to heterogeneous equality. -/
lemma comp_whiskerLeft_heq (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (α : h ⟶ k) :
    HEq ((f ≫ g) ◁ α) (f ◁ g ◁ α) :=
  (conj_eqToHom_iff_heq _ _ (Strict.assoc f g h) (Strict.assoc f g k)).1
    (Strict.comp_whiskerLeft f g α)

/-- Right whiskering by a composite, up to heterogeneous equality. -/
lemma whiskerRight_comp_heq {f g : a ⟶ b} (α : f ⟶ g) (h : b ⟶ c) (k : c ⟶ d) :
    HEq (α ▷ (h ≫ k)) ((α ▷ h) ▷ k) :=
  (conj_eqToHom_iff_heq _ _ (Strict.assoc f h k).symm
    (Strict.assoc g h k).symm).1 (Strict.whiskerRight_comp α h k)

/-- Left and right whiskering commute, up to heterogeneous equality. -/
lemma whisker_assoc_heq (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) (k : c ⟶ d) :
    HEq (f ◁ (α ▷ k)) ((f ◁ α) ▷ k) :=
  (conj_eqToHom_iff_heq _ _ (Strict.assoc f g k).symm
    (Strict.assoc f h k).symm).1 (Strict.whisker_assoc f α k)

end Strict

end Bicategory

end CategoryTheory
