module

public import Mathlib.CategoryTheory.Bicategory.Opposites
public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Strictness of opposite and induced bicategories

The 1-cell opposite `Bᵒᵖ` of a strict bicategory is strict; Mathlib already makes the induced
bicategory `InducedBicategory C F` of a strict bicategory strict. These are the index
2-categories of the hom 2-functors used in the proof of Theorem 7.4.

## Main results

* `Bicategory.Opposite.strict`: `Bᵒᵖ` is strict when `B` is.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.4
-/

@[expose] public section

universe w v u

open CategoryTheory Bicategory

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- `op2` of an `eqToHom` is an `eqToHom`. -/
lemma op2_eqToHom {a b : B} {f g : a ⟶ b} (h : f = g) :
    op2 (eqToHom h) = eqToHom (congrArg Quiver.Hom.op h) := by
  subst h; rfl

instance strict [Bicategory.Strict B] : Bicategory.Strict Bᵒᵖ where
  id_comp f := Quiver.Hom.unop_inj (Category.comp_id f.unop)
  comp_id f := Quiver.Hom.unop_inj (Category.id_comp f.unop)
  assoc f g h := Quiver.Hom.unop_inj (Category.assoc h.unop g.unop f.unop).symm
  leftUnitor_eqToIso f := by
    ext
    rw [eqToIso.hom, ← op2_unop2 (λ_ f).hom, bicategory_leftUnitor_hom_unop2,
      Strict.rightUnitor_eqToIso, eqToIso.hom, op2_eqToHom]
  rightUnitor_eqToIso f := by
    ext
    rw [eqToIso.hom, ← op2_unop2 (ρ_ f).hom, bicategory_rightUnitor_hom_unop2,
      Strict.leftUnitor_eqToIso, eqToIso.hom, op2_eqToHom]
  associator_eqToIso f g h := by
    ext
    rw [eqToIso.hom, ← op2_unop2 (α_ f g h).hom, bicategory_associator_hom_unop2,
      Strict.associator_eqToIso, eqToIso.inv, op2_eqToHom]

end Bicategory.Opposite

