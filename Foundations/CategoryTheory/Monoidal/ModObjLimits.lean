module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Foundations.CategoryTheory.Exact.CoreflexiveTransport

/-!
# Reflection of isomorphisms for module objects

The forgetful functor from module objects reflects isomorphisms.

## Main results

* `CategoryTheory.Mod_.forget_reflectsIsomorphisms`: the forgetful functor from module objects to
  the ambient category reflects isomorphisms.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Section VII.4
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.13
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Limits
open scoped MonoidalLeftAction ModObj

section

namespace CategoryTheory.Mod_

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]
variable {A : C} [MonObj A]

/-- The forgetful functor from module objects to the ambient category reflects isomorphisms. -/
instance forget_reflectsIsomorphisms :
    (CategoryTheory.Mod.forget (D := D) A).ReflectsIsomorphisms where
  reflects {M N} f hf := by
    have : IsIso f.hom := hf
    have hcomm : γ[N.X] ≫ inv f.hom = A ⊴ₗ inv f.hom ≫ γ[M.X] := by
      rw [← cancel_epi (A ⊴ₗ f.hom), ← Category.assoc, ← IsModHom.smul_hom,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id, ← Category.assoc,
        ← MonoidalLeftAction.actionHomRight_comp, IsIso.hom_inv_id,
        MonoidalLeftAction.actionHomRight_id, Category.id_comp]
    exact ⟨⟨CategoryTheory.Mod.Hom.mk' (inv f.hom) hcomm, by ext; simp, by ext; simp⟩⟩

section

variable {J : Type*} [Category J] (K : J ⥤ CategoryTheory.Mod D A)
  (c : Cone (K ⋙ CategoryTheory.Mod.forget (D := D) A))

variable (hc : IsLimit c)

include hc

end

end CategoryTheory.Mod_

end
