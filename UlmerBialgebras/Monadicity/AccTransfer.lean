module

public import Mathlib.CategoryTheory.Presentable.Adjunction
public import UlmerBialgebras.Basic.AccClosure

/-!
# Accessibility under equivalences

Transfer of accessible categories and accessible functors along equivalences and equality.

## Main results

* `UlmerBialgebras.isAccessible_of_eq`: accessibility of a functor transfers along an equality.
* `UlmerBialgebras.isEquivalence_isAccessible`: an equivalence of categories is an accessible
  functor.
* `UlmerBialgebras.isAccessibleCategory_of_isEquivalence'`: accessibility of a category transfers
  backwards along an equivalence.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe w v v' v'' u u' u''

namespace UlmerBialgebras

open CategoryTheory Limits

/-- Accessibility of a functor only depends on the functor: it transfers along an equality. -/
theorem isAccessible_of_eq {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    {F G : A ⥤ B} (h : F = G) [Functor.IsAccessible.{w} F] : Functor.IsAccessible.{w} G := by
  subst h; infer_instance

/-- An equivalence of categories is an accessible functor: it preserves all colimits. -/
instance isEquivalence_isAccessible {A : Type u} [Category.{v} A] {B : Type u'}
    [Category.{v'} B] (F : A ⥤ B) [F.IsEquivalence] : Functor.IsAccessible.{w} F := by
  have : Fact (Cardinal.aleph0.{w}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  exact Functor.isAccessible_of_isCardinalAccessible _ Cardinal.aleph0.{w}

/-- Accessibility of a category transfers backwards along an equivalence. -/
theorem isAccessibleCategory_of_isEquivalence' {A : Type u} [Category.{v} A] {B : Type u'}
    [Category.{v'} B] (F : A ⥤ B) [F.IsEquivalence] [IsAccessibleCategory.{w} B] :
    IsAccessibleCategory.{w} A :=
  F.asEquivalence.symm.isAccessibleCategory

section

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D}
variable {X : Type u''} [Category.{v''} X]

variable {η θ : F ⟶ G}

end

section

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v'} (C i)]
variable {X : Type u''} [Category.{v''} X]

end

section

variable {ι : Type v} [Small.{w} ι] {C : ι → Type u} [∀ i, Category.{v'} (C i)]
variable {X : Type u''} [Category.{v''} X]

end

section

variable {ι : Type v} {C : ι → Type u} [∀ i, Category.{v'} (C i)]

end

end UlmerBialgebras
