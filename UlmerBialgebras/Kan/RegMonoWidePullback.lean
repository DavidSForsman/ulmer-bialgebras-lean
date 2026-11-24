module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import UlmerBialgebras.Kan.Sifted
public import Foundations.CategoryTheory.Limits.OpTranslate

/-!
# Regular-mono wide-pullback interfaces

This file defines the regular-mono wide-pullback preservation predicates and coreflexive
equalizer presentations used by the opposite-category translations in
`UlmerBialgebras/Proofs/Sec4/OpTranslateWide.lean`.

## Main results

* `UlmerBialgebras.RegMonoWide.regMono`: the class of regular monomorphisms, as a morphism property.
* `UlmerBialgebras.RegMonoWide.PreservesWidePullbacksIn`: `G` preserves `K`-wide pullbacks of
  families of morphisms in a given class.
* `UlmerBialgebras.RegMonoWide.RegularMonosAreCoreflexiveEqualizers`: every regular monomorphism is
  the equalizer of a coreflexive pair.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 4.19,
  Example 4.20 (2)
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace UlmerBialgebras.RegMonoWide

open CategoryTheory Limits

variable {K : Type w}

section Defs

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]

/-- The class of regular monomorphisms of a category, as a morphism property. -/
def regMono (X : Type u₁) [Category.{v₁} X] : MorphismProperty X :=
  fun _ _ f => IsRegularMono f

/-- A `K`-wide cospan all of whose legs satisfy `M`. -/
def IsWideCospanIn (M : MorphismProperty X) (Dg : WidePullbackShape K ⥤ X) : Prop :=
  ∀ k, M (Dg.map (WidePullbackShape.Hom.term k))

/-- `G` preserves (all existing) `K`-wide pullbacks of families of `M`-morphisms. -/
def PreservesWidePullbacksIn (K : Type w) (M : MorphismProperty X) (G : X ⥤ Y) : Prop :=
  ∀ Dg : WidePullbackShape K ⥤ X, IsWideCospanIn M Dg → PreservesLimit Dg G

/-- Every regular monomorphism is the equalizer of a coreflexive pair. -/
def RegularMonosAreCoreflexiveEqualizers (X : Type u₁) [Category.{v₁} X] : Prop :=
  ∀ ⦃a c : X⦄ (m : a ⟶ c), IsRegularMono m →
    ∃ (q : X) (f g : c ⟶ q) (_ : IsCoreflexivePair f g) (w : m ≫ f = m ≫ g),
      Nonempty (IsLimit (Fork.ofι m w))

end Defs

end UlmerBialgebras.RegMonoWide
