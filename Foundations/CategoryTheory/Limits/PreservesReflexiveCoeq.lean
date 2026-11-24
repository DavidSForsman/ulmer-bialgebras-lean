module

public import Mathlib.CategoryTheory.Monad.Monadicity

/-!
# Functors preserving reflexive coequalizers

The one local notion of preservation of reflexive coequalizers, for functors between categories
with possibly different hom universes, and its comparison with Mathlib's
`CategoryTheory.Monad.PreservesColimitOfIsReflexivePair`, which asks for one hom universe.

## Main definitions

* `CategoryTheory.PreservesReflexiveCoeq`: `F` preserves the coequalizer of every reflexive pair.

## Main results

* `CategoryTheory.preservesReflexiveCoeq_iff`: for one hom universe, the class is Mathlib's
  `Monad.PreservesColimitOfIsReflexivePair`; both directions are instances.

## References

* [M. Barr, C. Wells, *Toposes, triples, and theories*][barrToposesTriplesTheories1985]
-/

@[expose] public section

universe v u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory

/-- The functor `F` preserves the coequalizer of every reflexive pair. -/
class PreservesReflexiveCoeq {A : Type*} [Category A] {B : Type*} [Category B] (F : A ⥤ B) :
    Prop where
  preserves : ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), IsReflexivePair u v → PreservesColimit (parallelPair u v) F

/-- A functor with `PreservesReflexiveCoeq` preserves the coequalizer of any reflexive pair. -/
instance preservesColimit_parallelPair_of_preservesReflexiveCoeq {A : Type*} [Category A]
    {B : Type*} [Category B] (F : A ⥤ B) [PreservesReflexiveCoeq F] {X Y : A} (u v : X ⟶ Y)
    [h : IsReflexivePair u v] : PreservesColimit (parallelPair u v) F :=
  PreservesReflexiveCoeq.preserves u v h

section SameUniverse

variable {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B] (F : A ⥤ B)

/-- Mathlib's `Monad.PreservesColimitOfIsReflexivePair` gives `PreservesReflexiveCoeq`. -/
instance preservesReflexiveCoeq_of_preservesColimitOfIsReflexivePair
    [Monad.PreservesColimitOfIsReflexivePair F] : PreservesReflexiveCoeq F where
  preserves _ _ u v _ := Monad.PreservesColimitOfIsReflexivePair.out u v

/-- `PreservesReflexiveCoeq` gives Mathlib's `Monad.PreservesColimitOfIsReflexivePair`. -/
instance preservesColimitOfIsReflexivePair_of_preservesReflexiveCoeq [PreservesReflexiveCoeq F] :
    Monad.PreservesColimitOfIsReflexivePair F where
  out _ _ _ _ _ := inferInstance

/-- For one hom universe, `PreservesReflexiveCoeq` is Mathlib's
`Monad.PreservesColimitOfIsReflexivePair`. -/
theorem preservesReflexiveCoeq_iff :
    PreservesReflexiveCoeq F ↔ Monad.PreservesColimitOfIsReflexivePair F :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

end SameUniverse

end CategoryTheory
