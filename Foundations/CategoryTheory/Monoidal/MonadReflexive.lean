module

public import Mathlib.CategoryTheory.Monad.Limits
public import Foundations.CategoryTheory.Monoidal.ModObjColimits

/-!
# Reflexive coequalizers in Eilenberg–Moore categories

This file records the basic facts about reflexive coequalizers needed for the construction of
the (symmetric) monoidal structure on the Eilenberg–Moore category of a symmetric monoidal
monad.

## Main results

* `CategoryTheory.preservesColimit_parallelPair_comp`, `CategoryTheory.preservesReflexiveCoeq_comp`:
  stability of the class under composition of functors.

## References

* [M. Barr, C. Wells, *Toposes, triples, and theories*][barrToposesTriplesTheories1985]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.13
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory
open CategoryTheory

variable {A : Type*} [Category A] {B : Type*} [Category B] {D : Type*} [Category D]

/-- A functor preserving reflexive coequalizers preserves the coequalizer of a reflexive pair
transported along another functor. -/
lemma preservesColimit_parallelPair_comp (L : A ⥤ B) (F : B ⥤ D) [PreservesReflexiveCoeq F]
    {X Y : A} (u v : X ⟶ Y) (h : IsReflexivePair u v) :
    PreservesColimit (parallelPair u v ⋙ L) F := by
  have : IsReflexivePair (L.map u) (L.map v) := isReflexivePair_map L h
  have := CategoryTheory.PreservesReflexiveCoeq.preserves (F := F) (L.map u) (L.map v) inferInstance
  exact preservesColimit_of_iso_diagram F (parallelPairComp L u v).symm

/-- The composite of two functors preserving reflexive coequalizers preserves them. -/
instance preservesReflexiveCoeq_comp (F : A ⥤ B) (G : B ⥤ D)
    [PreservesReflexiveCoeq F] [PreservesReflexiveCoeq G] : PreservesReflexiveCoeq (F ⋙ G) where
  preserves := by
    intro X Y u v h
    have := h
    have := preservesColimit_parallelPair_comp F G u v h
    exact comp_preservesColimit (F := F) (G := G)

section

section Free

variable {C : Type u₁} [Category.{v₁} C] {T : CategoryTheory.Monad C}

end Free

end

section

variable {C : Type u₁} [Category.{v₁} C] (T : CategoryTheory.Monad C)

section

variable [HasReflexiveCoequalizers C] [PreservesReflexiveCoeq (T : C ⥤ C)]

end

end

end CategoryTheory
