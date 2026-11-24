module

public import Foundations.CategoryTheory.Limits.OpTranslate

/-!
# Regular mono categories along equivalences

The property that every monomorphism is regular transfers along an equivalence of categories
(`CategoryTheory.isRegularMonoCategory_of_equivalence`). A monomorphism `f` of the target is
isomorphic, as an arrow, to the image under `e.functor` of the monomorphism `e.inverse.map f`,
and equalizer-preserving functors preserve regular monomorphisms
(`UlmerBialgebras.OpTranslate.isRegularMono_map`).

## Main results

* `CategoryTheory.isRegularMonoCategory_of_equivalence`: `IsRegularMonoCategory` transfers along
  an equivalence.

## References

* F. Borceux, *Handbook of Categorical Algebra 1: Basic Category Theory* (1994), §4.3
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Being a regular mono category transfers along an equivalence.** -/
theorem isRegularMonoCategory_of_equivalence (e : C ≌ D) [IsRegularMonoCategory C] :
    IsRegularMonoCategory D where
  regularMonoOfMono {X Y} f _ := by
    have : IsRegularMono (e.inverse.map f) := IsRegularMonoCategory.regularMonoOfMono _
    have : IsRegularMono (e.functor.map (e.inverse.map f)) :=
      UlmerBialgebras.OpTranslate.isRegularMono_map e.functor _
    exact ⟨⟨RegularMono.ofArrowIso (Arrow.isoMk (f := Arrow.mk (e.functor.map (e.inverse.map f)))
      (g := Arrow.mk f) (e.counitIso.app X) (e.counitIso.app Y)
      (e.counit.naturality f).symm) (IsRegularMono.getStruct _)⟩⟩

end CategoryTheory
