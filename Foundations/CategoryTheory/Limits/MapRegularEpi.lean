module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Foundations.CategoryTheory.Monoidal.MonadReflexive

/-!
# Mapping regular epimorphisms using reflexive coequalizers

## Main results

* `CategoryTheory.isRegularEpi_map_of_preservesReflexiveCoeq`.

## References

* [M. Barr, *Exact Categories*][Ba]
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open Limits
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A functor preserving reflexive coequalizers maps a regular epimorphism with a kernel pair
 to a regular epimorphism. -/
theorem isRegularEpi_map_of_preservesReflexiveCoeq (F : C ⥤ D) [PreservesReflexiveCoeq F]
    {X Y : C} (f : X ⟶ Y) [IsRegularEpi f] [HasPullback f f] : IsRegularEpi (F.map f) := by
  let k := IsKernelPair.of_hasPullback f
  let _ : IsReflexivePair (pullback.fst f f) (pullback.snd f f) := k.isReflexivePair
  have h := (isColimitMapCoconeCoforkEquiv F k.w)
    (isColimitOfPreserves F k.toCoequalizer')
  exact ⟨⟨{ W := F.obj (pullback f f)
            left := F.map (pullback.fst f f)
            right := F.map (pullback.snd f f)
            w := by rw [← F.map_comp, ← F.map_comp, pullback.condition]
            isColimit := h }⟩⟩

end CategoryTheory
