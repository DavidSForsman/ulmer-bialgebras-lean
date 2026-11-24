module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# Functors preserve reflexive pairs

The image of a reflexive pair under a functor is a reflexive pair, with the image of the common
section.

## Main results

* `CategoryTheory.isReflexivePair_map`: functors preserve reflexive pairs.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], IV.7
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

/-- Functors preserve reflexive pairs. -/
lemma isReflexivePair_map {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {A B : C} {f g : A ⟶ B} (h : IsReflexivePair f g) :
    IsReflexivePair (F.map f) (F.map g) := by
  obtain ⟨s, hf, hg⟩ := h.common_section'
  exact .mk' (F.map s) (by rw [← F.map_comp, hf, F.map_id]) (by rw [← F.map_comp, hg, F.map_id])

end CategoryTheory

end
