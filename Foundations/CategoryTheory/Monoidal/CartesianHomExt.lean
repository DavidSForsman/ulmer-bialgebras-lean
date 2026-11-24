module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Element extensionality for maps out of a product

In a cartesian monoidal category, two morphisms out of `A ⊗ B` (or `A ⊗ (B ⊗ N)`) agree as soon as
they agree on all pairs (triples) of generalized elements.

## Main results

* `CategoryTheory.CartesianMonoidalCategory.hom_ext_lift`: extensionality for maps out of a binary
  product.
* `CategoryTheory.CartesianMonoidalCategory.hom_ext_lift₃`: extensionality for maps out of
  `A ⊗ (B ⊗ N)`.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], III.2 (Yoneda)
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Two morphisms out of a binary product agree as soon as they agree on all pairs of
generalized elements. -/
lemma hom_ext_lift {A B D : C} {u v : A ⊗ B ⟶ D}
    (h : ∀ {T : C} (a : T ⟶ A) (b : T ⟶ B), lift a b ≫ u = lift a b ≫ v) : u = v := by
  have := h (fst A B) (snd A B)
  rwa [lift_fst_snd, Category.id_comp, Category.id_comp] at this

/-- Two morphisms out of an iterated binary product agree as soon as they agree on all
triples of generalized elements. -/
lemma hom_ext_lift₃ {A B N D : C} {u v : A ⊗ (B ⊗ N) ⟶ D}
    (h : ∀ {T : C} (a : T ⟶ A) (b : T ⟶ B) (c : T ⟶ N),
      lift a (lift b c) ≫ u = lift a (lift b c) ≫ v) : u = v := by
  refine hom_ext_lift ?_
  intro T a b
  have hb : lift (b ≫ fst B N) (b ≫ snd B N) = b := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have := h a (b ≫ fst B N) (b ≫ snd B N)
  rwa [hb] at this

end CategoryTheory.CartesianMonoidalCategory
