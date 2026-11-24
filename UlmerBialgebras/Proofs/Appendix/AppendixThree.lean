module

public import UlmerBialgebras.Paper.AppendixDefsThree
public import UlmerBialgebras.Proofs.Appendix.AppendixProbes

/-!
# Functors out of the three-object probe

A `V`-functor `3_{x,y} ⟶ C` out of the linear `V`-category on `0 → 1 → 2` is determined by its
three vertices and its two edge maps (`threeVFunctor_reconstruct`). This is the uniqueness part
of the description of such functors that follows Definition A.4 and is used in Theorem A.5.

## Main results

* `UlmerBialgebras.Paper.Appendix.threeVFunctor_reconstruct`: a `V`-functor `F : 3_{x,y} ⟶ C` equals
  the functor `threeVFunctor` built from its three vertices and its two edge maps.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma A.3, Definition A.4 and Theorem A.5
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

section Emap

variable (Z : MonoidalInitial V) (x y : V) {C : Type u} [Category.{w} C]
  [EnrichedOrdinaryCategory V C] (c₀ c₁ c₂ : C) (f : x ⟶ (c₀ ⟶[V] c₁)) (g : y ⟶ (c₁ ⟶[V] c₂))

/-- `threeVFunctor` sends the vertex `0` to `c₀`. -/
@[simp] lemma threeVFunctor_obj_zero :
    (threeVFunctor.{w, v, u} Z x y c₀ c₁ c₂ f g).obj .zero = c₀ := rfl

/-- `threeVFunctor` sends the vertex `1` to `c₁`. -/
@[simp] lemma threeVFunctor_obj_one :
    (threeVFunctor.{w, v, u} Z x y c₀ c₁ c₂ f g).obj .one = c₁ := rfl

/-- `threeVFunctor` sends the vertex `2` to `c₂`. -/
@[simp] lemma threeVFunctor_obj_two :
    (threeVFunctor.{w, v, u} Z x y c₀ c₁ c₂ f g).obj .two = c₂ := rfl

/-- On the edge `0 → 1`, `threeVFunctor` is `f`. -/
@[simp] lemma threeVFunctor_emap_zero_one :
    (threeVFunctor.{w, v, u} Z x y c₀ c₁ c₂ f g).emap .zero .one = f := rfl

/-- On the edge `1 → 2`, `threeVFunctor` is `g`. -/
@[simp] lemma threeVFunctor_emap_one_two :
    (threeVFunctor.{w, v, u} Z x y c₀ c₁ c₂ f g).emap .one .two = g := rfl

/-- On the composite `0 → 2`, `threeVFunctor` is `f ⊗ g` followed by composition. -/
@[simp] lemma threeVFunctor_emap_zero_two :
    (threeVFunctor.{w, v, u} Z x y c₀ c₁ c₂ f g).emap .zero .two =
      (f ⊗ₘ g) ≫ eComp V c₀ c₁ c₂ := rfl

end Emap

/-- A functor from the three-object probe is forced by its vertices and edge maps. -/
theorem threeVFunctor_reconstruct (Z : MonoidalInitial V) (x y : V)
    (C : VCat.{w, v, u} V) (F : threeVCat.{w, v, u} Z x y ⟶ C) :
    F = threeVFunctor Z x y (F.obj .zero) (F.obj .one) (F.obj .two)
      (F.emap .zero .one) (F.emap .one .two) := by
  apply vFunctor_ext_obj_heq
  · funext a
    cases a <;> rfl
  · intro a b
    cases a <;> cases b <;> apply heq_of_eq
    · exact (Category.id_comp _).symm.trans (F.emap_id .zero)
    · rfl
    · exact (Category.id_comp _).symm.trans (F.emap_comp .zero .one .two)
    · exact Z.isInitial.hom_ext _ _
    · exact (Category.id_comp _).symm.trans (F.emap_id .one)
    · rfl
    · exact Z.isInitial.hom_ext _ _
    · exact Z.isInitial.hom_ext _ _
    · exact (Category.id_comp _).symm.trans (F.emap_id .two)

end UlmerBialgebras.Paper.Appendix
