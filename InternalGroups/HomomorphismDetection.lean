module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Foundations.CategoryTheory.Grp.GrpObjPullback

/-!
# Detecting homomorphisms of internal groups through a monomorphism

`InternalGroups.Internal.isMonHom_of_comp_mono`: in a cartesian monoidal category, a morphism
`h : T ⟶ W` between internal groups is a homomorphism of internal monoids as soon as its
composite `h ≫ m` with a monomorphism `m : W ⟶ V` that is a homomorphism is one.

Its lemma is elementary and general, not a result of the author; it is part of the library because
the exactness criterion uses it.

## Main results

* `InternalGroups.Internal.isMonHom_of_comp_mono`: if `m : W ⟶ V` is a monomorphism and a
  homomorphism of internal monoids and `h ≫ m` is a homomorphism, then `h : T ⟶ W` is a
  homomorphism.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory MonObj

namespace InternalGroups
namespace Internal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section Separator

variable {G H A : C} [GrpObj G] [Closed G]

variable [GrpObj A]

end Separator

section Main

/-- A morphism which becomes a homomorphism of internal groups after composition with a
monomorphism of internal groups is itself a homomorphism. -/
lemma isMonHom_of_comp_mono {T W V : C} [GrpObj T] [GrpObj W] [GrpObj V] (h : T ⟶ W) (m : W ⟶ V)
    [Mono m] [IsMonHom m] [IsMonHom (h ≫ m)] : IsMonHom h := by
  refine isMonHom_of_mul' _ fun S a b => ?_
  rw [← cancel_mono m, Category.assoc, MonObj.mul_comp _ _ (h ≫ m), MonObj.mul_comp _ _ m]
  simp

end Main

end Internal
end InternalGroups
