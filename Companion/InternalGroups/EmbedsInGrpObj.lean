module

public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Categories whose objects embed into group objects

`InternalGroups.EmbedsInGrpObj C`: in a cartesian monoidal category `C`, every object has a
monomorphism into (the underlying object of) a group object. For `C = CommComon (ModuleCat k)`
this is the statement that every cocommutative coalgebra embeds into a cocommutative Hopf algebra
(`InternalGroups.embedsInGrpObj_commComon_moduleCat`, `Companion/Hopf/Embed/CommComonEmbeds.lean`).

## References

* D. Forsman, exactness criterion for internal groups (unpublished, announced)
-/

@[expose] public section

universe v u

open CategoryTheory

namespace InternalGroups

/-- **Every object embeds into a group object**: for every `X : C` there are a group object `G` of
`C` and a monomorphism `X ⟶ G`. -/
def EmbedsInGrpObj (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] : Prop :=
  ∀ X : C, ∃ (G : Grp C) (f : X ⟶ G.X), Mono f

end InternalGroups
