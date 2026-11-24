module

public import InternalGroups.GrpExactCriterion
public import InternalGroups.Pi0ConnectedReduction

/-!
# Underlying maps of zero group morphisms

The underlying morphism of the zero (trivial) internal-group homomorphism.

## Main results

* `InternalGroups.ConnExact.zero_hom_hom`: the underlying morphism of the zero morphism `K ⟶ Q` of
  internal groups is the trivial generalized element `1 : K.X ⟶ Q.X`.

## References

* [M. Barr, *Exact categories*][Ba]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
* [A. Carboni, S. Lack, R. F. C. Walters, *Introduction to extensive and distributive
  categories*][Lextensive]
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace InternalGroups

namespace ConnExact

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ### Generalized elements killed by a morphism of group objects -/

section Kills

variable {X Q : Grp C} (q : X ⟶ Q)

variable {q}

/-- The underlying morphism of the zero morphism of internal groups is the trivial generalized
element. -/
lemma zero_hom_hom {K Q : Grp C} :
    (0 : K ⟶ Q).hom.hom = (1 : K.X ⟶ Q.X) := by
  rw [Hom.one_def]
  rfl

end Kills

/-! ### The fibre over the unit -/

section Fibre

variable [HasEqualizers C] {X Q : Grp C} (q : X ⟶ Q)

variable {q}

end Fibre

/-! ### The two conditions -/

section Conditions

variable {K X Q : Grp C} (κ : K ⟶ X) (q : X ⟶ Q)

variable {κ q}

end Conditions

/-! ### The reduction to connected objects -/

section Reduction

variable [HasEqualizers C] {K X Q : Grp C} {κ : K ⟶ X} {q : X ⟶ Q}

end Reduction

/-! ### Factorizations of morphisms of group objects -/

section GrpHom

variable {K X Q : Grp C} {κ : K ⟶ X} {q : X ⟶ Q}

end GrpHom

end ConnExact

end InternalGroups
