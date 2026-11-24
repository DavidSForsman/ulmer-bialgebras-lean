module

public import InternalGroups.GrpObjSubgroupCorrespondence
public import Mathlib.Order.Antisymmetrization

/-!
# Newman's correspondence: towards surjectivity onto the regular quotients

This file begins the companion direction of the Galois connection of
`InternalGroups/GrpObjSubgroupCorrespondence.lean`.  It is a port, still in progress, of the
corresponding results of D. Forsman's exactness development for internal groups (the external
`RequestProject` development); `quot_stab_le` is the half of the correspondence proved here.

**Not yet implemented:** the identification of the kernel pair of a quotient module with the
coset relation of the stabiliser of its base point, the surjectivity of `cosetQuot` onto the
regular quotients, and the antisymmetrisation of the correspondence.

## Main results

* `InternalGroups.quot_stab_le`: the coset quotient of the stabiliser of a quotient module is a
  quotient of it (one half of the correspondence);
* `InternalGroups.SubGrp.regularEpiQuot`: the coset quotient is a regular epimorphism of
  `G`-modules;
* `InternalGroups.RegQuot` (regular quotient modules, with their preorder), `SubGrp.regQuot`,
  `RegQuot.stab` and the monotone map `cosetQuot : SubGrp G →o RegQuot G`: the map whose
  surjectivity is Newman's correspondence.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups

open CategoryTheory


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G : C} [GrpObj G]

section CosetRel

variable [HasPullbacks C]

open QuotMod

end CosetRel

/-! ## Newman's correspondence -/

section Correspondence

open QuotMod

variable [HasPullbacks C] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

/-- Half of the correspondence, from the Galois connection: the coset quotient of the stabiliser
of a quotient module `q` is a quotient of `q`. -/
theorem quot_stab_le (q : QuotMod G) : (stab q).quot ≤ q :=
  galoisConnection_quot_stab.l_u_le q

/-- The coset quotient is a regular epimorphism of `G`-modules. -/
noncomputable def SubGrp.regularEpiQuot (s : SubGrp G) : RegularEpi (s.quot).p where
  W := (freeMod G).obj s.toSubMon.N.X
  left := SubMon.mulTranspose s.toSubMon
  right := SubMon.oneTranspose isTerminalTensorUnit s.toSubMon
  w := coequalizer.condition _ _
  isColimit := coequalizerIsCoequalizer _ _

/-! ### The correspondence as a bijection -/

/-- A **regular quotient module** of `G`. -/
structure RegQuot (G : C) [MonObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)] where
  /-- the underlying quotient module -/
  toQuotMod : QuotMod G
  /-- the quotient map is a regular epimorphism -/
  reg : RegularEpi toQuotMod.p

/-- Regular quotient modules are preordered as quotient modules are. -/
instance : Preorder (RegQuot G) := Preorder.lift RegQuot.toQuotMod

/-- **Newman's correspondence**, from subgroup objects to regular quotient modules. -/
noncomputable def SubGrp.regQuot (s : SubGrp G) : RegQuot G := ⟨s.quot, s.regularEpiQuot⟩

/-- The inverse correspondence: the stabiliser of the base point. -/
noncomputable def RegQuot.stab (q : RegQuot G) : SubGrp G := InternalGroups.stab q.toQuotMod

/-- **Newman's correspondence** as a monotone map. -/
noncomputable def cosetQuot : SubGrp G →o RegQuot G where
  toFun s := s.regQuot
  monotone' _ _ h := galoisConnection_quot_stab.monotone_l h

/-- The correspondence map sends a subgroup object to its regular quotient module. -/
@[simp] lemma cosetQuot_apply (s : SubGrp G) : cosetQuot s = s.regQuot := rfl

end Correspondence


end InternalGroups
