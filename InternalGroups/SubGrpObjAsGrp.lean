module

public import Foundations.CategoryTheory.Grp.GrpRegular
public import InternalGroups.GrpSubQuot

/-!
# Subgroup objects are group objects with a monomorphic inclusion

Let `C` be a cartesian monoidal category and `H : Grp C` a group object.  The two possible
descriptions of a subgroup object of `H` are:

* the elementwise one, `InternalGroups.SubGrpObj H`: a monomorphism `n : N ⟶ H.X` whose generalized
  elements are closed under the unit, the multiplication and the inverse of `H`;
* the structural one: a group object `G : Grp C` together with a morphism of group objects
  `f : G ⟶ H` whose underlying morphism is a monomorphism.

This file proves that the two agree:

* `InternalGroups.SubGrpObj.grpObj` — the underlying object of a subgroup object is a group object,
  `InternalGroups.SubGrpObj.isMonHom_n` — for which the inclusion is a morphism of group objects,
  so `InternalGroups.SubGrpObj.toGrp` and `InternalGroups.SubGrpObj.incl` produce the structural
  data;
* `InternalGroups.SubGrpObj.ofGrpHom` — conversely a monomorphic morphism of group objects is a
  subgroup object in the elementwise sense.

## Main results

* `InternalGroups.SubGrpObj.grpObj`: the underlying object of a subgroup object is a group object.
* `InternalGroups.SubGrpObj.isMonHom_n`: the inclusion of a subgroup object is a morphism of monoid
  objects.
* `InternalGroups.SubGrpObj.incl`: the inclusion as a morphism `S.toGrp ⟶ H` of group objects.
* `InternalGroups.SubGrpObj.ofGrpHom`: a morphism of group objects whose underlying morphism is a
  monomorphism gives a subgroup object.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 6.3,
  Corollary 6.11
-/

@[expose] public section

universe v u

namespace InternalGroups

open UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {H : Grp C}

namespace SubGrpObj

variable (S : SubGrpObj H)

/-- The unit of a subgroup object, chosen by closedness under the unit. -/
noncomputable def one' : 𝟙_ C ⟶ S.N := (S.one_mem (𝟙_ C)).choose

/-- The chosen unit of `S` composed with the inclusion is the unit of `H`. -/
@[reassoc]
lemma one'_comp : S.one' ≫ S.n = η[H.X] := by
  refine (S.one_mem (𝟙_ C)).choose_spec.trans ?_
  rw [Hom.one_def, SemiCartesianMonoidalCategory.toUnit_unique (toUnit (𝟙_ C)) (𝟙 _),
    Category.id_comp]

/-- The multiplication of a subgroup object, chosen by closedness under multiplication. -/
noncomputable def mul' : S.N ⊗ S.N ⟶ S.N := (S.mul_mem (fst S.N S.N) (snd S.N S.N)).choose

/-- The chosen multiplication of `S` is compatible with that of `H` along the inclusion. -/
@[reassoc]
lemma mul'_comp : S.mul' ≫ S.n = (S.n ⊗ₘ S.n) ≫ μ[H.X] := by
  refine (S.mul_mem (fst S.N S.N) (snd S.N S.N)).choose_spec.trans ?_
  rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]

/-- The inverse of a subgroup object, chosen by closedness under inverses. -/
noncomputable def inv' : S.N ⟶ S.N := (S.inv_mem (𝟙 S.N)).choose

/-- The chosen inverse of `S` is compatible with that of `H` along the inclusion. -/
@[reassoc]
lemma inv'_comp : S.inv' ≫ S.n = S.n ≫ ι[H.X] := by
  refine (S.inv_mem (𝟙 S.N)).choose_spec.trans ?_
  rw [Category.id_comp, Hom.inv_def]

/-- **The underlying object of a subgroup object is a group object.** -/
@[instance_reducible]
noncomputable def grpObj : GrpObj S.N := subGrpObj S.mul'_comp S.one'_comp S.inv'_comp

attribute [local instance] grpObj

/-- **The inclusion of a subgroup object is a morphism of group objects.** -/
lemma isMonHom_n : IsMonHom S.n := isMonHom_sub S.mul'_comp S.one'_comp

attribute [local instance] isMonHom_n

/-- A subgroup object, viewed as a group object of `C`. -/
noncomputable def toGrp : Grp C := Grp.mk S.N

/-- The inclusion of a subgroup object, as a morphism of group objects. -/
noncomputable def incl : S.toGrp ⟶ H := @Grp.homMk _ _ _ S.toGrp H S.n S.isMonHom_n

/-- **A monomorphic morphism of group objects is a subgroup object.** -/
def ofGrpHom {G : Grp C} (f : G ⟶ H) (hf : Mono f.hom.hom) : SubGrpObj H where
  N := G.X
  n := f.hom.hom
  mono := hf
  one_mem _ := ⟨1, MonObj.one_comp _⟩
  mul_mem x y := ⟨x * y, MonObj.mul_comp x y _⟩
  inv_mem x := ⟨x⁻¹, GrpObj.inv_comp x _⟩

end SubGrpObj

end InternalGroups
