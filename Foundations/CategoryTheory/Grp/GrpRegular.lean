module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Foundations.CategoryTheory.Factorization.RegularExact
public import Foundations.CategoryTheory.Grp.GrpLimits

/-!
# Group structures on subobjects

A subobject of an internal group closed under multiplication, the unit and inversion
inherits an internal group structure. The inclusion is a homomorphism of internal groups.
The construction uses cancellation along the inclusion to verify the group laws.

## Main results

* `UlmerBialgebras.subMonObj`: a subobject of a group object closed under the multiplication and the
  unit is a monoid object;
* `UlmerBialgebras.subGrpObj`: a subobject of a group object closed under the operations is a group
  object;
* `UlmerBialgebras.isMonHom_sub`: the inclusion of such a subobject is a morphism of monoid objects.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 6.3 and Theorem 6.6
* [F. E. J. Linton, *Coequalizers in categories of algebras*][Linton1969]
* [T. Wißmann, *Minimality notions via factorization systems and examples*][Wissmann2022Minimality],
  Proposition 3.7
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## Subobjects of group objects -/

section SubGrp

variable {I B : C} [GrpObj B] {m : I ⟶ B} {mI : I ⊗ I ⟶ I} {oI : 𝟙_ C ⟶ I} {iI : I ⟶ I}

/-- The multiplication of a subobject, read on generalized elements. -/
lemma sub_lift_comp (hmul : mI ≫ m = (m ⊗ₘ m) ≫ μ) {T : C} (x y : T ⟶ I) :
    (lift x y ≫ mI) ≫ m = (x ≫ m) * (y ≫ m) := by
  rw [Category.assoc, hmul, Hom.mul_def, ← Category.assoc, lift_map]

variable [Mono m]

/-- A subobject of a group object closed under the multiplication and the unit is a monoid
object. -/
@[instance_reducible]
def subMonObj (hmul : mI ≫ m = (m ⊗ₘ m) ≫ μ) (hone : oI ≫ m = η) : MonObj I where
  one := oI
  mul := mI
  one_mul := by
    rw [← cancel_mono m, show oI ▷ I = lift (fst _ I ≫ oI) (snd _ I) by
      rw [← tensorHom_id, ← lift_fst_comp_snd_comp]; simp, sub_lift_comp hmul, Category.assoc,
      hone, leftUnitor_hom]
    rw [show (fst (𝟙_ C) I ≫ (η : 𝟙_ C ⟶ B)) = 1 by
      rw [Hom.one_def, SemiCartesianMonoidalCategory.toUnit_unique (fst (𝟙_ C) I) (toUnit _)],
      one_mul]
  mul_one := by
    rw [← cancel_mono m, show I ◁ oI = lift (fst I _) (snd I _ ≫ oI) by
      rw [← id_tensorHom, ← lift_fst_comp_snd_comp]; simp, sub_lift_comp hmul, Category.assoc,
      hone, rightUnitor_hom]
    rw [show (snd I (𝟙_ C) ≫ (η : 𝟙_ C ⟶ B)) = 1 by
      rw [Hom.one_def, SemiCartesianMonoidalCategory.toUnit_unique (snd I (𝟙_ C)) (toUnit _)],
      mul_one]
  mul_assoc := by
    have e1 : mI ▷ I = lift (fst _ I ≫ mI) (snd _ I) := by
      rw [← tensorHom_id, ← lift_fst_comp_snd_comp]; simp
    have e2 : I ◁ mI = lift (fst I _) (snd I _ ≫ mI) := by
      rw [← id_tensorHom, ← lift_fst_comp_snd_comp]; simp
    have hα1 : (α_ I I I).hom ≫ fst I (I ⊗ I) = fst (I ⊗ I) I ≫ fst I I := by simp
    have hα2 : (α_ I I I).hom ≫ snd I (I ⊗ I) =
        lift (fst (I ⊗ I) I ≫ snd I I) (snd (I ⊗ I) I) := by
      apply hom_ext <;> simp
    have h3 : (fst (I ⊗ I) I ≫ mI) ≫ m =
        (fst (I ⊗ I) I ≫ fst I I ≫ m) * (fst (I ⊗ I) I ≫ snd I I ≫ m) := by
      rw [show fst (I ⊗ I) I = lift (fst (I ⊗ I) I ≫ fst I I) (fst (I ⊗ I) I ≫ snd I I) from by
        apply hom_ext <;> simp, sub_lift_comp hmul]
      simp
    rw [← cancel_mono m, e1, e2, sub_lift_comp hmul, h3, ← Category.assoc (α_ I I I).hom,
      comp_lift, hα1, ← Category.assoc (α_ I I I).hom (snd I (I ⊗ I)) mI, hα2,
      sub_lift_comp hmul, sub_lift_comp hmul, mul_assoc]
    simp

/-- The multiplication of `subMonObj` is `mI`. -/
lemma subMonObj_mul (hmul : mI ≫ m = (m ⊗ₘ m) ≫ μ) (hone : oI ≫ m = η) :
    (subMonObj hmul hone).mul = mI := rfl

/-- The unit of `subMonObj` is `oI`. -/
lemma subMonObj_one (hmul : mI ≫ m = (m ⊗ₘ m) ≫ μ) (hone : oI ≫ m = η) :
    (subMonObj hmul hone).one = oI := rfl

/-- A subobject of a group object closed under the operations is a group object. -/
@[instance_reducible]
def subGrpObj (hmul : mI ≫ m = (m ⊗ₘ m) ≫ μ) (hone : oI ≫ m = η) (hinv : iI ≫ m = m ≫ ι) :
    @GrpObj C _ _ I :=
  letI := subMonObj hmul hone
  { inv := iI
    left_inv := by
      rw [subMonObj_mul, subMonObj_one, ← cancel_mono m, sub_lift_comp hmul, hinv,
        Category.assoc, hone, Category.id_comp, ← Hom.inv_def, ← Hom.one_def, inv_mul_cancel]
    right_inv := by
      rw [subMonObj_mul, subMonObj_one, ← cancel_mono m, sub_lift_comp hmul, hinv,
        Category.assoc, hone, Category.id_comp, ← Hom.inv_def, ← Hom.one_def, mul_inv_cancel] }

/-- The inclusion of a subobject closed under the operations is a morphism of monoid
objects. -/
lemma isMonHom_sub (hmul : mI ≫ m = (m ⊗ₘ m) ≫ μ) (hone : oI ≫ m = η) :
    letI := subMonObj hmul hone
    IsMonHom m :=
  letI := subMonObj hmul hone
  { one_hom := hone
    mul_hom := hmul }

end SubGrp

end UlmerBialgebras
