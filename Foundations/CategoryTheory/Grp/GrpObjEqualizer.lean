module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Foundations.CategoryTheory.Monoidal.MonObjEqualizer
public import Foundations.CategoryTheory.Exact.CoreflexiveTransport

/-!
# Internal group structures on equalizers

An equalizer of internal-group morphisms inherits a group structure, including inversion.

## Main results

* `CategoryTheory.GrpEqualizer.grpObj`: the group structure on the equalizer of two morphisms of
  group objects;
* `CategoryTheory.GrpEqualizer.inv_comp`: its inverse is compatible with the inclusion,
  `inv he ≫ e = e ≫ ι[G]`.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory

section
open CategoryTheory.MonEqualizer

namespace CategoryTheory.GrpEqualizer

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section GrpObj

variable {G H E : C} [GrpObj G] [GrpObj H] {u v : G ⟶ H} [IsMonHom u] [IsMonHom v]
  {e : E ⟶ G} {w : e ≫ u = e ≫ v} (he : IsLimit (Fork.ofι e w))

include he

/-- The inverse of the equalizer of two morphisms of group objects. -/
noncomputable def inv : E ⟶ E :=
  Fork.IsLimit.lift he (e ≫ ι[G]) (by
    rw [Category.assoc, Category.assoc, GrpObj.inv_hom, GrpObj.inv_hom, ← Category.assoc,
      ← Category.assoc, w])

/-- The inverse of the equalizer is compatible with the inclusion: `inv he ≫ e = e ≫ ι[G]`. -/
@[reassoc (attr := simp)]
lemma inv_comp : inv he ≫ e = e ≫ ι[G] := Fork.IsLimit.lift_ι' he _ _

/-- **The group structure on the equalizer of two morphisms of group objects.** -/
@[instance_reducible]
noncomputable def grpObj : GrpObj E :=
  letI := CategoryTheory.MonEqualizer.monObj he
  have hmul : (μ : E ⊗ E ⟶ E) ≫ e = (e ⊗ₘ e) ≫ μ[G] := by
    rw [CategoryTheory.MonEqualizer.monObj_mul he, CategoryTheory.MonEqualizer.mul_comp]
  have hone : (η : 𝟙_ C ⟶ E) ≫ e = η[G] := by
    rw [CategoryTheory.MonEqualizer.monObj_one he, CategoryTheory.MonEqualizer.one_comp]
  haveI := CategoryTheory.MonEqualizer.mono_e he
  { toMonObj := CategoryTheory.MonEqualizer.monObj he
    inv := inv he
    left_inv := by
      rw [← cancel_mono e, Category.assoc, Category.assoc, hmul, hone, ← Category.assoc]
      have h1 : lift (inv he) (𝟙 E) ≫ (e ⊗ₘ e) = e ≫ lift ι[G] (𝟙 G) := by
        apply hom_ext <;> simp
      rw [h1, Category.assoc, GrpObj.left_inv, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    right_inv := by
      rw [← cancel_mono e, Category.assoc, Category.assoc, hmul, hone, ← Category.assoc]
      have h1 : lift (𝟙 E) (inv he) ≫ (e ⊗ₘ e) = e ≫ lift (𝟙 G) ι[G] := by
        apply hom_ext <;> simp
      rw [h1, Category.assoc, GrpObj.right_inv, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _ }

end GrpObj

section CommGrp

variable [BraidedCategory C]

variable {G H : CommGrp C} {u v : G ⟶ H} {E : C} {e : E ⟶ G.X}
  {w : e ≫ u.hom.hom.hom = e ≫ v.hom.hom.hom} (he : IsLimit (Fork.ofι e w))

include he

end CommGrp

section Instances

variable (C)
variable [BraidedCategory C] [HasCoreflexiveEqualizers C]

end Instances

end CategoryTheory.GrpEqualizer

end
