module

public import Mathlib.CategoryTheory.Monoidal.Internal.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Equalizers of monoid objects

In any monoidal category, the equalizer of a pair of morphisms of monoid objects carries a
unique monoid structure making the inclusion a morphism of monoid objects, and the resulting
fork is a limit in `Mon C`.  Unlike the dual statement for
coequalizers (`Foundations/CategoryTheory/Monoidal/MonObjReflexiveCoeq.lean`), no hypothesis on the
tensor
product is needed: the multiplication of the equalizer is obtained from the universal property, not
from a preservation property. The structure comes from Mathlib’s limit construction; its operations
agree with the equalizer lifts described below.

## Main results

* `CategoryTheory.MonEqualizer.monObj`: the monoid structure on an equalizer of monoid morphisms;
* `CategoryTheory.MonEqualizer.isMonHom_e`: the inclusion is a morphism of monoid objects;
* `CategoryTheory.MonEqualizer.isMonHom_liftMon`: the universal property is one of monoid objects.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.11
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj

section

namespace CategoryTheory.MonEqualizer

variable {C : Type u} [Category.{v} C]

variable {M N E : C} {u v : M ⟶ N} {e : E ⟶ M} {w : e ≫ u = e ≫ v}
  (he : IsLimit (Fork.ofι e w))

include he

/-- The inclusion `e` of an equalizer is a monomorphism. -/
lemma mono_e : Mono e := Fork.IsLimit.mono he

variable [MonoidalCategory C] [MonObj M] [MonObj N] [IsMonHom u] [IsMonHom v]

/-- The unit of the equalizer of two morphisms of monoid objects. -/
noncomputable def one : 𝟙_ C ⟶ E :=
  Fork.IsLimit.lift he η[M] (by rw [IsMonHom.one_hom, IsMonHom.one_hom])

/-- The unit of the equalizer satisfies `one he ≫ e = η[M]`. -/
@[reassoc (attr := simp)]
lemma one_comp : one he ≫ e = η[M] := Fork.IsLimit.lift_ι' he _ _

/-- The multiplication of the equalizer of two morphisms of monoid objects. -/
noncomputable def mul : E ⊗ E ⟶ E :=
  Fork.IsLimit.lift he ((e ⊗ₘ e) ≫ μ[M]) (by
    rw [Category.assoc, Category.assoc, IsMonHom.mul_hom u, IsMonHom.mul_hom v,
      ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, w])

/-- The multiplication of the equalizer satisfies `mul he ≫ e = (e ⊗ₘ e) ≫ μ[M]`. -/
@[reassoc (attr := simp)]
lemma mul_comp : mul he ≫ e = (e ⊗ₘ e) ≫ μ[M] := Fork.IsLimit.lift_ι' he _ _

/-- The monoid structure on the equalizer, from Mathlib's limit construction. -/
@[instance_reducible]
noncomputable def monObj : MonObj E := by
  let F : WalkingParallelPair ⥤ Mon C :=
    parallelPair (show Mon.mk M ⟶ Mon.mk N from ⟨u⟩) (show Mon.mk M ⟶ Mon.mk N from ⟨v⟩)
  let i : F ⋙ Mon.forget C ≅ parallelPair u v := diagramIsoParallelPair _
  let c : Cone (F ⋙ Mon.forget C) := (Cone.postcompose i.inv).obj (Fork.ofι e w)
  let hc : IsLimit c := (IsLimit.postcomposeInvEquiv i (Fork.ofι e w)).symm he
  exact (Mon.limit F c hc).mon

/-- The inclusion of the equalizer is a morphism of monoid objects. -/
lemma isMonHom_e : letI := monObj he; IsMonHom e := by
  let F : WalkingParallelPair ⥤ Mon C :=
    parallelPair (show Mon.mk M ⟶ Mon.mk N from ⟨u⟩) (show Mon.mk M ⟶ Mon.mk N from ⟨v⟩)
  let i : F ⋙ Mon.forget C ≅ parallelPair u v := diagramIsoParallelPair _
  let c : Cone (F ⋙ Mon.forget C) := (Cone.postcompose i.inv).obj (Fork.ofι e w)
  let hc : IsLimit c := (IsLimit.postcomposeInvEquiv i (Fork.ofι e w)).symm he
  let h := (Mon.limitCone F c hc).π.app WalkingParallelPair.zero
  have hh : h.hom = e := by
    change c.π.app WalkingParallelPair.zero = e
    simp only [diagramIsoParallelPair, Functor.comp_obj, parallelPair_obj_zero,
      parallelPair_obj_one, Functor.comp_map, parallelPair_map_left, parallelPair_map_right,
      Cone.postcompose, Fork.ofι_pt, Functor.const_obj_obj, NatTrans.comp_app, Fork.ofι_π_app, F,
      c, i]
    exact Category.comp_id e
  have hhmon := h.isMonHom_hom
  rw [hh] at hhmon
  exact hhmon

/-- The unit from the limit construction is the equalizer lift of the unit. -/
lemma monObj_one : letI := monObj he; η[E] = one he := by
  let _ : MonObj E := monObj he
  have := isMonHom_e he
  have := mono_e he
  apply (cancel_mono e).1
  rw [IsMonHom.one_hom, one_comp]

/-- The multiplication from the limit construction is the equalizer lift of multiplication. -/
lemma monObj_mul : letI := monObj he; μ[E] = mul he := by
  let _ : MonObj E := monObj he
  have := isMonHom_e he
  have := mono_e he
  apply (cancel_mono e).1
  rw [IsMonHom.mul_hom, mul_comp]

section Lift

variable {Z : C} [MonObj Z] (h : Z ⟶ M) [IsMonHom h] (hh : h ≫ u = h ≫ v)

/-- The morphism induced into the equalizer by a morphism of monoid objects equalizing the
pair. -/
noncomputable def liftMon : Z ⟶ E := Fork.IsLimit.lift he h hh

omit [MonoidalCategory C] [MonObj M] [MonObj N] [IsMonHom u] [IsMonHom v] [MonObj Z] [IsMonHom h] in
/-- The induced morphism satisfies `liftMon he h hh ≫ e = h`. -/
@[reassoc (attr := simp)]
lemma liftMon_comp : liftMon he h hh ≫ e = h := Fork.IsLimit.lift_ι' he h hh

/-- The induced morphism is again a morphism of monoid objects. -/
lemma isMonHom_liftMon : letI := monObj he; IsMonHom (liftMon he h hh) :=
  letI := monObj he
  { one_hom := by
      have := mono_e he
      rw [← cancel_mono e, Category.assoc]
      rw [monObj_one he]
      rw [liftMon_comp he, one_comp he, IsMonHom.one_hom]
    mul_hom := by
      have := mono_e he
      rw [← cancel_mono e, Category.assoc, Category.assoc]
      rw [monObj_mul he]
      rw [liftMon_comp he, mul_comp he, ← Category.assoc, tensorHom_comp_tensorHom,
        liftMon_comp he, IsMonHom.mul_hom] }

end Lift

end CategoryTheory.MonEqualizer

end
