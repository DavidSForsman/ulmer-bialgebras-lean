module

public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.Tactic.CategoryTheory.Coherence
public import Foundations.CategoryTheory.Monoidal.ModObjLimits

/-!
# Free module objects

For a monoid object `A` in a monoidal category `C`, the object `A ⊗ X` is naturally an `A`-module,
and the resulting functor `CategoryTheory.freeMod A : C ⥤ Mod_ C A` is left adjoint to the forgetful
functor.

## Main results

* `CategoryTheory.freeMod`: the free `A`-module functor `X ↦ A ⊗ X`;
* `CategoryTheory.freeModAdj`: the free-forgetful adjunction for module objects.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Section VII.4
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory MonoidalCategory MonObj Limits
open scoped MonoidalLeftAction ModObj Obj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] (A : C) [MonObj A]

/-- `A ⊗ X` is an `A`-module. -/
@[instance_reducible, simps]
def freeModObj (X : C) : ModObj A (A ⊗ X) where
  smul := (α_ A A X).inv ≫ (μ : A ⊗ A ⟶ A) ▷ X
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    simp [← comp_whiskerRight]
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.mul_assoc]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_middle_assoc]
    have h : (α_ (A ⊗ A) A X).inv ≫ (α_ A A A).hom ▷ X =
        (α_ A A (A ⊗ X)).hom ≫ A ◁ (α_ A A X).inv ≫ (α_ A (A ⊗ A) X).inv := by monoidal
    rw [reassoc_of% h]

/-- **The free `A`-module functor.** -/
@[simps, implicit_reducible]
def freeMod : C ⥤ CategoryTheory.Mod C A where
  obj X := letI := freeModObj A X; ⟨A ⊗ X⟩
  map {X Y} g :=
    letI := freeModObj A X
    letI := freeModObj A Y
    CategoryTheory.Mod.Hom.mk'' (A ◁ g) (by
      simp only [freeModObj_smul, selfLeftAction_actionHomRight, Category.assoc,
        associator_inv_naturality_right_assoc, whisker_exchange])
  map_id X := by ext; simp
  map_comp g h := by ext; simp

variable {A}

/-- Associativity of the action, in the form used below. -/
lemma smul_assoc_flip (M : CategoryTheory.Mod C A) :
    A ◁ γ[A, M.X] ≫ γ[A, M.X]
      = (α_ A A M.X).inv ≫ (μ : A ⊗ A ⟶ A) ▷ M.X ≫ γ[A, M.X] := by
  simp

/-- The unit of the action, in the form used below. -/
lemma one_smul' (M : CategoryTheory.Mod C A) :
    (η : 𝟙_ C ⟶ A) ▷ M.X ≫ γ[A, M.X] = (λ_ M.X).hom := by
  simp

variable (A)

/-- **The free-forgetful adjunction for module objects.** -/
def freeModAdj : freeMod A ⊣ CategoryTheory.Mod.forget A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M =>
        { toFun := fun g => (λ_ X).inv ≫ (η : 𝟙_ C ⟶ A) ▷ X ≫ g.hom
          invFun := fun (h : X ⟶ M.X) =>
            letI := freeModObj A X
            CategoryTheory.Mod.Hom.mk'' (A ◁ h ≫ γ[A, M.X]) (by
              simp only [freeModObj_smul, selfLeftAction_actionHomRight, Category.assoc,
                MonoidalCategory.whiskerLeft_comp]
              rw [smul_assoc_flip M, associator_inv_naturality_right_assoc,
                whisker_exchange_assoc])
          left_inv := fun g => by
            ext
            change A ◁ ((λ_ X).inv ≫ (η : 𝟙_ C ⟶ A) ▷ X ≫ g.hom) ≫ γ[A, M.X] = g.hom
            have hg := IsModHom.smul_hom (A := A) (f := g.hom)
            simp only [freeMod_obj_X, freeModObj_smul, selfLeftAction_actionHomRight] at hg
            rw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp,
              Category.assoc, Category.assoc, ← hg, Category.assoc,
              associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, MonObj.mul_one]
            have hco : A ◁ (λ_ X).inv ≫ (α_ A (𝟙_ C) X).inv ≫ (ρ_ A).hom ▷ X
                = 𝟙 (A ⊗ X) := by monoidal
            rw [reassoc_of% hco]
          right_inv := fun (h : X ⟶ M.X) => by
            change (λ_ X).inv ≫ (η : 𝟙_ C ⟶ A) ▷ X ≫
              (A ◁ h ≫ γ[A, M.X]) = h
            rw [← whisker_exchange_assoc]
            simp only [one_smul' M]
            simp }
      homEquiv_naturality_left_symm := by
        intro X X' M g (h : X' ⟶ M.X)
        ext
        exact (MonoidalCategory.whiskerLeft_comp _ _ _ =≫ _).trans (Category.assoc _ _ _)
      homEquiv_naturality_right := by
        intro X M M' g h
        exact ((Category.assoc _ _ _).trans (_ ≫= Category.assoc _ _ _)).symm }

/-- The free-module adjunction sends `h : X ⟶ M.X` to the module morphism `A ⊗ X ⟶ M`
with underlying morphism `A ◁ h ≫ γ[A, M.X]`. -/
@[simp]
lemma freeModAdj_homEquiv_symm_hom {X : C} {M : CategoryTheory.Mod C A}
    (h : X ⟶ M.X) :
    (((freeModAdj A).homEquiv X M).symm h).hom = A ◁ h ≫ γ[A, M.X] := by
  rw [freeModAdj, Adjunction.mkOfHomEquiv_homEquiv]; rfl

end CategoryTheory
