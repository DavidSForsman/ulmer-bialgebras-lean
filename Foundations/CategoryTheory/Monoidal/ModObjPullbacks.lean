module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import Foundations.CategoryTheory.Monoidal.ModObjFree

/-!
# Pullbacks of module objects

Let `C` be a monoidal category, `A` a monoid object of `C` and `M, N, L` module objects over `A`.
This file shows that the pullback in `C` of two morphisms of module objects carries a module
structure, and that the resulting cone is a limit cone in the category
`CategoryTheory.Mod C A` of `A`-module objects.

The module structure on the pullback `P` is induced by the universal property of the pullback:
the action map `A ⊗ P ⟶ P` is the pairing of the two actions on `M` and `L`, which agree over
`N` because the two given maps are morphisms of module objects.  Nothing is assumed about the
tensor product beyond the monoidal structure, so in particular no preservation of limits by
tensoring is needed: maps *into* a limit are built from maps into its components.

## Main results

* `CategoryTheory.Mod_.pullbackModObj`: the module structure on the pullback of two module maps;
* `CategoryTheory.Mod_.pullbackObj`, `pullbackFst`, `pullbackSnd`: the pullback of two module
  maps as a module and its two projections;
* `CategoryTheory.Mod_.pullbackConeIsLimit`: the pullback cone is a limit cone;
* `CategoryTheory.Mod_.hasPullbacks`: `Mod C A` has pullbacks when `C` does.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Section VII.4
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped MonoidalLeftAction ModObj

namespace CategoryTheory

namespace Mod_

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] {A : C} [MonObj A]
variable {M N L : C} [ModObj A M] [ModObj A N] [ModObj A L]

/-- The action map on the pullback of two morphisms of module objects: the pairing of the two
actions, which agree after the two given maps. -/
noncomputable def pullbackSmul (f : M ⟶ N) (g : L ⟶ N) [IsModHom A f] [IsModHom A g]
    [HasPullback f g] : A ⊗ pullback f g ⟶ pullback f g :=
  pullback.lift (A ◁ pullback.fst f g ≫ γ[A, M]) (A ◁ pullback.snd f g ≫ γ[A, L]) (by
    rw [Category.assoc, Category.assoc, IsModHom.smul_hom, IsModHom.smul_hom]
    simp only [selfLeftAction_actionHomRight]
    rw [← Category.assoc, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp A (pullback.fst f g) f,
      ← MonoidalCategory.whiskerLeft_comp A (pullback.snd f g) g, pullback.condition])

/-- The defining property of the action on the pullback, against the first projection. -/
lemma pullbackSmul_fst (f : M ⟶ N) (g : L ⟶ N) [IsModHom A f] [IsModHom A g]
    [HasPullback f g] :
    pullbackSmul f g ≫ pullback.fst f g = A ◁ pullback.fst f g ≫ γ[A, M] :=
  pullback.lift_fst _ _ _

/-- The defining property of the action on the pullback, against the second projection. -/
lemma pullbackSmul_snd (f : M ⟶ N) (g : L ⟶ N) [IsModHom A f] [IsModHom A g]
    [HasPullback f g] :
    pullbackSmul f g ≫ pullback.snd f g = A ◁ pullback.snd f g ≫ γ[A, L] :=
  pullback.lift_snd _ _ _

/-- A morphism `p : P ⟶ M` into a module object intertwining a map `s : A ⊗ P ⟶ P` with the
action of `M` sees `s` as compatible with the multiplication of `A`. -/
lemma mul_smul_comp_of_smul_comp {P : C} (s : A ⊗ P ⟶ P) (p : P ⟶ M)
    (hs : s ≫ p = A ◁ p ≫ γ[A,M]) :
    (μ : A ⊗ A ⟶ A) ▷ P ≫ s ≫ p = (α_ A A P).hom ≫ A ◁ s ≫ s ≫ p := by
  rw [hs, ← whisker_exchange_assoc, ModObj.mul_smul_self, ← whiskerLeft_comp_assoc, hs]
  simp only [whiskerLeft_comp, Category.assoc, associator_naturality_right_assoc]

/-- The pullback of two morphisms of module objects carries a module structure. -/
@[instance_reducible]
noncomputable def pullbackModObj (f : M ⟶ N) (g : L ⟶ N) [IsModHom A f] [IsModHom A g]
    [HasPullback f g] : ModObj A (pullback f g) where
  smul := pullbackSmul f g
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSmul_fst]
      have hone : (η : 𝟙_ C ⟶ A) ▷ M ≫ γ[A, M] = (λ_ M).hom := CategoryTheory.one_smul' ⟨M⟩
      rw [← Category.assoc, ← whisker_exchange, Category.assoc, hone, leftUnitor_naturality]
    · simp only [Category.assoc, pullbackSmul_snd]
      have hone : (η : 𝟙_ C ⟶ A) ▷ L ≫ γ[A, L] = (λ_ L).hom := CategoryTheory.one_smul' ⟨L⟩
      rw [← Category.assoc, ← whisker_exchange, Category.assoc, hone, leftUnitor_naturality]
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      exact mul_smul_comp_of_smul_comp _ _ (pullbackSmul_fst f g)
    · simp only [Category.assoc]
      exact mul_smul_comp_of_smul_comp _ _ (pullbackSmul_snd f g)

section Cone

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable {A : C} [MonObj A] {X Y Z : Mod C A}

/-- The pullback of two morphisms of module objects, as a module object. -/
noncomputable abbrev pullbackObj (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] : Mod C A :=
  letI := pullbackModObj (A := A) f.hom g.hom
  ⟨pullback f.hom g.hom⟩

/-- The first projection of the pullback of two morphisms of module objects. -/
noncomputable def pullbackFst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    pullbackObj (A := A) f g ⟶ X :=
  letI := pullbackModObj (A := A) f.hom g.hom
  Mod.Hom.mk'' (pullback.fst f.hom g.hom) (pullbackSmul_fst f.hom g.hom)

/-- The second projection of the pullback of two morphisms of module objects. -/
noncomputable def pullbackSnd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    pullbackObj (A := A) f g ⟶ Y :=
  letI := pullbackModObj (A := A) f.hom g.hom
  Mod.Hom.mk'' (pullback.snd f.hom g.hom) (pullbackSmul_snd f.hom g.hom)

/-- The underlying morphism of `pullbackFst`. -/
@[simp]
lemma pullbackFst_hom (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    (pullbackFst (A := A) f g).hom = pullback.fst f.hom g.hom := rfl

/-- The underlying morphism of `pullbackSnd`. -/
@[simp]
lemma pullbackSnd_hom (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    (pullbackSnd (A := A) f g).hom = pullback.snd f.hom g.hom := rfl

/-- The pullback cone of two morphisms of module objects. -/
noncomputable def pullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    PullbackCone f g :=
  PullbackCone.mk (pullbackFst (A := A) f g) (pullbackSnd (A := A) f g) (by
    ext
    exact pullback.condition)

/-- The pullback cone of two morphisms of module objects is a limit cone. -/
noncomputable def pullbackConeIsLimit (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    IsLimit (pullbackCone (A := A) f g) := by
  letI := pullbackModObj (A := A) f.hom g.hom
  refine PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h₁ h₂ => ?_)
  · refine Mod.Hom.mk'' (pullback.lift s.fst.hom s.snd.hom (congr(($(s.condition)).hom)))
      ?_
    have hlift : pullback.lift s.fst.hom s.snd.hom (congr(($(s.condition)).hom)) ≫
        pullback.fst f.hom g.hom = s.fst.hom := pullback.lift_fst _ _ _
    have hlifts : pullback.lift s.fst.hom s.snd.hom (congr(($(s.condition)).hom)) ≫
        pullback.snd f.hom g.hom = s.snd.hom := pullback.lift_snd _ _ _
    have hsm₁ : γ[A, pullback f.hom g.hom] ≫ pullback.fst f.hom g.hom =
        A ⊴ₗ pullback.fst f.hom g.hom ≫ γ[A, X.X] := pullbackSmul_fst _ _
    have hsm₂ : γ[A, pullback f.hom g.hom] ≫ pullback.snd f.hom g.hom =
        A ⊴ₗ pullback.snd f.hom g.hom ≫ γ[A, Y.X] := pullbackSmul_snd _ _
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hlift, hsm₁, ← Category.assoc,
        ← MonoidalLeftAction.actionHomRight_comp, hlift]
      exact IsModHom.smul_hom
    · rw [Category.assoc, Category.assoc, hlifts, hsm₂, ← Category.assoc,
        ← MonoidalLeftAction.actionHomRight_comp, hlifts]
      exact IsModHom.smul_hom
  · ext
    exact pullback.lift_fst _ _ _
  · ext
    exact pullback.lift_snd _ _ _
  · apply Mod.hom_ext
    apply pullback.hom_ext
    · have h₁' := congr(($(h₁)).hom)
      simp only [Mod.comp_hom', pullbackFst_hom] at h₁'
      exact h₁'.trans (pullback.lift_fst _ _ _).symm
    · have h₂' := congr(($(h₂)).hom)
      simp only [Mod.comp_hom', pullbackSnd_hom] at h₂'
      exact h₂'.trans (pullback.lift_snd _ _ _).symm

end Cone

section Instances

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable {A : C} [MonObj A] {X Y Z : Mod C A}

/-- The pullback of two morphisms of module objects, as a limit. -/
noncomputable instance hasPullback (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f.hom g.hom] :
    HasPullback f g :=
  ⟨_, pullbackConeIsLimit (A := A) f g⟩

/-- **The category of module objects has pullbacks when the ambient category does.** -/
noncomputable instance hasPullbacks [HasPullbacks C] : HasPullbacks (Mod C A) :=
  hasPullbacks_of_hasLimit_cospan (Mod C A)

end Instances

end Mod_

end CategoryTheory
