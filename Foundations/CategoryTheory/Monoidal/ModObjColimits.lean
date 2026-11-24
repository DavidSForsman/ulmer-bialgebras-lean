module

public import Foundations.CategoryTheory.Monoidal.ModObjFree
public import Foundations.CategoryTheory.Limits.ReflexivePairMap
public import Foundations.CategoryTheory.Limits.PreservesReflexiveCoeq

/-!
# Colimits in categories of module objects

Let `A` be a monoid object of a monoidal category `C`.  In contrast with limits (see
`Foundations/CategoryTheory/Monoidal/ModObjLimits.lean`), the forgetful functor
`Mod_.forget A` only creates those colimits which are preserved by the functors `Z ⊗ -`.  This
is exactly the situation for *reflexive coequalizers* in the applications, where one assumes
that tensoring preserves reflexive coequalizers.

## Main results

* `CategoryTheory.Mod_.createsColimitForget`: `Mod_.forget A` creates a colimit that is preserved by
  all the functors `tensorLeft Z`;
* `CategoryTheory.Mod_.hasReflexiveCoequalizers`: categories of module objects have reflexive
  coequalizers when the ambient category does and tensoring preserves them;
* `CategoryTheory.Mod_.preservesReflexiveCoequalizers_forget`: the forgetful functor preserves
  reflexive coequalizers.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Section VII.4
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.13
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory MonoidalCategory MonObj Limits
open scoped MonoidalLeftAction ModObj Obj

namespace CategoryTheory

namespace Mod_

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] {A : C} [MonObj A]

/-- `(tensorLeft Z).map f` is the whiskering `Z ◁ f`. -/
lemma tensorLeft_map_eq (Z : C) {X Y : C} (f : X ⟶ Y) : (tensorLeft Z).map f = Z ◁ f := rfl

section

variable {J : Type*} [Category J] (K : J ⥤ CategoryTheory.Mod C A)
  (c : Cocone (K ⋙ CategoryTheory.Mod.forget A))

/-- The cocone over `(K ⋙ forget) ⋙ tensorLeft A` used to define the action on a colimit. -/
def actCocone : Cocone ((K ⋙ CategoryTheory.Mod.forget A) ⋙ tensorLeft A) :=
  Cocone.mk c.pt
    { app := fun j => γ[A, (K.obj j).X] ≫ c.ι.app j
      naturality := by
        intro j j' α
        have h : γ[A, (K.obj j).X] ≫ (K.map α).hom = A ◁ (K.map α).hom ≫ γ[A, (K.obj j').X] := by
          simp
        have hc : (K.map α).hom ≫ c.ι.app j' = c.ι.app j :=
          (c.ι.naturality α).trans (Category.comp_id _)
        exact ((Category.assoc _ _ _).symm.trans (h.symm =≫ c.ι.app j')).trans
          (((Category.assoc _ _ _).trans (γ[A, (K.obj j).X] ≫= hc)).trans
            (Category.comp_id _).symm) }

/-- The legs of `actCocone K c` are `γ[A, (K.obj j).X] ≫ c.ι.app j`. -/
@[simp]
lemma actCocone_app (j : J) :
    (actCocone K c).ι.app j = γ[A, (K.obj j).X] ≫ c.ι.app j := rfl

/-- The point of `actCocone K c` is `c.pt`. -/
@[simp]
lemma actCocone_pt : (actCocone K c).pt = c.pt := rfl

/-- The leg of `c` at `j`, as a map `(K.obj j).X ⟶ c.pt`. -/
def leg (j : J) : (K.obj j).X ⟶ c.pt := c.ι.app j

/-- The map out of the colimit `c.pt` induced by a cocone `s` over `K`. -/
noncomputable def descX (hc0 : IsColimit c) (s : Cocone K) : c.pt ⟶ s.pt.X :=
  hc0.desc ((CategoryTheory.Mod.forget A).mapCocone s)

/-- `descX` restricts to the legs of `s`. -/
@[reassoc]
lemma leg_descX (hc0 : IsColimit c) (s : Cocone K) (j : J) :
    leg K c j ≫ descX K c hc0 s = (s.ι.app j).hom :=
  hc0.fac ((CategoryTheory.Mod.forget A).mapCocone s) j

variable (hc : ∀ Z : C, IsColimit ((tensorLeft Z).mapCocone c))

include hc

/-- The action on the point of `c`, induced by the colimit `A ⊗ c.pt`. -/
noncomputable def actDesc : A ⊗ c.pt ⟶ c.pt := (hc A).desc (actCocone K c)

/-- `actDesc` restricts to `γ[A, (K.obj j).X] ≫ leg K c j` along `A ◁ leg K c j`. -/
@[reassoc]
lemma ι_actDesc (j : J) :
    A ◁ leg K c j ≫ actDesc K c hc = γ[A, (K.obj j).X] ≫ leg K c j :=
  (hc A).fac (actCocone K c) j

/-- If `Z ⊗ -` preserves the colimit `c` (`hc`), maps out of `Z ⊗ c.pt` agree if they agree
after each `Z ◁ leg K c j`. -/
lemma tensor_hom_ext (Z : C) {W : C} {f g : Z ⊗ c.pt ⟶ W}
    (h : ∀ j, Z ◁ leg K c j ≫ f = Z ◁ leg K c j ≫ g) : f = g :=
  (hc Z).hom_ext h

/-- The point of a colimit cocone over `K ⋙ forget` carries a canonical `A`-module structure,
provided the colimit is preserved by tensoring. -/
@[instance_reducible, simps]
noncomputable def colimitModObj : ModObj A c.pt where
  smul := actDesc K c hc
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    refine tensor_hom_ext K c hc (𝟙_ C) fun j => ?_
    rw [whisker_exchange_assoc, ι_actDesc, ← Category.assoc]
    have h : (η : 𝟙_ C ⟶ A) ▷ (K.obj j).X ≫ γ[A, (K.obj j).X] = (λ_ (K.obj j).X).hom := by
      simp
    exact (h =≫ leg K c j).trans (leftUnitor_naturality _).symm
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso]
    refine tensor_hom_ext K c hc (A ⊗ A) fun j => ?_
    have h : (μ : A ⊗ A ⟶ A) ▷ (K.obj j).X ≫ γ[A, (K.obj j).X]
        = (α_ A A (K.obj j).X).hom ≫ A ◁ γ[A, (K.obj j).X] ≫ γ[A, (K.obj j).X] := by
      simp
    rw [whisker_exchange_assoc, ι_actDesc, associator_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ι_actDesc,
      MonoidalCategory.whiskerLeft_comp_assoc, ι_actDesc, ← Category.assoc, h]
    simp only [Category.assoc]

/-- The lift of a colimit cocone over `K ⋙ forget` to a cocone over `K`. -/
noncomputable def liftedCocone : Cocone K :=
  letI := colimitModObj K c hc
  Cocone.mk ⟨c.pt⟩
    { app := fun j => CategoryTheory.Mod.Hom.mk' (c.ι.app j) (ι_actDesc K c hc j).symm
      naturality := by
        intro j j' α
        ext
        exact c.ι.naturality α }

/-- The underlying morphisms of the legs of `liftedCocone K c hc` are the legs of `c`. -/
@[simp]
lemma liftedCocone_app (j : J) : ((liftedCocone K c hc).ι.app j).hom = c.ι.app j := rfl

/-- The lifted cocone is a colimit cocone. -/
noncomputable def liftedCoconeIsColimit (hc0 : IsColimit c) :
    IsColimit (liftedCocone K c hc) where
  desc s :=
    letI := colimitModObj K c hc
    CategoryTheory.Mod.Hom.mk' (descX K c hc0 s) (by
      change actDesc K c hc ≫ descX K c hc0 s = A ◁ descX K c hc0 s ≫ γ[A, s.pt.X]
      refine tensor_hom_ext K c hc A fun j => ?_
      rw [ι_actDesc_assoc, leg_descX, ← MonoidalCategory.whiskerLeft_comp_assoc, leg_descX]
      exact IsModHom.smul_hom (f := (s.ι.app j).hom))
  fac s j := by
    ext
    exact leg_descX K c hc0 s j
  uniq s m hm := by
    ext
    exact hc0.uniq ((CategoryTheory.Mod.forget A).mapCocone s) m.hom fun j =>
      congr(($(hm j)).hom)

/-- **The forgetful functor creates those colimits that are preserved by tensoring.** -/
@[instance_reducible]
noncomputable def createsColimitForget
    (hpres : ∀ Z : C, PreservesColimit (K ⋙ CategoryTheory.Mod.forget A) (tensorLeft Z)) :
    CreatesColimit K (CategoryTheory.Mod.forget A) :=
  createsColimitOfReflectsIso fun c t =>
    letI hcol : ∀ Z : C, IsColimit ((tensorLeft Z).mapCocone c) := fun Z => by
      haveI := hpres Z
      exact isColimitOfPreserves (tensorLeft Z) t
    { liftedCocone := liftedCocone K c hcol
      validLift := Cocone.ext (Iso.refl _) fun _ => Category.comp_id _
      makesColimit := liftedCoconeIsColimit K c hcol t }

end

section Reflexive

private lemma preservesColimit_parallelPair_tensorLeft
    (htens : ∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)) {X Y : CategoryTheory.Mod C A}
    (u v : X ⟶ Y) (huv : IsReflexivePair u v) (Z : C) :
    PreservesColimit (parallelPair u v ⋙ CategoryTheory.Mod.forget A) (tensorLeft Z) := by
  have := (htens Z).preserves _ _ (isReflexivePair_map (CategoryTheory.Mod.forget A) huv)
  exact preservesColimit_of_iso_diagram (tensorLeft Z)
    (CategoryTheory.parallelPairComp (CategoryTheory.Mod.forget A) u v).symm

variable [HasReflexiveCoequalizers C]

private lemma hasColimit_comp_forget {X Y : CategoryTheory.Mod C A}
    (u v : X ⟶ Y) (huv : IsReflexivePair u v) :
    HasColimit (parallelPair u v ⋙ CategoryTheory.Mod.forget A) := by
  have : IsReflexivePair ((CategoryTheory.Mod.forget A).map u)
      ((CategoryTheory.Mod.forget A).map v) :=
    isReflexivePair_map (CategoryTheory.Mod.forget A) huv
  have : HasColimit (parallelPair ((CategoryTheory.Mod.forget A).map u)
      ((CategoryTheory.Mod.forget A).map v)) := HasReflexiveCoequalizers.has_coeq _ _
  exact hasColimit_of_iso (CategoryTheory.parallelPairComp (CategoryTheory.Mod.forget A) u v)

variable (htens : ∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z))

include htens

/-- Categories of module objects have reflexive coequalizers as soon as the ambient category
does and tensoring preserves them. -/
theorem hasReflexiveCoequalizers : HasReflexiveCoequalizers (CategoryTheory.Mod C A) where
  has_coeq {X Y} u v huv := by
    have := createsColimitForget (parallelPair u v)
      (preservesColimit_parallelPair_tensorLeft htens u v huv)
    have := hasColimit_comp_forget u v huv
    exact hasColimit_of_created (parallelPair u v) (CategoryTheory.Mod.forget A)

/-- The forgetful functor preserves reflexive coequalizers. -/
theorem preservesReflexiveCoequalizers_forget :
    PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) A) := by
  refine ⟨fun X Y u v huv => ?_⟩
  have := createsColimitForget (parallelPair u v)
    (preservesColimit_parallelPair_tensorLeft htens u v huv)
  have := hasColimit_comp_forget u v huv
  have : HasColimit (parallelPair u v) :=
    hasColimit_of_created (parallelPair u v) (CategoryTheory.Mod.forget A)
  exact preservesColimit_of_createsColimit_and_hasColimit _ _

end Reflexive

end Mod_

end CategoryTheory
