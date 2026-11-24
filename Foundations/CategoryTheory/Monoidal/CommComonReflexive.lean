module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Foundations.CategoryTheory.Grp.GrpTensorReflexive
public import Foundations.CategoryTheory.Monoidal.CocommProducts
public import Foundations.CategoryTheory.Monoidal.ComonColimits
public import Foundations.CategoryTheory.Monoidal.ModObjColimits

/-!
# Reflexive coequalizers of cocommutative comonoids

Let `V` be a symmetric monoidal category.  This file transfers reflexive coequalizers from `V`
to `CategoryTheory.CommComon V`, the category of cocommutative comonoid objects of `V`, at the
weakest hypotheses of the two statements:

* **Existence** needs only `HasReflexiveCoequalizers V`.  Colimits of cocommutative comonoids are
  created by the forgetful functor `forgetV : CommComon V ⥤ V`, and the underlying coequalizer
  of a reflexive pair exists by hypothesis; no tensor-preservation assumption is used.
* **Preservation** by the product with a fixed object needs, in addition, that tensoring in
  either variable preserves the coequalizers of reflexive pairs in `V`.  Since the product of
  cocommutative comonoids is the tensor product of their underlying objects
  (`Foundations/CategoryTheory/Monoidal/CocommProducts.lean`), the product functor on
  `CommComon V` is conjugate, along `forgetV`, to the tensor functor on `V`
  (`tensorLeftForgetIso`), and preservation transfers
  (`CategoryTheory.preservesReflexiveCoeq_of_natIso`).

The resulting instances give reflexive coequalizers in the categories of modules over an internal
monoid of `CommComon V` (`CommComon.hasReflexiveCoequalizers_mod`), which are the action
categories used in Newman's correspondence.

## Main results

* `UlmerBialgebras.CommComon.forgetV` — the forgetful functor `CommComon V ⥤ V`;
* `UlmerBialgebras.CommComon.forgetV_preservesReflexiveCoeq` — it preserves reflexive
  coequalizers;
* `UlmerBialgebras.CommComon.hasReflexiveCoequalizers` — `CommComon V` has reflexive
  coequalizers;
* `UlmerBialgebras.CommComon.prodIsoTensorObj`, `tensorLeftForgetIso` — the product of
  cocommutative comonoids is the tensor product, and the forgetful functor conjugates the two;
* `UlmerBialgebras.CommComon.preservesReflexiveCoeq_tensorLeft`,
  `preservesReflexiveCoeq_tensorRight` — the product with a fixed cocommutative comonoid
  preserves reflexive coequalizers;
* `UlmerBialgebras.CommComon.hasReflexiveCoequalizers_mod` — the category of modules over an
  internal monoid of `CommComon V` has reflexive coequalizers.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped ComonObj

namespace CommComon

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]

/-- The forgetful functor from cocommutative comonoids to the ambient category. -/
abbrev forgetV (V : Type u) [Category.{v} V] [MonoidalCategory.{v} V] [BraidedCategory.{v} V] :
    CategoryTheory.CommComon V ⥤ V :=
  CategoryTheory.CommComon.forget₂Comon V ⋙ CategoryTheory.Comon.forget V

/-- The forgetful functor from cocommutative comonoids to `V` is faithful. -/
instance : (forgetV V).Faithful := by
  unfold forgetV; infer_instance

/-- The forgetful functor from cocommutative comonoids to `V` reflects isomorphisms. -/
instance : (forgetV V).ReflectsIsomorphisms := by
  unfold forgetV; infer_instance

/-! ## Existence of reflexive coequalizers -/

/-- **The forgetful functor `CommComon V ⥤ V` preserves reflexive coequalizers** as soon as `V`
has them: colimits of cocommutative comonoids are created by the forgetful functor and the
underlying coequalizer exists.  No tensor-preservation hypothesis is used. -/
instance forgetV_preservesReflexiveCoeq [HasReflexiveCoequalizers V] :
    CategoryTheory.PreservesReflexiveCoeq (forgetV V) := by
  constructor
  intro X Y u v huv
  have huv' : IsReflexivePair ((forgetV V).map u) ((forgetV V).map v) :=
    isReflexivePair_map (forgetV V) huv
  have := huv'
  have hV : HasColimit (parallelPair ((forgetV V).map u) ((forgetV V).map v)) :=
    HasReflexiveCoequalizers.has_coeq ((forgetV V).map u) ((forgetV V).map v)
  have hV' : HasColimit (parallelPair u v ⋙ forgetV V) :=
    hasColimit_of_iso (parallelPairComp (forgetV V) u v)
  have : HasColimit (CommComon.toComonDiagram (parallelPair u v) ⋙
      CategoryTheory.Comon.forget V) := hV'
  have : CreatesColimit (parallelPair u v) (CategoryTheory.CommComon.forget₂Comon V) :=
    CommComon.createsColimit_forget₂Comon _
  have : HasColimit (parallelPair u v ⋙ CategoryTheory.CommComon.forget₂Comon V) :=
    ⟨_, Comon.colimitCoconeIsColimit (CommComon.toComonDiagram (parallelPair u v))⟩
  have : PreservesColimit (parallelPair u v) (CategoryTheory.CommComon.forget₂Comon V) :=
    CommComon.forget₂Comon_preservesColimit _
  have : PreservesColimit (parallelPair u v ⋙ CategoryTheory.CommComon.forget₂Comon V)
      (CategoryTheory.Comon.forget V) :=
    Comon.forget_preservesColimit _
  exact comp_preservesColimit (CategoryTheory.CommComon.forget₂Comon V)
    (CategoryTheory.Comon.forget V)

/-- **`CommComon V` has reflexive coequalizers** as soon as `V` does.  No tensor-preservation
hypothesis is used: the coequalizer is created by the forgetful functor. -/
noncomputable instance hasReflexiveCoequalizers [HasReflexiveCoequalizers V] :
    HasReflexiveCoequalizers (CategoryTheory.CommComon V) where
  has_coeq {X Y} u v huv := by
    have huv' : IsReflexivePair ((forgetV V).map u) ((forgetV V).map v) :=
      isReflexivePair_map (forgetV V) huv
    have := huv'
    have hV : HasColimit (parallelPair ((forgetV V).map u) ((forgetV V).map v)) :=
      HasReflexiveCoequalizers.has_coeq ((forgetV V).map u) ((forgetV V).map v)
    have hV' : HasColimit (parallelPair u v ⋙ forgetV V) :=
      hasColimit_of_iso (parallelPairComp (forgetV V) u v)
    have : HasColimit (CommComon.toComonDiagram (parallelPair u v) ⋙
        CategoryTheory.Comon.forget V) := hV'
    exact CommComon.hasColimit (F := parallelPair u v)

/-! ## The forgetful functor turns the product into the tensor product -/

section Tensor

variable (A B : CategoryTheory.CommComon V)

/-- The categorical product of two cocommutative comonoids has the tensor product of the
underlying objects as underlying object. -/
noncomputable def prodIsoTensorObj : A ⊗ B ≅ CommComon.tensorObj A B :=
  IsLimit.conePointUniqueUpToIso (tensorProductIsBinaryProduct A B) (binaryFanIsLimit A B)

/-- `(prodIsoTensorObj A B).hom ≫ (binaryFan A B).fst = fst A B`. -/
@[reassoc]
lemma prodIsoTensorObj_hom_fst :
    (prodIsoTensorObj A B).hom ≫ (binaryFan A B).fst = fst A B :=
  IsLimit.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct A B)
    (binaryFanIsLimit A B) ⟨WalkingPair.left⟩

/-- `(prodIsoTensorObj A B).hom ≫ (binaryFan A B).snd = snd A B`. -/
@[reassoc]
lemma prodIsoTensorObj_hom_snd :
    (prodIsoTensorObj A B).hom ≫ (binaryFan A B).snd = snd A B :=
  IsLimit.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct A B)
    (binaryFanIsLimit A B) ⟨WalkingPair.right⟩

end Tensor

/-- Whiskering a morphism of comonoid objects by a comonoid object is a morphism of comonoid
objects. -/
lemma isComonHom_whiskerLeft (A : V) [ComonObj A] {B B' : V} [ComonObj B] [ComonObj B']
    (g : B ⟶ B') [IsComonHom g] : IsComonHom (A ◁ g) := by
  have h : IsComonHom
      ((CategoryTheory.Comon.mk A ◁
        (CategoryTheory.Comon.Hom.mk g :
          CategoryTheory.Comon.mk B ⟶ CategoryTheory.Comon.mk B')).hom) := inferInstance
  exact h

section Naturality

variable {A : CategoryTheory.CommComon V} {B B' : CategoryTheory.CommComon V}

/-- The first projection is natural in the second variable. -/
lemma whiskerLeft_comp_fst (g : B.X ⟶ B'.X) [IsComonHom g] :
    (A.X ◁ g) ≫ CocommComon.fst A.X B'.X = CocommComon.fst A.X B.X := by
  rw [CocommComon.fst, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    IsComonHom.hom_counit]
  rfl

/-- The second projection is natural in the second variable. -/
lemma whiskerLeft_comp_snd (g : B.X ⟶ B'.X) :
    (A.X ◁ g) ≫ CocommComon.snd A.X B'.X = CocommComon.snd A.X B.X ≫ g := by
  rw [CocommComon.snd, ← Category.assoc, whisker_exchange, Category.assoc,
    MonoidalCategory.leftUnitor_naturality, CocommComon.snd, Category.assoc]

end Naturality

/-! ## Preservation of reflexive coequalizers by the product -/

section Preserves

variable (A : CategoryTheory.CommComon V)

/-- Whiskering by a fixed cocommutative comonoid, on tensor products of underlying objects. -/
noncomputable def tensorObjWhiskerLeft {B B' : CategoryTheory.CommComon V} (f : B ⟶ B') :
    CommComon.tensorObj A B ⟶ CommComon.tensorObj A B' :=
  have : IsComonHom f.hom.hom := f.hom.isComonHom_hom
  @CommComon.homMk V _ _ _ (CommComon.tensorObj A B) (CommComon.tensorObj A B')
    (A.X ◁ f.hom.hom) (isComonHom_whiskerLeft A.X f.hom.hom)

/-- `tensorObjWhiskerLeft A f ≫ (binaryFan A B').fst = (binaryFan A B).fst`. -/
@[reassoc]
lemma tensorObjWhiskerLeft_fst {B B' : CategoryTheory.CommComon V} (f : B ⟶ B') :
    tensorObjWhiskerLeft A f ≫ (binaryFan A B').fst = (binaryFan A B).fst := by
  have : IsComonHom f.hom.hom := f.hom.isComonHom_hom
  refine (forgetV V).map_injective ?_
  exact @whiskerLeft_comp_fst _ _ _ _ A B B' f.hom.hom f.hom.isComonHom_hom

/-- `tensorObjWhiskerLeft A f ≫ (binaryFan A B').snd = (binaryFan A B).snd ≫ f`. -/
@[reassoc]
lemma tensorObjWhiskerLeft_snd {B B' : CategoryTheory.CommComon V} (f : B ⟶ B') :
    tensorObjWhiskerLeft A f ≫ (binaryFan A B').snd = (binaryFan A B).snd ≫ f := by
  have : IsComonHom f.hom.hom := f.hom.isComonHom_hom
  refine (forgetV V).map_injective ?_
  exact @whiskerLeft_comp_snd _ _ _ _ A B B' f.hom.hom

/-- The square comparing the product with a fixed cocommutative comonoid, computed in
`CommComon V`, with the tensor product of the underlying objects. -/
lemma prodIsoTensorObj_naturality {B B' : CategoryTheory.CommComon V} (f : B ⟶ B') :
    (A ◁ f) ≫ (prodIsoTensorObj A B').hom
      = (prodIsoTensorObj A B).hom ≫ tensorObjWhiskerLeft A f := by
  have : IsComonHom f.hom.hom := f.hom.isComonHom_hom
  have : IsComonHom (A.X ◁ f.hom.hom) := isComonHom_whiskerLeft A.X f.hom.hom
  refine BinaryFan.IsLimit.hom_ext (binaryFanIsLimit A B') ?_ ?_
  · rw [Category.assoc, Category.assoc, prodIsoTensorObj_hom_fst,
      tensorObjWhiskerLeft_fst, prodIsoTensorObj_hom_fst]
    simp
  · rw [Category.assoc, Category.assoc, prodIsoTensorObj_hom_snd,
      tensorObjWhiskerLeft_snd, ← Category.assoc, prodIsoTensorObj_hom_snd]
    simp

/-- **The forgetful functor turns the product with a fixed cocommutative comonoid into the
tensor product with its underlying object.** -/
noncomputable def tensorLeftForgetIso :
    tensorLeft A ⋙ forgetV V ≅ forgetV V ⋙ tensorLeft A.X :=
  NatIso.ofComponents (fun B => (forgetV V).mapIso (prodIsoTensorObj A B))
    (fun f => congr(($(prodIsoTensorObj_naturality A f)).hom.hom))

variable [HasReflexiveCoequalizers V]
variable [∀ Z : V, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]

/-- **The product with a fixed cocommutative comonoid preserves reflexive coequalizers**, as soon
as the tensor product of the ambient category does. -/
instance preservesReflexiveCoeq_tensorLeft :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft A : CategoryTheory.CommComon V ⥤ _) :=
  CategoryTheory.preservesReflexiveCoeq_of_natIso _ (forgetV V) (tensorLeft A.X)
    (tensorLeftForgetIso A)

/-- **The product with a fixed cocommutative comonoid preserves reflexive coequalizers on the
other side**, by symmetry of the monoidal structure. -/
instance preservesReflexiveCoeq_tensorRight :
    CategoryTheory.PreservesReflexiveCoeq (tensorRight A : CategoryTheory.CommComon V ⥤ _) := by
  constructor
  intro X Y u v huv
  let : BraidedCategory (CategoryTheory.CommComon V) :=
    BraidedCategory.ofCartesianMonoidalCategory
  have : PreservesColimit (parallelPair u v) (tensorLeft A) :=
    CategoryTheory.PreservesReflexiveCoeq.preserves u v huv
  exact preservesColimit_of_natIso (parallelPair u v)
    (BraidedCategory.tensorLeftIsoTensorRight A)

/-- **The product with a fixed cocommutative comonoid preserves colimits indexed by the walking
reflexive pair.** -/
instance preservesColimitsOfShape_walkingReflexivePair_tensorLeft :
    PreservesColimitsOfShape WalkingReflexivePair
      (tensorLeft A : CategoryTheory.CommComon V ⥤ _) :=
  CategoryTheory.preservesColimitsOfShape_walkingReflexivePair_of_preservesReflexiveCoeq _

end Preserves

/-! ## Action categories -/

section Mod

variable [HasReflexiveCoequalizers V]
variable [∀ Z : V, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]

/-- **The category of modules over an internal monoid of `CommComon V` has reflexive
coequalizers**, under the hypotheses that give them in `CommComon V` and make the product
preserve them. -/
noncomputable instance hasReflexiveCoequalizers_mod (A : CategoryTheory.CommComon V) [MonObj A] :
    HasReflexiveCoequalizers (CategoryTheory.Mod (CategoryTheory.CommComon V) A) :=
  CategoryTheory.Mod_.hasReflexiveCoequalizers (A := A) fun _ => inferInstance

end Mod

end CommComon

end UlmerBialgebras
