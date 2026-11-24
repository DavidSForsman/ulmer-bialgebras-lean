module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monoidal.CommComon_

/-!
# Colimits of comonoid objects

The forgetful functor `Comon C ⥤ C` **creates colimits**: no exactness or preservation
hypothesis on the tensor product is needed, because the structure morphisms of a comonoid go
*out* of the object, so they can be defined on a colimit by its universal property.  (This is
dual to the fact, already in Mathlib as an instance `HasLimitsOfShape J (Mon C)`, that monoid
objects have all the limits of the ambient category.)

The same holds for **cocommutative** comonoid objects, since cocommutativity of the induced
comultiplication is checked on the colimit injections.

For `C = ModuleCat k` this says that the category `Comon_k` of coalgebras, and its full
subcategory `Comon_k^coc = CommComon (ModuleCat k)` of cocommutative coalgebras, are cocomplete,
with colimits computed on underlying modules.

## Main results

* `UlmerBialgebras.Comon.hasColimitsOfShape` and
  `UlmerBialgebras.Comon.forget_preservesColimitsOfShape`;
* `UlmerBialgebras.CommComon.createsColimit_forget₂Comon` and
  `UlmerBialgebras.CommComon.hasColimitsOfShape`;
* in particular, `CommComon C` has the reflexive coequalizers of `C` (by
  `UlmerBialgebras.CommComon.hasColimitsOfShape`), one of the standing hypotheses of Newman's
  correspondence.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.11
-/

@[expose] public section

universe w w' v u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory
open scoped ComonObj

namespace Comon

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- The forgetful functor of comonoid objects, on objects. -/
@[simp] lemma forget_obj (M : CategoryTheory.Comon C) :
    (CategoryTheory.Comon.forget C).obj M = M.X :=
  rfl

/-- The forgetful functor of comonoid objects, on morphisms. -/
@[simp] lemma forget_map {M N : CategoryTheory.Comon C} (f : M ⟶ N) :
    (CategoryTheory.Comon.forget C).map f = f.hom :=
  rfl

variable (F : J ⥤ CategoryTheory.Comon C)

/-- The diagram of underlying objects, on objects. -/
@[simp] lemma comp_forget_obj (j : J) :
    (F ⋙ CategoryTheory.Comon.forget C).obj j = (F.obj j).X := rfl

/-- The diagram of underlying objects, on morphisms. -/
@[simp] lemma comp_forget_map {j j' : J} (u : j ⟶ j') :
    (F ⋙ CategoryTheory.Comon.forget C).map u = (F.map u).hom := rfl

variable [HasColimit (F ⋙ CategoryTheory.Comon.forget C)]

/-- The underlying object of the colimit of a diagram of comonoid objects. -/
noncomputable def cpt : C := colimit (F ⋙ CategoryTheory.Comon.forget C)

/-- The colimit injections, as morphisms of the ambient category. -/
noncomputable def cinc (j : J) : (F.obj j).X ⟶ cpt F :=
  colimit.ι (F ⋙ CategoryTheory.Comon.forget C) j

/-- The colimit injections are compatible with the diagram:
`(F.map u).hom ≫ cinc F j' = cinc F j`. -/
@[reassoc (attr := simp)]
lemma map_comp_cinc {j j' : J} (u : j ⟶ j') : (F.map u).hom ≫ cinc F j' = cinc F j :=
  colimit.w (F ⋙ CategoryTheory.Comon.forget C) u

/-- Two morphisms out of `cpt F` agreeing after each colimit injection `cinc F j` are equal. -/
lemma cpt_hom_ext {Z : C} {f g : cpt F ⟶ Z} (h : ∀ j, cinc F j ≫ f = cinc F j ≫ g) : f = g :=
  colimit.hom_ext h

/-- The cocone defining the comultiplication of the colimit. -/
@[simps]
noncomputable def comulCocone : Cocone (F ⋙ CategoryTheory.Comon.forget C) where
  pt := cpt F ⊗ cpt F
  ι :=
    { app := fun j => Δ[(F.obj j).X] ≫ (cinc F j ⊗ₘ cinc F j)
      naturality := fun j j' u => by
        have h := IsComonHom.hom_comul (F.map u).hom
        dsimp
        rw [Category.comp_id, ← Category.assoc, h]
        rw [Category.assoc, tensorHom_comp_tensorHom, map_comp_cinc] }

/-- The cocone defining the counit of the colimit. -/
@[simps]
noncomputable def counitCocone : Cocone (F ⋙ CategoryTheory.Comon.forget C) where
  pt := 𝟙_ C
  ι :=
    { app := fun j => ε[(F.obj j).X]
      naturality := fun j j' u => by
        have h := IsComonHom.hom_counit (F.map u).hom
        dsimp
        rw [Category.comp_id]
        exact h }

/-- The comultiplication of the colimit. -/
noncomputable def ccomul : cpt F ⟶ cpt F ⊗ cpt F := colimit.desc _ (comulCocone F)

/-- The counit of the colimit. -/
noncomputable def ccounit : cpt F ⟶ 𝟙_ C := colimit.desc _ (counitCocone F)

/-- `cinc F j ≫ ccomul F = Δ[(F.obj j).X] ≫ (cinc F j ⊗ₘ cinc F j)`. -/
@[reassoc (attr := simp)]
lemma cinc_ccomul (j : J) : cinc F j ≫ ccomul F = Δ[(F.obj j).X] ≫ (cinc F j ⊗ₘ cinc F j) :=
  colimit.ι_desc _ _

/-- `cinc F j ≫ ccounit F = ε[(F.obj j).X]`. -/
@[reassoc (attr := simp)]
lemma cinc_ccounit (j : J) : cinc F j ≫ ccounit F = ε[(F.obj j).X] :=
  colimit.ι_desc _ _

/-- The comonoid structure on the colimit of a diagram of comonoid objects. -/
noncomputable instance comonObjCpt : ComonObj (cpt F) where
  counit := ccounit F
  comul := ccomul F
  counit_comul := by
    refine cpt_hom_ext F fun j => ?_
    rw [cinc_ccomul_assoc, ← tensorHom_id, tensorHom_comp_tensorHom, cinc_ccounit,
      Category.comp_id, MonoidalCategory.tensorHom_def, ← Category.assoc,
      ComonObj.counit_comul, leftUnitor_inv_naturality]
  comul_counit := by
    refine cpt_hom_ext F fun j => ?_
    rw [cinc_ccomul_assoc, ← id_tensorHom, tensorHom_comp_tensorHom, cinc_ccounit,
      Category.comp_id, tensorHom_def', ← Category.assoc, ComonObj.comul_counit,
      rightUnitor_inv_naturality]
  comul_assoc := by
    refine cpt_hom_ext F fun j => ?_
    have hL : (cinc F j ⊗ₘ cinc F j) ≫ (cpt F ◁ ccomul F)
        = ((F.obj j).X ◁ Δ[(F.obj j).X]) ≫ (cinc F j ⊗ₘ (cinc F j ⊗ₘ cinc F j)) := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp, cinc_ccomul]
    have hR : (cinc F j ⊗ₘ cinc F j) ≫ (ccomul F ▷ cpt F)
        = (Δ[(F.obj j).X] ▷ (F.obj j).X) ≫ ((cinc F j ⊗ₘ cinc F j) ⊗ₘ cinc F j) := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp, cinc_ccomul]
    rw [cinc_ccomul_assoc, cinc_ccomul_assoc, hL, ← Category.assoc (cinc F j ⊗ₘ cinc F j), hR,
      ← Category.assoc, ComonObj.comul_assoc]
    simp only [Category.assoc]
    rw [associator_naturality]

/-- The comultiplication of `cpt F` satisfies
`cinc F j ≫ Δ[cpt F] = Δ[(F.obj j).X] ≫ (cinc F j ⊗ₘ cinc F j)`. -/
@[reassoc (attr := simp)]
lemma cinc_comul (j : J) :
    cinc F j ≫ Δ[cpt F] = Δ[(F.obj j).X] ≫ (cinc F j ⊗ₘ cinc F j) := cinc_ccomul F j

/-- The counit of `cpt F` satisfies `cinc F j ≫ ε[cpt F] = ε[(F.obj j).X]`. -/
@[reassoc (attr := simp)]
lemma cinc_counit (j : J) : cinc F j ≫ ε[cpt F] = ε[(F.obj j).X] := cinc_ccounit F j

/-- The colimit inclusions `cinc F j` are morphisms of comonoid objects. -/
instance isComonHom_cinc (j : J) : IsComonHom (cinc F j) where
  hom_counit := cinc_ccounit F j
  hom_comul := cinc_ccomul F j

/-- The colimit of a diagram of comonoid objects, as a comonoid object. -/
noncomputable abbrev colimitComon : CategoryTheory.Comon C := ⟨cpt F⟩

/-- The colimit cocone in `Comon C`. -/
@[simps]
noncomputable def colimitCocone : Cocone F where
  pt := colimitComon F
  ι :=
    { app := fun j => CategoryTheory.Comon.Hom.mk (cinc F j)
      naturality := fun j j' u =>
        CategoryTheory.Comon.ext (by simp [map_comp_cinc F u]) }

/-- The morphism out of the colimit induced by a cocone, on underlying objects. -/
noncomputable def descHom (s : Cocone F) : cpt F ⟶ s.pt.X :=
  colimit.desc _ ((CategoryTheory.Comon.forget C).mapCocone s)

/-- `descHom` after a colimit injection is the leg of the cocone. -/
@[reassoc (attr := simp)]
lemma cinc_descHom (s : Cocone F) (j : J) : cinc F j ≫ descHom F s = (s.ι.app j).hom :=
  colimit.ι_desc _ _

/-- The colimit of a diagram of comonoid objects is computed on underlying objects. -/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc s :=
    CategoryTheory.Comon.Hom.mk' (M := colimitComon F) (N := s.pt) (descHom F s)
      (by
        refine cpt_hom_ext F fun j => ?_
        rw [← Category.assoc, cinc_descHom, IsComonHom.hom_counit, cinc_counit])
      (by
        refine cpt_hom_ext F fun j => ?_
        rw [← Category.assoc, cinc_descHom, IsComonHom.hom_comul, ← Category.assoc, cinc_comul,
          Category.assoc, tensorHom_comp_tensorHom, cinc_descHom])
  fac s j := CategoryTheory.Comon.ext (cinc_descHom F s j)
  uniq s m hm := CategoryTheory.Comon.ext (by
    refine cpt_hom_ext F fun j => ?_
    exact (congrArg CategoryTheory.Comon.Hom.hom (hm j)).trans (cinc_descHom F s j).symm)

/-- The image of the colimit cocone under the forgetful functor is the colimit cocone of the
underlying diagram. -/
noncomputable def forgetMapCoconeIso :
    (CategoryTheory.Comon.forget C).mapCocone (colimitCocone F)
      ≅ colimit.cocone (F ⋙ CategoryTheory.Comon.forget C) :=
  Cocone.ext (Iso.refl _) (fun j => by
    simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, Iso.refl_hom]
    exact Category.comp_id _)

/-- The forgetful functor `Comon C ⥤ C` preserves the colimit of any diagram whose underlying
diagram has a colimit. -/
noncomputable instance forget_preservesColimit :
    PreservesColimit F (CategoryTheory.Comon.forget C) :=
  preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit F)
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ CategoryTheory.Comon.forget C))
      (forgetMapCoconeIso F).symm)

end Comon

section ComonShape

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [HasColimitsOfShape J C]

/-- **`Comon C` has all the colimits that `C` has**, computed on underlying objects. -/
noncomputable instance Comon.hasColimitsOfShape :
    HasColimitsOfShape J (CategoryTheory.Comon C) where
  has_colimit F := ⟨_, Comon.colimitCoconeIsColimit F⟩

/-- **The forgetful functor `Comon C ⥤ C` preserves colimits.** -/
noncomputable instance Comon.forget_preservesColimitsOfShape :
    PreservesColimitsOfShape J (CategoryTheory.Comon.forget C) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone (Comon.colimitCoconeIsColimit F)
      (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ CategoryTheory.Comon.forget C))
        (Comon.forgetMapCoconeIso F).symm)

end ComonShape

/-! ## The cocommutative case -/

namespace CommComon

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [BraidedCategory.{v} C]
variable (F : J ⥤ CategoryTheory.CommComon C)

/-- The forgetful functor from cocommutative comonoids to comonoids is full. -/
instance full_forget₂Comon : (CategoryTheory.CommComon.forget₂Comon C).Full :=
  inferInstanceAs (inducedFunctor CategoryTheory.CommComon.toComon).Full

/-- The forgetful functor from cocommutative comonoids to comonoids is faithful. -/
instance faithful_forget₂Comon : (CategoryTheory.CommComon.forget₂Comon C).Faithful :=
  inferInstanceAs (inducedFunctor CategoryTheory.CommComon.toComon).Faithful

/-- The diagram of underlying comonoid objects. -/
noncomputable abbrev toComonDiagram : J ⥤ CategoryTheory.Comon C :=
  F ⋙ CategoryTheory.CommComon.forget₂Comon C

/-! The underlying diagram of a diagram of cocommutative comonoid objects has a colimit as soon
as the composite forgetful functor to the ambient category has one.  This is the individual
diagram hypothesis under which the cocommutative colimit construction below works. -/
variable [HasColimit (toComonDiagram F ⋙ CategoryTheory.Comon.forget C)]

/-- Each object of the underlying comonoid diagram is cocommutative. -/
instance isCommComonObj_obj (j : J) : IsCommComonObj ((toComonDiagram F).obj j).X :=
  (F.obj j).comm

/-- **The colimit of a diagram of cocommutative comonoid objects is cocommutative.** -/
instance isCommComonObj_cpt : IsCommComonObj (Comon.cpt (toComonDiagram F)) where
  comul_comm := by
    refine Comon.cpt_hom_ext (toComonDiagram F) fun j => ?_
    rw [Comon.cinc_comul_assoc, Comon.cinc_comul, BraidedCategory.braiding_naturality,
      ← Category.assoc, IsCommComonObj.comul_comm]

/-- The colimit of a diagram of cocommutative comonoid objects, as a cocommutative comonoid
object. -/
noncomputable abbrev colimitCommComon : CategoryTheory.CommComon C :=
  ⟨Comon.cpt (toComonDiagram F)⟩

/-- **The inclusion of the cocommutative comonoid objects into all comonoid objects creates
colimits**: the colimit of a diagram of cocommutative comonoid objects, formed in `Comon C`, is
again cocommutative. -/
noncomputable instance createsColimit_forget₂Comon :
    CreatesColimit F (CategoryTheory.CommComon.forget₂Comon C) := by
  haveI : HasColimit (F ⋙ CategoryTheory.CommComon.forget₂Comon C) :=
    ⟨_, Comon.colimitCoconeIsColimit (toComonDiagram F)⟩
  exact createsColimitOfFullyFaithfulOfIso (colimitCommComon F)
    (colimit.isoColimitCocone
      ⟨Comon.colimitCocone (toComonDiagram F), Comon.colimitCoconeIsColimit _⟩).symm

/-- **`CommComon C` has the colimit of every diagram whose underlying diagram has a colimit in
`C`**, computed on underlying objects. -/
noncomputable instance hasColimit : HasColimit F := by
  have : HasColimit (F ⋙ CategoryTheory.CommComon.forget₂Comon C) :=
    ⟨_, Comon.colimitCoconeIsColimit (toComonDiagram F)⟩
  exact hasColimit_of_created F (CategoryTheory.CommComon.forget₂Comon C)

/-- The forgetful functor `CommComon C ⥤ Comon C` preserves the colimit of a diagram whose
underlying diagram has a colimit. -/
noncomputable instance forget₂Comon_preservesColimit :
    PreservesColimit F (CategoryTheory.CommComon.forget₂Comon C) := by
  have : HasColimit (F ⋙ CategoryTheory.CommComon.forget₂Comon C) :=
    ⟨_, Comon.colimitCoconeIsColimit (toComonDiagram F)⟩
  exact preservesColimit_of_createsColimit_and_hasColimit _ _

end CommComon

section CommComonShape

variable {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [BraidedCategory.{v} C]

/-- **`CommComon C` has all the colimits that `C` has**. -/
noncomputable instance CommComon.hasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CategoryTheory.CommComon C) where
  has_colimit F := CommComon.hasColimit F

end CommComonShape

end UlmerBialgebras
