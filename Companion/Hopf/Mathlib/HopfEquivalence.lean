module

public import Mathlib.Algebra.Category.HopfAlgCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import Companion.Hopf.Mathlib.BimonEquivalence

/-!
# Equivalence between `R`-Hopf algebras and Hopf monoid objects in `ModuleCat R`

Given a commutative ring `R`, this file establishes the equivalence of categories
between bundled `R`-Hopf algebras (`HopfAlgCat R`) and internal Hopf monoids in the
symmetric monoidal category of `R`-modules (`Hopf (ModuleCat R)`).

## Main definitions

* `HopfAlgCat.instHopfObj`: the `HopfObj` instance on `ModuleCat.of R H` for `H : HopfAlgCat R`.
* `HopfAlgCat.toHopf`: the functor `HopfAlgCat R ⥤ Hopf (ModuleCat R)`.
* `Hopf.instHopfAlgebra`: the `HopfAlgebra R M.X` structure for `M : Hopf (ModuleCat R)`.
* `Hopf.ofHopf`: the inverse functor `Hopf (ModuleCat R) ⥤ HopfAlgCat R`.
* `HopfAlgCat.hopfEquivalence`: the equivalence `HopfAlgCat R ≌ Hopf (ModuleCat R)`.
* `Hopf.forget`: the forgetful functor from `Hopf C` to `C`.
* `HopfAlgCat.toHopfForget`: compatibility of `toHopf` with the forgetful functors to `ModuleCat R`.

## Implementation notes

Building upon the equivalence `BialgCat R ≌ Bimon (ModuleCat R)`
from `Hopf.Mathlib.BimonEquivalence`,
we match the antipode on an `R`-Hopf algebra with the categorical antipode morphism `𝒮`
on a Hopf monoid in `ModuleCat R`. The antipode axioms correspond directly to the
commutativity of the antipode triangles in `ModuleCat R`.

## References

* M. E. Sweedler, *Hopf Algebras* (1969)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj ComonObj Comon CoalgCat
open ModuleCat.MonModuleEquivalenceAlgebra
open scoped TensorProduct

variable {R : Type u} [CommRing R]

namespace CategoryTheory

instance HopfAlgCat.hasForgetToModule : HasForget₂ (HopfAlgCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun X => ModuleCat.of R X
      map := fun f => ModuleCat.ofHom f.toBialgHom.toLinearMap }

/-- The forgetful functor from `HopfAlgCat R` to `ModuleCat R` sends `X` to `ModuleCat.of R X`. -/
@[simp]
theorem HopfAlgCat.forget₂_module_obj (X : HopfAlgCat R) :
    (forget₂ (HopfAlgCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

/-- The forgetful functor to `ModuleCat R` sends a Hopf algebra map to its underlying linear map. -/
@[simp]
theorem HopfAlgCat.forget₂_module_map {X Y : HopfAlgCat R} (f : X ⟶ Y) :
    (forget₂ (HopfAlgCat R) (ModuleCat R)).map f = ModuleCat.ofHom f.toBialgHom.toLinearMap :=
  rfl

namespace HopfAlgCat

/-- The Hopf monoid object structure on the underlying module of an `R`-Hopf algebra. -/
@[simps!]
noncomputable instance instHopfObj (X : HopfAlgCat.{u} R) :
    HopfObj (ModuleCat.of R X) where
  toBimonObj := BialgCat.instBimonObj ((forget₂ (HopfAlgCat R) (BialgCat R)).obj X)
  antipode := ModuleCat.ofHom (HopfAlgebra.antipode R)
  antipode_left := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]
    exact HopfAlgebra.mul_antipode_rTensor_comul
  antipode_right := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_comp]
    exact HopfAlgebra.mul_antipode_lTensor_comul

/-- The Hopf monoid object associated to an `R`-Hopf algebra. -/
noncomputable def toHopfObj (X : HopfAlgCat.{u} R) : Hopf (ModuleCat.{u} R) where
  X := ModuleCat.of R X

/-- The morphism of Hopf monoid objects induced by a morphism of `R`-Hopf algebras. -/
noncomputable def toHopfMap {X Y : HopfAlgCat.{u} R} (f : X ⟶ Y) :
    toHopfObj X ⟶ toHopfObj Y :=
  InducedCategory.homMk ((BialgCat.toBimon R).map ((forget₂ (HopfAlgCat R) (BialgCat R)).map f))

variable (R) in
/-- The natural functor from `R`-Hopf algebras to Hopf monoids in `ModuleCat R`. -/
noncomputable def toHopf : HopfAlgCat.{u} R ⥤ Hopf (ModuleCat.{u} R) where
  obj := toHopfObj
  map := toHopfMap
  map_id X := by
    apply InducedCategory.hom_ext
    exact (BialgCat.toBimon R).map_id ((forget₂ (HopfAlgCat R) (BialgCat R)).obj X)
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (BialgCat.toBimon R).map_comp ((forget₂ (HopfAlgCat R) (BialgCat R)).map f)
      ((forget₂ (HopfAlgCat R) (BialgCat R)).map g)

end HopfAlgCat

namespace Hopf

attribute [local instance] MonObj.toRing Algebra_of_Mon_
attribute [local instance] CoalgCat.ofComonObjCoalgebraStruct

/-- The multiplication of a Hopf monoid in `ModuleCat R` is the linear map `LinearMap.mul'`. -/
lemma hom_mul_eq_hopf (M : Hopf (ModuleCat.{u} R)) :
    ModuleCat.Hom.hom μ[M.X] = LinearMap.mul' R M.X :=
  TensorProduct.ext' fun _ _ => rfl

/-- The unit of a Hopf monoid in `ModuleCat R` is the algebra map `Algebra.linearMap R M.X`. -/
lemma hom_one_eq_hopf (M : Hopf (ModuleCat.{u} R)) :
    ModuleCat.Hom.hom η[M.X] = Algebra.linearMap R M.X :=
  LinearMap.ext_ring rfl

/-- A Hopf monoid in `ModuleCat R` has a natural `R`-Hopf algebra structure. -/
@[instance_reducible]
noncomputable def instHopfAlgebra (M : Hopf (ModuleCat.{u} R)) : HopfAlgebra R M.X where
  toBialgebra := Bimon.instBialgebra (Hopf.toBimon M)
  antipode := M.hopf.antipode.hom
  mul_antipode_rTensor_comul := by
    have h := HopfObj.antipode_left M.X
    have h_hom := ModuleCat.hom_ext_iff.1 h
    simp only [ModuleCat.hom_comp] at h_hom
    rw [hom_mul_eq_hopf M, hom_one_eq_hopf M] at h_hom
    exact h_hom
  mul_antipode_lTensor_comul := by
    have h := HopfObj.antipode_right M.X
    have h_hom := ModuleCat.hom_ext_iff.1 h
    simp only [ModuleCat.hom_comp] at h_hom
    rw [hom_mul_eq_hopf M, hom_one_eq_hopf M] at h_hom
    exact h_hom

/-- The `R`-Hopf algebra associated to a Hopf monoid in `ModuleCat R`. -/
noncomputable def ofHopfObj (M : Hopf (ModuleCat.{u} R)) : HopfAlgCat.{u} R :=
  let _ : Ring M.X := inferInstance
  let _ : HopfAlgebra R M.X := instHopfAlgebra M
  HopfAlgCat.of R M.X

/-- The morphism of `R`-Hopf algebras induced by a morphism of Hopf monoid objects. -/
noncomputable def ofHopfMap {M N : Hopf (ModuleCat.{u} R)} (f : M ⟶ N) :
    ofHopfObj M ⟶ ofHopfObj N :=
  ⟨((Bimon.ofBimon R).map f.hom).toBialgHom⟩

variable (R) in
/-- The natural functor from Hopf monoids in `ModuleCat R` to `R`-Hopf algebras. -/
noncomputable def ofHopf : Hopf (ModuleCat.{u} R) ⥤ HopfAlgCat.{u} R where
  obj := ofHopfObj
  map := ofHopfMap
  map_id M := by
    apply HopfAlgCat.hom_ext
    exact BialgCat.Hom.ext_iff.1 ((Bimon.ofBimon R).map_id M.toBimon)
  map_comp f g := by
    apply HopfAlgCat.hom_ext
    exact BialgCat.Hom.ext_iff.1 ((Bimon.ofBimon R).map_comp f.hom g.hom)

end Hopf

namespace HopfAlgCat

variable (X : HopfAlgCat.{u} R)

/-- Auxiliary definition for the unit isomorphism of `hopfEquivalence`. -/
noncomputable def hopfUnitIsoApp :
    X ≅ (toHopf R ⋙ Hopf.ofHopf R).obj X where
  hom := ⟨(BialgCat.unitIsoApp ((forget₂ (HopfAlgCat R) (BialgCat R)).obj X)).hom.toBialgHom⟩
  inv := ⟨(BialgCat.unitIsoApp ((forget₂ (HopfAlgCat R) (BialgCat R)).obj X)).inv.toBialgHom⟩
  hom_inv_id := HopfAlgCat.hom_ext _ _
    (BialgCat.Hom.ext_iff.1 (BialgCat.unitIsoApp _).hom_inv_id)
  inv_hom_id := HopfAlgCat.hom_ext _ _
    (BialgCat.Hom.ext_iff.1 (BialgCat.unitIsoApp _).inv_hom_id)

variable (M : Hopf (ModuleCat.{u} R))

/-- Auxiliary definition for the counit isomorphism of `hopfEquivalence`. -/
noncomputable def hopfCounitIsoApp :
    (Hopf.ofHopf R ⋙ toHopf R).obj M ≅ M :=
  InducedCategory.isoMk (BialgCat.counitIsoApp M.toBimon)

variable (R) in
/-- The natural category equivalence between `R`-Hopf algebras and Hopf monoids in
`ModuleCat R`. -/
noncomputable def hopfEquivalence : HopfAlgCat.{u} R ≌ Hopf (ModuleCat.{u} R) where
  functor := toHopf R
  inverse := Hopf.ofHopf R
  unitIso := NatIso.ofComponents hopfUnitIsoApp (fun f => by
    apply HopfAlgCat.hom_ext
    exact BialgCat.Hom.ext_iff.1 ((BialgCat.bimonEquivalence R).unitIso.hom.naturality
      ((forget₂ (HopfAlgCat R) (BialgCat R)).map f)))
  counitIso := NatIso.ofComponents hopfCounitIsoApp (fun f => by
    apply InducedCategory.hom_ext
    exact (BialgCat.bimonEquivalence R).counitIso.hom.naturality f.hom)
  functor_unitIso_comp X := by
    apply InducedCategory.hom_ext
    exact (BialgCat.bimonEquivalence R).functor_unitIso_comp
      ((forget₂ (HopfAlgCat R) (BialgCat R)).obj X)

end HopfAlgCat

namespace Hopf

variable (C : Type*) [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- The forgetful functor from `Hopf C` to `C`. -/
def forget : Hopf C ⥤ C :=
  inducedFunctor Hopf.toBimon ⋙ Bimon.forget C

/-- The forgetful functor `Hopf.forget C` sends a Hopf monoid `M` to its underlying object. -/
@[simp]
theorem forget_obj (M : Hopf C) : (forget C).obj M = M.X :=
  rfl

/-- The forgetful functor `Hopf.forget C` sends a morphism to its underlying morphism in `C`. -/
@[simp]
theorem forget_map {M N : Hopf C} (f : M ⟶ N) : (forget C).map f = f.hom.hom.hom :=
  rfl

end Hopf

namespace HopfAlgCat

variable (R) in
/-- Compatibility of `toHopf` with the forgetful functors to `ModuleCat R`. -/
noncomputable def toHopfForget :
    toHopf R ⋙ Hopf.forget (ModuleCat.{u} R) ≅ forget₂ (HopfAlgCat.{u} R) (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    apply ModuleCat.hom_ext
    rfl)

end HopfAlgCat

end CategoryTheory
