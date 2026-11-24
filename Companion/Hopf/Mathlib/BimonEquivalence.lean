module

public import Mathlib.Algebra.Category.BialgCat.Basic
public import Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import Mathlib.CategoryTheory.Monoidal.Bimon_

/-!
# Equivalence between `R`-bialgebras and bimonoid objects in `ModuleCat R`

Given a commutative ring `R`, this file establishes the equivalence of categories
between bundled `R`-bialgebras (`BialgCat R`) and internal bimonoid objects in the
symmetric monoidal category of `R`-modules (`Bimon (ModuleCat R)`).

## Main definitions

* `BialgCat.instBimonObj`: the `BimonObj` instance on `ModuleCat.of R B` for `B : BialgCat R`.
* `BialgCat.toBimon`: the functor `BialgCat R ⥤ Bimon (ModuleCat R)`.
* `Bimon.instBialgebra`: the `Bialgebra R M.X.X` structure for `M : Bimon (ModuleCat R)`.
* `Bimon.ofBimon`: the inverse functor `Bimon (ModuleCat R) ⥤ BialgCat R`.
* `BialgCat.bimonEquivalence`: the equivalence `BialgCat R ≌ Bimon (ModuleCat R)`.
* `BialgCat.toBimonForget`: compatibility of `toBimon` with the forgetful functors to `ModuleCat R`.

## Implementation notes

The equivalence builds directly on Mathlib's `ModuleCat.monModuleEquivalenceAlgebra` and
`CoalgCat.comonEquivalence`. The four coherence axioms of `BimonObj`
(`one_counit`, `one_comul`, `mul_counit`, `mul_comul`) are verified using the corresponding
axioms of `Bialgebra` together with `LinearMap.mul'_tensor` and `tensorμ_eq_tensorTensorTensorComm`.

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

instance BialgCat.hasForgetToModule : HasForget₂ (BialgCat R) (ModuleCat R) where
  forget₂ :=
    { obj := fun X => ModuleCat.of R X
      map := fun f => ModuleCat.ofHom f.toBialgHom.toLinearMap }

/-- The forgetful functor from `R`-bialgebras to `R`-modules sends `X` to `ModuleCat.of R X`. -/
@[simp]
theorem BialgCat.forget₂_module_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (ModuleCat R)).obj X = ModuleCat.of R X :=
  rfl

/-- The forgetful functor from `R`-bialgebras to `R`-modules sends a morphism to its underlying
linear map. -/
@[simp]
theorem BialgCat.forget₂_module_map {X Y : BialgCat R} (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (ModuleCat R)).map f = ModuleCat.ofHom f.toBialgHom.toLinearMap :=
  rfl

namespace BialgCat

/-- The monoid object structure on the underlying module of an `R`-bialgebra. -/
@[simps!]
noncomputable instance instMonObj (X : BialgCat.{u} R) :
    MonObj (ModuleCat.of R X) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj ((forget₂ (BialgCat R) (AlgCat R)).obj X)

/-- The comonoid object structure on the underlying module of an `R`-bialgebra. -/
@[simps!]
noncomputable instance instComonObj (X : BialgCat.{u} R) :
    ComonObj (ModuleCat.of R X) :=
  (CoalgCat.toComonObj ((forget₂ (BialgCat R) (CoalgCat R)).obj X)).comon

/-- The unit of `ModuleCat.of R X` is the algebra map. -/
@[simp] lemma hom_one_apply (X : BialgCat.{u} R) (r : R) :
    (η[ModuleCat.of R X]).hom r = algebraMap R X r := rfl

/-- The multiplication of `ModuleCat.of R X` is that of `X`. -/
@[simp] lemma hom_mul_tmul (X : BialgCat.{u} R) (x y : X) :
    (μ[ModuleCat.of R X]).hom (x ⊗ₜ y) = x * y := rfl

/-- The counit of `ModuleCat.of R X` is that of `X`. -/
@[simp] lemma hom_counit_apply (X : BialgCat.{u} R) (x : X) :
    (ε[ModuleCat.of R X]).hom x = Coalgebra.counit x := rfl

/-- The comultiplication of `ModuleCat.of R X` is that of `X`. -/
@[simp] lemma hom_comul_apply (X : BialgCat.{u} R) (x : X) :
    (Δ[ModuleCat.of R X]).hom x = Coalgebra.comul x := rfl

/-- The unit of an `R`-bialgebra followed by its counit is the identity of the monoidal unit of
`ModuleCat R`. -/
lemma one_counit (X : BialgCat.{u} R) :
    η[ModuleCat.of R X] ≫ ε[ModuleCat.of R X] = 𝟙 (𝟙_ (ModuleCat R)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
  rw [hom_one_apply, hom_counit_apply, map_one, Bialgebra.counit_one]

/-- The unit of an `R`-bialgebra followed by its comultiplication is the unit of the tensor square.
-/
lemma one_comul (X : BialgCat.{u} R) :
    η[ModuleCat.of R X] ≫ Δ[ModuleCat.of R X] = η[ModuleCat.of R X ⊗ ModuleCat.of R X] := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [MonObj.tensorObj.one_def]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply]
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [hom_one_apply, hom_comul_apply, map_one, Bialgebra.comul_one, Algebra.TensorProduct.one_def]

/-- The multiplication of an `R`-bialgebra followed by its counit is the counit of the tensor
square. -/
lemma mul_counit (X : BialgCat.{u} R) :
    μ[ModuleCat.of R X] ≫ ε[ModuleCat.of R X] = ε[ModuleCat.of R X ⊗ ModuleCat.of R X] := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [Comon.tensorObj_counit]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  rw [hom_mul_tmul, hom_counit_apply, hom_counit_apply, hom_counit_apply,
    smul_eq_mul, Bialgebra.counit_mul]

/-- The comultiplication of an `R`-bialgebra is multiplicative: `μ ≫ Δ` is
`(Δ ⊗ₘ Δ) ≫ tensorμ ≫ (μ ⊗ₘ μ)`. -/
lemma mul_comul (X : BialgCat.{u} R) :
    μ[ModuleCat.of R X] ≫ Δ[ModuleCat.of R X] =
      (Δ[ModuleCat.of R X] ⊗ₘ Δ[ModuleCat.of R X]) ≫
        tensorμ (ModuleCat.of R X) (ModuleCat.of R X) (ModuleCat.of R X) (ModuleCat.of R X) ≫
        (μ[ModuleCat.of R X] ⊗ₘ μ[ModuleCat.of R X]) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [hom_mul_tmul, hom_comul_apply, hom_comul_apply, hom_comul_apply, ← LinearMap.comp_apply]
  have h_mul : (ModuleCat.Hom.hom (μ[ModuleCat.of R X] ⊗ₘ μ[ModuleCat.of R X])) ∘ₗ
      (ModuleCat.Hom.hom
        (tensorμ (ModuleCat.of R X) (ModuleCat.of R X) (ModuleCat.of R X) (ModuleCat.of R X)))
      = LinearMap.mul' R (X ⊗[R] X) := by
    rw [ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm]
    rw [ModuleCat.hom_ofHom]
    rw [ModuleCat.hom_tensorHom]
    exact LinearMap.mul'_tensor.symm
  rw [h_mul]
  rw [LinearMap.mul'_apply]
  exact Bialgebra.comul_mul x y

/-- The bimonoid object structure on the underlying module of an `R`-bialgebra. -/
@[instance_reducible]
noncomputable instance instBimonObj (X : BialgCat.{u} R) :
    BimonObj (ModuleCat.of R X) where
  one_counit := one_counit X
  one_comul := one_comul X
  mul_counit := mul_counit X
  mul_comul := mul_comul X

/-- The bimonoid object associated to an `R`-bialgebra. -/
@[simps!]
noncomputable def toBimonObj (X : BialgCat.{u} R) : Bimon (ModuleCat.{u} R) :=
  Bimon.mk' (ModuleCat.of R X)

/-- The morphism of bimonoid objects induced by a morphism of `R`-bialgebras. -/
@[simps!]
noncomputable def toBimonMap {X Y : BialgCat.{u} R} (f : X ⟶ Y) :
    toBimonObj X ⟶ toBimonObj Y :=
  let _ : ComonObj (toBimonObj X).X := (toBimonObj X).comon
  let _ : ComonObj (toBimonObj Y).X := (toBimonObj Y).comon
  { hom :=
      { hom := ModuleCat.ofHom f.toBialgHom.toLinearMap
        isMonHom_hom :=
          { one_hom := ModuleCat.hom_ext <| LinearMap.ext f.toBialgHom.toAlgHom.commutes
            mul_hom := ModuleCat.hom_ext <|
              TensorProduct.ext <| LinearMap.ext₂ <| map_mul f.toBialgHom } }
    isComonHom_hom :=
      { hom_counit := Mon.Hom.ext <| ModuleCat.hom_ext f.toBialgHom.counit_comp
        hom_comul := Mon.Hom.ext <| ModuleCat.hom_ext f.toBialgHom.map_comp_comul.symm } }

variable (R) in
/-- The natural functor from `R`-bialgebras to bimonoid objects in `ModuleCat R`. -/
@[simps]
noncomputable def toBimon : BialgCat.{u} R ⥤ Bimon (ModuleCat.{u} R) where
  obj := toBimonObj
  map := toBimonMap
  map_id X := by
    apply Bimon.ext
    rfl
  map_comp f g := by
    apply Bimon.ext
    rfl

end BialgCat

namespace Bimon

attribute [local instance] MonObj.toRing Algebra_of_Mon_
attribute [local instance] CoalgCat.ofComonObjCoalgebraStruct

/-- The multiplication of a bimonoid object in `ModuleCat R` is the linear map `LinearMap.mul'` of
its ring structure. -/
lemma hom_mul_eq (M : Bimon (ModuleCat.{u} R)) :
    ModuleCat.Hom.hom μ[M.X.X] = LinearMap.mul' R M.X.X :=
  TensorProduct.ext' fun _ _ => rfl

/-- The counit of a bimonoid object in `ModuleCat R` sends `1` to `1`. -/
lemma counit_one_of_bimon (M : Bimon (ModuleCat.{u} R)) :
    Coalgebra.counit (R := R) (1 : M.X.X) = (1 : R) := by
  have h := BimonObj.one_counit M.X.X
  have h_app := congr($(ModuleCat.hom_ext_iff.mp h) (1 : R))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at h_app
  exact h_app

/-- The counit of a bimonoid object in `ModuleCat R` is multiplicative. -/
lemma counit_mul_of_bimon (M : Bimon (ModuleCat.{u} R)) (a b : M.X.X) :
    Coalgebra.counit (R := R) (a * b) = Coalgebra.counit a * Coalgebra.counit b := by
  have h := BimonObj.mul_counit M.X.X
  have h_app := congr($(ModuleCat.hom_ext_iff.mp h) (a ⊗ₜ[R] b))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h_app
  rw [Comon.tensorObj_counit] at h_app
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h_app
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at h_app
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply] at h_app
  rw [smul_eq_mul] at h_app
  exact h_app

/-- The comultiplication of a bimonoid object in `ModuleCat R` sends `1` to `1`. -/
lemma comul_one_of_bimon (M : Bimon (ModuleCat.{u} R)) :
    Coalgebra.comul (R := R) (1 : M.X.X) = (1 : M.X.X ⊗[R] M.X.X) := by
  have h := BimonObj.one_comul M.X.X
  have h_app := congr($(ModuleCat.hom_ext_iff.mp h) (1 : R))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h_app
  rw [MonObj.tensorObj.one_def] at h_app
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h_app
  rw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply] at h_app
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at h_app
  rw [Algebra.TensorProduct.one_def]
  exact h_app

/-- The comultiplication of a bimonoid object in `ModuleCat R` is multiplicative. -/
lemma comul_mul_of_bimon (M : Bimon (ModuleCat.{u} R)) (a b : M.X.X) :
    Coalgebra.comul (R := R) (a * b) = Coalgebra.comul a * Coalgebra.comul b := by
  have h := BimonObj.mul_comul M.X.X
  have h_app := congr($(ModuleCat.hom_ext_iff.mp h) (a ⊗ₜ[R] b))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h_app
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at h_app
  have h_mul : (ModuleCat.Hom.hom (μ[M.X.X] ⊗ₘ μ[M.X.X])) ∘ₗ
      (ModuleCat.Hom.hom (tensorμ M.X.X M.X.X M.X.X M.X.X))
      = LinearMap.mul' R (M.X.X ⊗[R] M.X.X) := by
    rw [ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm]
    rw [ModuleCat.hom_ofHom]
    rw [ModuleCat.hom_tensorHom]
    rw [hom_mul_eq]
    exact LinearMap.mul'_tensor.symm
  change Coalgebra.comul (a * b) =
    ((ModuleCat.Hom.hom (μ[M.X.X] ⊗ₘ μ[M.X.X])) ∘ₗ
      (ModuleCat.Hom.hom (tensorμ M.X.X M.X.X M.X.X M.X.X)))
      (Coalgebra.comul a ⊗ₜ Coalgebra.comul b) at h_app
  rw [h_mul] at h_app
  rw [LinearMap.mul'_apply] at h_app
  exact h_app

/-- A bimonoid object in `ModuleCat R` has a natural `R`-bialgebra structure. -/
@[instance_reducible]
noncomputable def instBialgebra (M : Bimon (ModuleCat.{u} R)) : Bialgebra R M.X.X :=
  let _ : Coalgebra R M.X.X := (CoalgCat.ofComonObj M.X.X).instCoalgebra
  Bialgebra.mk' R M.X.X (counit_one_of_bimon M) (fun {a b} => counit_mul_of_bimon M a b)
    (comul_one_of_bimon M) (fun {a b} => comul_mul_of_bimon M a b)

/-- The `R`-bialgebra associated to a bimonoid object in `ModuleCat R`. -/
noncomputable def ofBimonObj (M : Bimon (ModuleCat.{u} R)) : BialgCat.{u} R :=
  let _ : Ring M.X.X := inferInstance
  let _ : Bialgebra R M.X.X := instBialgebra M
  BialgCat.of R M.X.X

/-- The morphism of `R`-bialgebras induced by a morphism of bimonoid objects. -/
noncomputable def ofBimonMap {M N : Bimon (ModuleCat.{u} R)} (f : M ⟶ N) :
    ofBimonObj M ⟶ ofBimonObj N :=
  let _ : Ring M.X.X := inferInstance
  let _ : Ring N.X.X := inferInstance
  let _ : Bialgebra R M.X.X := instBialgebra M
  let _ : Bialgebra R N.X.X := instBialgebra N
  BialgCat.ofHom
    { toLinearMap := f.hom.hom.hom
      map_one' := congr($(ModuleCat.hom_ext_iff.mp (IsMonHom.one_hom f.hom.hom)) (1 : R))
      map_mul' := fun x y =>
        congr($(ModuleCat.hom_ext_iff.mp (IsMonHom.mul_hom f.hom.hom)) (x ⊗ₜ[R] y))
      counit_comp := ModuleCat.hom_ext_iff.mp (congr(($(f.isComonHom_hom.hom_counit)).hom))
      map_comp_comul :=
        (ModuleCat.hom_ext_iff.mp (congr(($(f.isComonHom_hom.hom_comul)).hom))).symm }

variable (R) in
/-- The natural functor from bimonoid objects in `ModuleCat R` to `R`-bialgebras. -/
@[simps]
noncomputable def ofBimon : Bimon (ModuleCat.{u} R) ⥤ BialgCat.{u} R where
  obj := ofBimonObj
  map := ofBimonMap
  map_id M := by
    apply BialgCat.hom_ext
    rfl
  map_comp f g := by
    apply BialgCat.hom_ext
    rfl

end Bimon

namespace BialgCat

variable (X : BialgCat.{u} R)

/-- The tensor product of two copies of the identity from `X` to the bialgebra of `toBimonObj X` is
the identity. -/
lemma id_tensor_id_eq : (TensorProduct.map
    (LinearMap.id : X.carrier →ₗ[R] (Bimon.ofBimonObj (toBimonObj X)).carrier)
    (LinearMap.id : X.carrier →ₗ[R] (Bimon.ofBimonObj (toBimonObj X)).carrier)) = LinearMap.id :=
  TensorProduct.ext' fun _ _ => rfl

/-- The tensor product of two copies of the identity from the bialgebra of `toBimonObj X` to `X` is
the identity. -/
lemma id_tensor_id_eq' : (TensorProduct.map
    (LinearMap.id : (Bimon.ofBimonObj (toBimonObj X)).carrier →ₗ[R] X.carrier)
    (LinearMap.id : (Bimon.ofBimonObj (toBimonObj X)).carrier →ₗ[R] X.carrier)) = LinearMap.id :=
  TensorProduct.ext' fun _ _ => rfl

/-- Auxiliary definition for the unit isomorphism of `bimonEquivalence`. -/
noncomputable def unitIsoApp :
    X ≅ (toBimon R ⋙ Bimon.ofBimon R).obj X where
  hom := ⟨{
    toLinearMap := LinearMap.id
    map_one' := (map_one (algebraMap R X)).symm
    map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y)
    counit_comp := rfl
    map_comp_comul := by
      ext x : 1
      exact congr($(id_tensor_id_eq X) (Coalgebra.comul x)) }⟩
  inv := ⟨{
    toLinearMap := LinearMap.id
    map_one' := map_one (algebraMap R X)
    map_mul' := fun x y => (@LinearMap.mul'_apply R _ _ _ _ _ _ x y).symm
    counit_comp := rfl
    map_comp_comul := by
      ext x : 1
      exact congr($(id_tensor_id_eq' X) (Coalgebra.comul x)) }⟩
  hom_inv_id := BialgCat.hom_ext _ _ rfl
  inv_hom_id := BialgCat.hom_ext _ _ rfl

variable (M : Bimon (ModuleCat.{u} R))

/-- The identity of the underlying module of `M` commutes with the comultiplications:
`𝟙 ≫ Δ = Δ ≫ (𝟙 ⊗ₘ 𝟙)`. -/
lemma counitIsoApp_hom_comul :
    (𝟙 M.X.X : M.X.X ⟶ M.X.X) ≫ Δ[M.X.X] =
      Δ[M.X.X] ≫ (𝟙 M.X.X ⊗ₘ 𝟙 M.X.X) := by
  rw [Category.id_comp]
  have h_id : (𝟙 M.X.X ⊗ₘ 𝟙 M.X.X : M.X.X ⊗ M.X.X ⟶ M.X.X ⊗ M.X.X) = 𝟙 (M.X.X ⊗ M.X.X) := by
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_tensorHom, ModuleCat.hom_id, TensorProduct.map_id]
  rw [h_id, Category.comp_id]

/-- Auxiliary definition for the counit isomorphism of `bimonEquivalence`. -/
noncomputable def counitIsoApp :
    (Bimon.ofBimon R ⋙ toBimon R).obj M ≅ M where
  hom :=
    let _ : ComonObj ((Bimon.ofBimon R ⋙ toBimon R).obj M).X :=
      ((Bimon.ofBimon R ⋙ toBimon R).obj M).comon
    let _ : ComonObj M.X := M.comon
    { hom :=
        { hom := 𝟙 M.X.X
          isMonHom_hom :=
            { one_hom := ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl
              mul_hom := ModuleCat.hom_ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl } }
      isComonHom_hom :=
        { hom_counit := Mon.Hom.ext <| ModuleCat.hom_ext rfl
          hom_comul := Mon.Hom.ext (counitIsoApp_hom_comul M) } }
  inv :=
    let _ : ComonObj ((Bimon.ofBimon R ⋙ toBimon R).obj M).X :=
      ((Bimon.ofBimon R ⋙ toBimon R).obj M).comon
    let _ : ComonObj M.X := M.comon
    { hom :=
        { hom := 𝟙 M.X.X
          isMonHom_hom :=
            { one_hom := ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl
              mul_hom := ModuleCat.hom_ext <| TensorProduct.ext <| LinearMap.ext₂ fun _ _ => rfl } }
      isComonHom_hom :=
        { hom_counit := Mon.Hom.ext <| ModuleCat.hom_ext rfl
          hom_comul := Mon.Hom.ext (counitIsoApp_hom_comul M) } }
  hom_inv_id := Bimon.ext rfl
  inv_hom_id := Bimon.ext rfl

variable (R) in
/-- The natural category equivalence between `R`-bialgebras and bimonoid objects in
`ModuleCat R`. -/
noncomputable def bimonEquivalence : BialgCat.{u} R ≌ Bimon (ModuleCat.{u} R) where
  functor := toBimon R
  inverse := Bimon.ofBimon R
  unitIso := NatIso.ofComponents unitIsoApp (fun f => by
    apply BialgCat.hom_ext
    ext x
    rfl)
  counitIso := NatIso.ofComponents counitIsoApp (fun f => by
    apply Bimon.ext
    rfl)
  functor_unitIso_comp X := by
    apply Bimon.ext
    rfl

variable (R) in
/-- Compatibility of `toBimon` with the forgetful functors to `ModuleCat R`. -/
noncomputable def toBimonForget :
    toBimon R ⋙ Bimon.forget (ModuleCat.{u} R) ≅ forget₂ (BialgCat.{u} R) (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    apply ModuleCat.hom_ext
    rfl)

end BialgCat

end CategoryTheory
