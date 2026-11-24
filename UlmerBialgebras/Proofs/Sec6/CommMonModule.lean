module

public import Mathlib.CategoryTheory.Monoidal.Internal.Module
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Commutative monoids in `R`-modules are commutative `R`-algebras

The commutative version of Mathlib's `ModuleCat.monModuleEquivalenceAlgebra`. The functor
`CommMon (ModuleCat R) ⥤ CommAlgCat R` keeps the underlying module. It takes the multiplication
`μ(x ⊗ y)` and unit `η(1)` given by Mathlib's `MonModuleEquivalenceAlgebra.MonObj.toRing`. It is
fully faithful and essentially surjective.

## Main results

* `UlmerBialgebras.CommMonModuleEquivalenceCommAlgebra.functor`: the functor
  `CommMon (ModuleCat R) ⥤ CommAlgCat R`.
* `UlmerBialgebras.CommMonModuleEquivalenceCommAlgebra.equivalence`: an equivalence
  `CommMon (ModuleCat R) ≌ CommAlgCat R`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11 (case `A = Mod_R^op`)
-/

@[expose] public section

universe u

namespace UlmerBialgebras.CommMonModuleEquivalenceCommAlgebra

open CategoryTheory MonoidalCategory MonObj ModuleCat
open scoped ModuleCat.MonModuleEquivalenceAlgebra
open scoped TensorProduct

attribute [local ext] TensorProduct.ext

noncomputable section

variable {R : Type u} [CommRing R]

/-- The commutative ring structure of a commutative monoid in `R`-modules. -/
abbrev commRing (A : CommMon (ModuleCat.{u} R)) : CommRing A.X :=
  @CommRing.mk A.X (MonModuleEquivalenceAlgebra.MonObj.toRing A.X) fun x y =>
    congr($(ModuleCat.hom_ext_iff.mp (IsCommMonObj.mul_comm A.X)) (y ⊗ₜ x))

attribute [local instance] commRing

variable (R) in
/-- Commutative monoids in `R`-modules to commutative `R`-algebras. -/
@[simps]
def functor : CommMon (ModuleCat.{u} R) ⥤ CommAlgCat.{u} R where
  obj A := CommAlgCat.of R A.X
  map {_ _} f := CommAlgCat.ofHom
    { toFun := f.hom.hom
      map_zero' := map_zero f.hom.hom.hom
      map_add' := map_add f.hom.hom.hom
      map_one' := congr($(ModuleCat.hom_ext_iff.mp (IsMonHom.one_hom f.hom.hom)) (1 : R))
      map_mul' := fun x y =>
        congr($(ModuleCat.hom_ext_iff.mp (IsMonHom.mul_hom f.hom.hom)) (x ⊗ₜ y))
      commutes' := fun r =>
        congr($(ModuleCat.hom_ext_iff.mp (IsMonHom.one_hom f.hom.hom)) r) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `CommMon (Mod_R) ⥤ CommAlgCat R` is faithful. -/
instance : (functor R).Faithful where
  map_injective {A B} f g h := by
    ext x
    exact congr(($(h)).hom x)

/-- An algebra map between commutative monoids is a monoid map. -/
def homOfAlgHom {A B : CommMon (ModuleCat.{u} R)}
    (g : CommAlgCat.of R A.X ⟶ CommAlgCat.of R B.X) : A ⟶ B :=
  let φ : A.X ⟶ B.X := ModuleCat.ofHom g.hom.toLinearMap
  have hφ : IsMonHom φ :=
    { one_hom := by
        ext
        exact g.hom.commutes 1
      mul_hom := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        exact map_mul g.hom x y }
  CommMon.homMk (Mon.Hom.mk (isMonHom_hom := hφ) φ)

/-- The functor `CommMon (Mod_R) ⥤ CommAlgCat R` is full, with preimages `homOfAlgHom`. -/
instance : (functor R).Full where
  map_surjective {_ _} g := ⟨homOfAlgHom g, rfl⟩

/-- A commutative `R`-algebra as a commutative monoid in `R`-modules. -/
def inverseObj (B : CommAlgCat.{u} R) : CommMon (ModuleCat.{u} R) :=
  letI := MonModuleEquivalenceAlgebra.inverseObj (AlgCat.of R B)
  { X := ModuleCat.of R B
    comm := ⟨by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      exact (LinearMap.mul'_apply (R := R) (a := y) (b := x)).trans
        ((mul_comm y x).trans (LinearMap.mul'_apply (R := R) (a := x) (b := y)).symm)⟩ }

/-- `functor (inverseObj B) ≅ B`: the identity map. -/
def functorObjInverseObjIso (B : CommAlgCat.{u} R) : (functor R).obj (inverseObj B) ≅ B :=
  CommAlgCat.isoMk
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun x y => LinearMap.mul'_apply (R := R) (a := x) (b := y)
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

/-- The functor `CommMon (Mod_R) ⥤ CommAlgCat R` is essentially surjective via `inverseObj`. -/
instance : (functor R).EssSurj where
  mem_essImage B := ⟨inverseObj B, ⟨functorObjInverseObjIso B⟩⟩

/-- The functor `CommMon (Mod_R) ⥤ CommAlgCat R` is an equivalence (fully faithful and
    essentially surjective). -/
instance : (functor R).IsEquivalence where

variable (R) in
/-- **Commutative monoids in `R`-modules are commutative `R`-algebras.** -/
noncomputable def equivalence : CommMon (ModuleCat.{u} R) ≌ CommAlgCat.{u} R :=
  (functor R).asEquivalence

end

end UlmerBialgebras.CommMonModuleEquivalenceCommAlgebra
