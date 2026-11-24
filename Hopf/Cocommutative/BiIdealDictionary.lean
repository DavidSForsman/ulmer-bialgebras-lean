module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Hopf.Cocommutative.BiIdealQuotient
public import Hopf.Cocommutative.GrpHomDictionary
public import Hopf.Cocommutative.Subcoalgebra
public import Hopf.Mathlib.CocommEquivalence
public import InternalGroups.GrpObjSubgroupCorrespondenceBiIdeal

/-!
# Bi-ideals of group objects of `Comon_k^coc` are left bi-ideals

Let `k` be a field and `H` a group object of `Comon_k^coc = CommComon (ModuleCat k)`, a
cocommutative Hopf algebra (`Hopf/Cocommutative/GrpCocommHopf.lean`).  Newman's categorical
correspondence (`InternalGroups/GrpObjSubgroupCorrespondenceBiIdeal.lean`) takes values in the
bi-ideals of `H`: the subobjects of `H` in `ModuleCat k` which are kernels of morphisms `H ⟶ M` of
`H`-modules in `CommComon (ModuleCat k)` (`InternalGroups.BiIdeal`).  This file compares them with
the left bi-ideals of the Hopf algebra `H` (`HopfAlgebra.Cocommutative.LeftBiIdeal`), the codomain
of Newman's algebraic correspondence `HopfAlgebra.Cocommutative.Correspondence.tauEquiv`.

* The kernel of a morphism of cocommutative coalgebras out of `H` is a coideal
  (`UlmerBialgebras.CocommComon.Internal.comul_mem_of_mem_ker`); the kernel of a morphism of
  `H`-modules out of `H` is moreover a left ideal, hence a left bi-ideal
  (`InternalGroups.isLeftBiIdeal_ker_modLinearMap`).
* A categorical kernel corresponds to the linear kernel under the order isomorphism
  `ModuleCat.subobjectModule` between subobjects and submodules
  (`InternalGroups.subobjectModule_kernelSubobject`).
* A subcoalgebra of a cocommutative coalgebra is an object of `Comon_k^coc` with an injective
  morphism to it (`InternalGroups.exists_subcoalgebra_hom`), and a generalized element with values
  in the image of an injective morphism factors through it
  (`InternalGroups.exists_comp_eq_of_range_le`).
* So every bi-ideal is a left bi-ideal (`InternalGroups.BiIdeal.toLeftBiIdeal`), and this
  assignment is injective (`InternalGroups.BiIdeal.toLeftBiIdeal_injective`).

## Main results

* `InternalGroups.isLeftBiIdeal_ker_modLinearMap`: the kernel of a morphism of `H`-modules out of
  `H` is a left bi-ideal;
* `InternalGroups.BiIdeal.toLeftBiIdeal`, `InternalGroups.BiIdeal.toLeftBiIdeal_injective`: the
  injective map from bi-ideals to left bi-ideals.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits
open scoped MonObj ComonObj MonoidalLeftAction HopfAlgebra.Cocommutative.GrpDict

namespace UlmerBialgebras.CocommComon.Internal

open HopfAlgebra.Cocommutative.GrpDict

variable {k : Type u} [Field k]

/-! ### Comonoid morphisms of `k`-modules, pointwise -/

section Pointwise

variable {M N : ModuleCat.{u} k} [ComonObj M] [ComonObj N] (f : M ⟶ N) [IsComonHom f]

/-- A comonoid morphism of `k`-modules preserves the counit: `ε (f x) = ε x`. -/
lemma counit_hom_apply (x : M) : ε[N].hom (f.hom x) = ε[M].hom x :=
  congr(($(IsComonHom.hom_counit f)).hom x)

/-- A comonoid morphism of `k`-modules commutes with the comultiplication:
`Δ (f x) = (f ⊗ f) (Δ x)`. -/
lemma comul_hom_apply (x : M) :
    Δ[N].hom (f.hom x) = TensorProduct.map f.hom f.hom (Δ[M].hom x) :=
  congr(($(IsComonHom.hom_comul f)).hom x)

end Pointwise

/-- The underlying linear map of a morphism of cocommutative coalgebras out of the underlying
coalgebra of a group object, typed so that its source carries the Hopf algebra structure. -/
abbrev outLinearMap {X : Grp (CategoryTheory.CommComon (ModuleCat.{u} k))}
    {B : CategoryTheory.CommComon (ModuleCat.{u} k)} (φ : X.X ⟶ B) :
    (X.X.X : ModuleCat.{u} k) →ₗ[k] (B.X : ModuleCat.{u} k) :=
  φ.hom.hom.hom

/-- **The kernel of a morphism of coalgebras out of a Hopf algebra is a coideal**, over a field:
`Δ (ker φ) ⊆ ker φ ⊗ X + X ⊗ ker φ`. -/
lemma comul_mem_of_mem_ker {X : Grp (CategoryTheory.CommComon (ModuleCat.{u} k))}
    {B : CategoryTheory.CommComon (ModuleCat.{u} k)} (φ : X.X ⟶ B) {x : (X.X.X : ModuleCat.{u} k)}
    (hx : x ∈ LinearMap.ker (outLinearMap φ)) :
    Coalgebra.comul (R := k) x ∈
      HopfAlgebra.Cocommutative.leftTensor (LinearMap.ker (outLinearMap φ)) ⊔
      HopfAlgebra.Cocommutative.rightTensor (LinearMap.ker (outLinearMap φ)) := by
  set n := outLinearMap φ
  have hcomul : TensorProduct.map n n (Coalgebra.comul (R := k) x) = 0 := by
    have h : Coalgebra.comul (R := k) (n x) = TensorProduct.map n n (Coalgebra.comul (R := k) x) :=
      comul_hom_apply φ.hom.hom x
    have hx0 : n x = 0 := hx
    rw [← h, hx0, map_zero]
  have hinj : Function.Injective (TensorProduct.map (LinearMap.range n).subtype
      (LinearMap.range n).subtype) :=
    TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
      (Submodule.injective_subtype _)
  have hcomp : TensorProduct.map n n = TensorProduct.map (LinearMap.range n).subtype
      (LinearMap.range n).subtype ∘ₗ TensorProduct.map n.rangeRestrict n.rangeRestrict := by
    rw [← TensorProduct.map_comp]
    rfl
  have hmem : Coalgebra.comul (R := k) x ∈ LinearMap.ker (TensorProduct.map n n) :=
    LinearMap.mem_ker.mpr hcomul
  rw [hcomp, LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hinj),
    HopfAlgebra.Cocommutative.ker_map_of_surjective _ n.surjective_rangeRestrict,
    LinearMap.ker_rangeRestrict] at hmem
  exact hmem

end UlmerBialgebras.CocommComon.Internal

namespace InternalGroups

open HopfAlgebra.Cocommutative.GrpDict UlmerBialgebras

/-! ## Kernels as submodules -/

/-- The submodule of a subobject of modules is the range of its arrow. -/
lemma subobjectModule_apply {R : Type u} [Ring R] {M : ModuleCat.{u} R} (S : Subobject M) :
    ModuleCat.subobjectModule M S = LinearMap.range S.arrow.hom := rfl

/-- **A categorical kernel of modules is the linear kernel**, under the order isomorphism
`ModuleCat.subobjectModule` between subobjects and submodules. -/
lemma subobjectModule_kernelSubobject {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [HasKernel f] : ModuleCat.subobjectModule M (kernelSubobject f) = LinearMap.ker f.hom := by
  rw [subobjectModule_apply]
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      kernelSubobject_arrow_comp, ModuleCat.hom_zero, LinearMap.zero_apply]
  · let g : ModuleCat.of R R ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
    have hg : g ≫ f = 0 := by
      ext
      simpa [g] using LinearMap.mem_ker.1 hx
    refine ⟨(factorThruKernelSubobject f g hg).hom 1, ?_⟩
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, factorThruKernelSubobject_comp_arrow]
    simp [g]

/-! ## Subcoalgebras and factorization through injective morphisms -/

section Subcoalgebra

variable {k : Type u} [Field k]

/-- **A generalized element with values in the image of an injective morphism of cocommutative
coalgebras factors through it.** -/
theorem exists_comp_eq_of_range_le {N X T : CategoryTheory.CommComon (ModuleCat.{u} k)}
    (n : N ⟶ X) (hn : Function.Injective n.hom.hom.hom) (x : T ⟶ X)
    (hx : LinearMap.range x.hom.hom.hom ≤ LinearMap.range n.hom.hom.hom) :
    ∃ z : T ⟶ N, z ≫ n = x := by
  -- The linear map `z₀ = n⁻¹ ∘ x`, defined since `x` lands in the range of the injective `n`.
  have hxt : ∀ t, x.hom.hom.hom t ∈ LinearMap.range n.hom.hom.hom := fun t => hx ⟨t, rfl⟩
  let z₀ : (T.X : ModuleCat.{u} k) →ₗ[k] (N.X : ModuleCat.{u} k) :=
    (LinearEquiv.ofInjective n.hom.hom.hom hn).symm.toLinearMap ∘ₗ
      (x.hom.hom.hom).codRestrict _ hxt
  have hz₀ : ∀ t, n.hom.hom.hom (z₀ t) = x.hom.hom.hom t := fun t =>
    LinearEquiv.ofInjective_symm_apply (f := n.hom.hom.hom) (h := hn) ⟨x.hom.hom.hom t, hxt t⟩
  have hz₀' : n.hom.hom.hom ∘ₗ z₀ = x.hom.hom.hom := LinearMap.ext hz₀
  have hnn : Function.Injective (TensorProduct.map n.hom.hom.hom n.hom.hom.hom) :=
    TensorProduct.map_injective_of_flat_flat _ _ hn hn
  -- `z₀` is a morphism of coalgebras: both conditions hold after composing with `n`, which is
  -- injective, and so is `n ⊗ n` over a field.
  let z : T.X ⟶ N.X := ModuleCat.ofHom z₀
  have hcounit : z ≫ ε[N.X] = ε[T.X] := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    calc ε[N.X].hom (z₀ t)
        = ε[X.X].hom (n.hom.hom.hom (z₀ t)) :=
          (CocommComon.Internal.counit_hom_apply n.hom.hom (z₀ t)).symm
      _ = ε[X.X].hom (x.hom.hom.hom t) := by rw [hz₀]
      _ = ε[T.X].hom t := CocommComon.Internal.counit_hom_apply x.hom.hom t
  have hcomul : z ≫ Δ[N.X] = Δ[T.X] ≫ (z ⊗ₘ z) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    change Δ[N.X].hom (z₀ t) = TensorProduct.map z₀ z₀ (Δ[T.X].hom t)
    refine hnn ?_
    have h1 : Δ[X.X].hom (n.hom.hom.hom (z₀ t)) =
        TensorProduct.map n.hom.hom.hom n.hom.hom.hom (Δ[N.X].hom (z₀ t)) :=
      CocommComon.Internal.comul_hom_apply n.hom.hom (z₀ t)
    have h2 : Δ[X.X].hom (x.hom.hom.hom t) =
        TensorProduct.map x.hom.hom.hom x.hom.hom.hom (Δ[T.X].hom t) :=
      CocommComon.Internal.comul_hom_apply x.hom.hom t
    have hmap : TensorProduct.map n.hom.hom.hom n.hom.hom.hom ∘ₗ TensorProduct.map z₀ z₀ =
        TensorProduct.map x.hom.hom.hom x.hom.hom.hom :=
      (TensorProduct.map_comp _ _ _ _).symm.trans (congrArg₂ TensorProduct.map hz₀' hz₀')
    rw [← h1, hz₀, h2]
    exact (LinearMap.congr_fun hmap _).symm
  have : IsComonHom z := { hom_counit := hcounit, hom_comul := hcomul }
  exact ⟨CommComon.homMk z, CategoryTheory.CommComon.hom_ext _ _
    (ModuleCat.hom_ext (LinearMap.ext hz₀))⟩

/-- **A subcoalgebra of a cocommutative coalgebra**, as an object of `Comon_k^coc` with a
morphism to it whose underlying linear map is the inclusion. -/
lemma exists_subcoalgebra_hom (X : CategoryTheory.CommComon (ModuleCat.{u} k))
    (E : Submodule k X.X)
    (hE : ∀ x ∈ E, Coalgebra.comul (R := k) x ∈
      LinearMap.range (TensorProduct.map E.subtype E.subtype)) :
    ∃ (N : CategoryTheory.CommComon (ModuleCat.{u} k)) (n : N ⟶ X),
      Function.Injective n.hom.hom.hom ∧ LinearMap.range n.hom.hom.hom = E := by
  let C : CoalgCat.{u} k := (CoalgCat.ofComon k).obj X.toComon
  have : Coalgebra.IsCocomm k C := (CoalgCat.ofComon_isCocomm_iff X.toComon).2 X.comm
  let E' : Submodule k C := E
  have hE : Subcoalg.IsSubcoalgebra E' := hE
  let := Subcoalg.subCoalgebra hE
  have : Coalgebra.IsCocomm k E' := ⟨Subcoalg.subComul_comm hE⟩
  let incl : E' →ₗc[k] C :=
    { E'.subtype with
      counit_comp := rfl
      map_comp_comul := Subcoalg.map_subtype_comp_subComul hE }
  let G := CoalgCat.toCommComonObj (CoalgCat.of k E')
  have : IsComonHom (C := ModuleCat.{u} k) (M := G.X) (N := X.X) (ModuleCat.ofHom E'.subtype) :=
    ((CoalgCat.toComon k).map (CoalgCat.ofHom incl)).isComonHom_hom
  exact ⟨G, CommComon.homMk (ModuleCat.ofHom E'.subtype), E'.injective_subtype, E'.range_subtype⟩

end Subcoalgebra

/-! ## Bi-ideals are left bi-ideals -/

variable {k : Type u} [Field k] {H : Grp (CategoryTheory.CommComon (ModuleCat.{u} k))}

/-- The underlying linear map of a morphism of `H`-modules out of `H`. -/
noncomputable abbrev modLinearMap {M : Mod (CategoryTheory.CommComon (ModuleCat.{u} k)) H.X}
    (f : selfMod H.X ⟶ M) : (H.X.X : ModuleCat.{u} k) →ₗ[k] (M.X.X : ModuleCat.{u} k) :=
  (modHomA f).hom

/-- **A morphism of `H`-modules out of `H` is `H`-linear**: `f (a * x) = a • f x`. -/
lemma modLinearMap_mul {M : Mod (CategoryTheory.CommComon (ModuleCat.{u} k)) H.X}
    (f : selfMod H.X ⟶ M) (a x : (H.X.X : ModuleCat.{u} k)) :
    modLinearMap f (a * x) =
      (ModObj.smul (M := H.X) (X := M.X)).hom.hom.hom (a ⊗ₜ modLinearMap f x) := by
  have h1 := IsModHom.smul_hom (A := H.X) (f := f.hom)
  have h2 := congr(($h1).hom.hom.hom (a ⊗ₜ[k] x))
  simp only [CategoryTheory.CommComon.comp_hom] at h2
  have hw : (H.X ⊴ₗ f.hom).hom.hom = 𝟙 _ ⊗ₘ f.hom.hom.hom :=
    congr(($((id_tensorHom H.X f.hom).symm)).hom.hom).trans (tensorHom_hom_hom _ _)
  rw [hw] at h2
  change modLinearMap f ((μ[H.X]).hom.hom.hom (a ⊗ₜ[k] x)) = _ at h2
  rw [← mulHom_eq] at h2
  exact h2

/-- **The kernel of a morphism of `H`-modules out of `H` is a left bi-ideal** of the Hopf
algebra `H`. -/
theorem isLeftBiIdeal_ker_modLinearMap {M : Mod (CategoryTheory.CommComon (ModuleCat.{u} k)) H.X}
    (f : selfMod H.X ⟶ M) :
    HopfAlgebra.Cocommutative.IsLeftBiIdeal (LinearMap.ker (modLinearMap f)) where
  mul_mem a x hx := by
    rw [LinearMap.mem_ker, modLinearMap_mul, LinearMap.mem_ker.1 hx, TensorProduct.tmul_zero]
    exact map_zero (ModObj.smul (M := H.X) (X := M.X)).hom.hom.hom
  counit_eq_zero x hx := by
    have hcounit : Coalgebra.counit (R := k) (modLinearMap f x) = Coalgebra.counit (R := k) x :=
      CocommComon.Internal.counit_hom_apply f.hom.hom.hom x
    rw [← hcounit, LinearMap.mem_ker.1 hx, map_zero]
  comul_mem x hx := CocommComon.Internal.comul_mem_of_mem_ker (X := H) f.hom hx

/-- **A bi-ideal of `H` is a left bi-ideal of the Hopf algebra `H`**: the submodule corresponding
to the subobject. -/
noncomputable def BiIdeal.toLeftBiIdeal (I : BiIdeal H.X) :
    HopfAlgebra.Cocommutative.LeftBiIdeal k (H.X.X : ModuleCat.{u} k) where
  carrier := ModuleCat.subobjectModule _ I.1
  isLeftBiIdeal := by
    rw [← I.kernelSubobject_map, subobjectModule_kernelSubobject]
    exact isLeftBiIdeal_ker_modLinearMap I.map

/-- **Distinct bi-ideals are distinct left bi-ideals.** -/
theorem BiIdeal.toLeftBiIdeal_injective :
    Function.Injective (BiIdeal.toLeftBiIdeal (H := H)) := fun _ _ hIJ =>
  Subtype.ext ((ModuleCat.subobjectModule (H.X.X : ModuleCat.{u} k)).injective
    congr(($hIJ).carrier))

end InternalGroups
