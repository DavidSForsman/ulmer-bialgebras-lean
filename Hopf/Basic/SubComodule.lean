module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Hopf.Basic.ComoduleFinite
public import Hopf.Basic.RelativeHopfModule

/-!
# Subcomodules as comodules

If `N` is a subcomodule of a right `C`-comodule `M` over a field `k` (that is, `ρ N ⊆ N ⊗ C`),
then `N` is itself a right `C`-comodule: the coaction of `M` restricts to `N`, because the map
`N ⊗ C → M ⊗ C` is injective (`C` is free, hence flat, over the field `k`).

Likewise a `K`-submodule of a relative `(H,K)`-Hopf module which is a subcomodule is again a
relative `(H,K)`-Hopf module.  This is what makes Takeuchi's Corollary 2.3 usable: a relative
Hopf module is the filtered union of *relative Hopf modules* which are finitely generated over
`K`.

## Main definitions

* `Coalgebra.Comodule.subCoact`: the restricted coaction of a subcomodule;
* `Coalgebra.Comodule.subComodule`: the comodule structure of a subcomodule.

## Main results

* `HopfAlgebra.isRelativeHopfModule_sub`: a `K`-submodule of a relative `(H,K)`-Hopf module
  which is a subcomodule is a relative `(H,K)`-Hopf module.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Corollary 2.3
-/

@[expose] public section

namespace Submodule

open TensorProduct

variable {k C M : Type*} [Field k] [AddCommGroup C] [Module k C] [AddCommGroup M] [Module k M]
  (N : Submodule k M)

/-- The inclusion `N ⊗ (C ⊗ C) → M ⊗ (C ⊗ C)` commutes with the associators. -/
private lemma rTensor_subtype_assoc (t : (↥N ⊗[k] C) ⊗[k] C) :
    LinearMap.rTensor (C ⊗[k] C) N.subtype ((TensorProduct.assoc k ↥N C C) t)
      = (TensorProduct.assoc k M C C)
          (LinearMap.rTensor C (LinearMap.rTensor C N.subtype) t) := by
  induction t with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul u c =>
    induction u with
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul x d => simp

/-- The inclusion `N → M` commutes with the right unitors after `id ⊗ ε`. -/
private lemma subtype_rid_lTensor_counit [Coalgebra k C] (t : ↥N ⊗[k] C) :
    N.subtype (TensorProduct.rid k ↥N (LinearMap.lTensor ↥N (Coalgebra.counit (R := k) (A := C)) t))
      = TensorProduct.rid k M (LinearMap.lTensor M (Coalgebra.counit (R := k) (A := C))
          (LinearMap.rTensor C N.subtype t)) := by
  induction t with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x c => simp

end Submodule

section
open Coalgebra Coalgebra.Comodule HopfAlgebra
namespace Coalgebra.Comodule

open _root_.TensorProduct _root_.Coalgebra

variable {k C M : Type*} [Field k] [AddCommGroup C] [Module k C] [AddCommGroup M] [Module k M]

variable (N : Submodule k M)

/-- Over a field, the inclusion `N ⊗ C → M ⊗ C` is injective. -/
lemma rTensor_subtype_injective :
    Function.Injective (LinearMap.rTensor C N.subtype) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype N)

variable [Coalgebra k C]

/-- The inclusion `N ⊗ C → M ⊗ C` commutes with the comultiplication of `C`. -/
private lemma rTensor_subtype_lTensor_comul (t : ↥N ⊗[k] C) :
    LinearMap.rTensor (C ⊗[k] C) N.subtype (LinearMap.lTensor ↥N (comul (R := k) (A := C)) t)
      = LinearMap.lTensor M (comul (R := k) (A := C)) (LinearMap.rTensor C N.subtype t) := by
  induction t with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul x c => simp

variable [RightComodule k C M] {N} (hN : IsSubcomodule (C := C) N)
include hN

/-- The coaction of a subcomodule. -/
noncomputable def subCoact : ↥N →ₗ[k] ↥N ⊗[k] C :=
  (LinearEquiv.ofInjective (LinearMap.rTensor C N.subtype)
      (rTensor_subtype_injective N)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (LinearMap.rTensor C N.subtype))
      ((coact (R := k) (C := C)) ∘ₗ N.subtype) (fun x => hN x x.2)

/-- Defining property of the restricted coaction. -/
@[simp] lemma rTensor_subtype_subCoact (x : ↥N) :
    LinearMap.rTensor C N.subtype (subCoact hN x) = coact (R := k) (C := C) (x : M) := by
  set e := LinearEquiv.ofInjective (LinearMap.rTensor C N.subtype)
    (rTensor_subtype_injective N) with he
  have h : ∀ y : ↥(LinearMap.range (LinearMap.rTensor C N.subtype)),
      LinearMap.rTensor C N.subtype (e.symm y) = (y : M ⊗[k] C) := by
    intro y
    exact Subtype.ext_iff.1 (e.apply_symm_apply y)
  exact h _

/-- A subcomodule is a comodule. -/
@[instance_reducible]
noncomputable def subComodule : RightComodule k C ↥N where
  coact := subCoact hN
  coassoc := by
    have hinj : Function.Injective (LinearMap.rTensor (C ⊗[k] C) N.subtype) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype N)
    ext x
    apply hinj
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [Submodule.rTensor_subtype_assoc, rTensor_subtype_lTensor_comul]
    have h1 : LinearMap.rTensor C (LinearMap.rTensor C N.subtype)
          (LinearMap.rTensor C (subCoact hN) (subCoact hN x))
        = LinearMap.rTensor C (coact (R := k) (C := C)) (coact (R := k) (C := C) (x : M)) := by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      have h2 : (LinearMap.rTensor C N.subtype) ∘ₗ (subCoact hN)
          = (coact (R := k) (C := C)) ∘ₗ N.subtype := by
        ext y; simp
      rw [h2, LinearMap.rTensor_comp]
      rw [LinearMap.comp_apply, rTensor_subtype_subCoact hN x]
    rw [h1, rTensor_subtype_subCoact hN x]
    exact congr($(Coalgebra.RightComodule.coassoc (R := k) (C := C) (M := M)) (x : M))
  counit_coact := by
    refine LinearMap.ext fun x => Submodule.injective_subtype N ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe,
      id_eq]
    rw [Submodule.subtype_rid_lTensor_counit, rTensor_subtype_subCoact hN x]
    exact congr($(Coalgebra.RightComodule.counit_coact (R := k) (C := C) (M := M)) (x : M))

end Coalgebra.Comodule

namespace HopfAlgebra

open TensorProduct _root_.Coalgebra Coalgebra.Comodule

variable {k K H M : Type*} [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] [AddCommGroup M] [Module k M] [Module K M]
  [IsScalarTower k K M] [RightComodule k H M] {φ : K →ₐc[k] H}

/-- A `K`-submodule of a relative `(H,K)`-Hopf module which is a subcomodule is again a relative
`(H,K)`-Hopf module. -/
theorem isRelativeHopfModule_sub (hM : IsRelativeHopfModule k K H M φ) (W : Submodule K M)
    (hW : IsSubcomodule (C := H) (W.restrictScalars k)) :
    letI : RightComodule k H ↥W := Coalgebra.Comodule.subComodule hW
    IsRelativeHopfModule k K H ↥W φ := by
  let : RightComodule k H ↥W := Coalgebra.Comodule.subComodule hW
  intro x w
  let ι : ↥W →ₗ[k] M := (W.restrictScalars k).subtype
  have hinj : Function.Injective (LinearMap.rTensor H ι) :=
    Coalgebra.Comodule.rTensor_subtype_injective _
  apply hinj
  have hsmul : ((x • w : ↥W) : M) = x • (w : M) := rfl
  have hcoact : ∀ v : ↥W,
      LinearMap.rTensor H ι (coact (R := k) (C := H) v) = coact (R := k) (C := H) (v : M) :=
    fun v => Coalgebra.Comodule.rTensor_subtype_subCoact hW v
  rw [hcoact (x • w), hsmul, hM x (w : M)]
  have hrel : ∀ (u : K ⊗[k] K) (t : ↥W ⊗[k] H),
      LinearMap.rTensor H ι (relCompat k K H ↥W φ (u ⊗ₜ[k] t))
        = relCompat k K H M φ (u ⊗ₜ[k] LinearMap.rTensor H ι t) := by
    intro u t
    induction u with
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul a b =>
      induction t with
      | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
      | tmul v h =>
        simp only [relCompat_tmul, LinearMap.rTensor_tmul]
        rfl
  rw [hrel, hcoact w]

end HopfAlgebra
end
