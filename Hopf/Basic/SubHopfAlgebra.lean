module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Smooth.Flat
public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Basic.NormalHopfIdeal

/-!
# A sub-Hopf algebra is a Hopf algebra

Let `H` be a commutative Hopf algebra over a commutative von Neumann regular ring `k` (for instance
a field) and let `K` be a subalgebra of `H` which is closed under the comultiplication and the
antipode (`HopfAlgebra.IsSubHopfAlgebra`). This file endows `K` with the structure of a Hopf
algebra over `k` in such a way that the inclusion `K ↪ H` is a morphism of Hopf algebras.

The comultiplication of `K` is obtained by descending `Δ|_K` along the injection
`K ⊗ K ↪ H ⊗ H`; all the axioms are then checked by injectivity.

## Main results

* `HopfAlgebra.subComul`, `HopfAlgebra.subAntipode`: the structure maps on `↥K`;
* `HopfAlgebra.subCoalgebra`, `HopfAlgebra.subBialgebra`,
  `HopfAlgebra.subHopfAlgebra`: the `Coalgebra`, `Bialgebra` and `HopfAlgebra` instances
  on `↥K`;
* `HopfAlgebra.subInclusion`: the inclusion `K ↪ H` as a morphism of bialgebras
  `↥K →ₐc[k] H`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra
namespace HopfAlgebra

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
    {K : Subalgebra k H}

/-! ### The injection `K ⊗ K ↪ H ⊗ H` -/

variable (K) in
/-- The inclusion `K ⊗ K → H ⊗ H`. -/
noncomputable abbrev mapVal2 : (↥K) ⊗[k] (↥K) →ₗ[k] H ⊗[k] H :=
  TensorProduct.map K.val.toLinearMap K.val.toLinearMap

/-- The inclusion `K → H` is injective. -/
lemma val_injective : Function.Injective (K.val.toLinearMap) := Subtype.val_injective

/-- Over a field, the inclusion `K ⊗ K → H ⊗ H` is injective (tensor of flat injections). -/
lemma mapVal2_injective [IsAbsFlat k] : Function.Injective (mapVal2 (k := k) K) :=
  TensorProduct.map_injective_of_flat_flat _ _ val_injective val_injective

/-- `mapVal2` is the linear map underlying the algebra map `K ⊗ K → H ⊗ H`. -/
lemma mapVal2_algHom :
    (Algebra.TensorProduct.map K.val K.val).toLinearMap = mapVal2 (k := k) K := by
  ext x y; simp

/-- `mapVal2` is multiplicative. -/
lemma mapVal2_mul (u v : (↥K) ⊗[k] (↥K)) :
    mapVal2 (k := k) K (u * v) = mapVal2 (k := k) K u * mapVal2 (k := k) K v := by
  simp only [← mapVal2_algHom, AlgHom.toLinearMap_apply, map_mul]

/-! ### The structure maps -/

variable (K) in
/-- The antipode of a sub-Hopf algebra. -/
noncomputable def subAntipode [hK : IsSubHopfAlgebra k K] : (↥K) →ₗ[k] (↥K) where
  toFun x := ⟨antipode k ((x : H)), hK.antipode_mem _ x.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-! ### Naturality lemmas -/

/-- Naturality of the associator with respect to the inclusion `K → H`. -/
lemma mapVal_assoc (u : ((↥K) ⊗[k] (↥K)) ⊗[k] (↥K)) :
    TensorProduct.map K.val.toLinearMap (mapVal2 (k := k) K)
        (TensorProduct.assoc k (↥K) (↥K) (↥K) u)
      = TensorProduct.assoc k H H H
          (TensorProduct.map (mapVal2 (k := k) K) K.val.toLinearMap u) := by
  induction u with
  | tmul t c =>
    induction t with
    | tmul a b => simp
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Naturality of the multiplication with respect to the inclusion `K → H`. -/
lemma mapVal_mul' (t : (↥K) ⊗[k] (↥K)) :
    ((LinearMap.mul' k (↥K) t : ↥K) : H) = LinearMap.mul' k H (mapVal2 (k := k) K t) := by
  induction t with
  | tmul a b => simp
  | add p q hp hq => push_cast [map_add, hp, hq]; ring

variable [hK : IsSubHopfAlgebra k K]
/-- The antipode of `K` is the restriction of the antipode of `H`. -/
@[simp] lemma val_subAntipode (x : ↥K) :
    ((subAntipode K x : ↥K) : H) = antipode k ((x : H)) := rfl

/-- Naturality of `S ⊗ id` with respect to the inclusion `K → H`. -/
lemma mapVal2_rTensor_antipode (t : (↥K) ⊗[k] (↥K)) :
    mapVal2 (k := k) K (LinearMap.rTensor (↥K) (subAntipode K) t)
      = LinearMap.rTensor H (antipode k (A := H)) (mapVal2 (k := k) K t) := by
  induction t with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Naturality of `id ⊗ S` with respect to the inclusion `K → H`. -/
lemma mapVal2_lTensor_antipode (t : (↥K) ⊗[k] (↥K)) :
    mapVal2 (k := k) K (LinearMap.lTensor (↥K) (subAntipode K) t)
      = LinearMap.lTensor H (antipode k (A := H)) (mapVal2 (k := k) K t) := by
  induction t with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-! ### The comultiplication: here flatness is used -/

variable [IsAbsFlat k]

variable (K) in
/-- The comultiplication of a sub-Hopf algebra, obtained by descending `Δ|_K` along the
injection `K ⊗ K ↪ H ⊗ H`. -/
noncomputable def subComul : (↥K) →ₗ[k] (↥K) ⊗[k] (↥K) :=
  (LinearEquiv.ofInjective (mapVal2 (k := k) K) mapVal2_injective).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (mapVal2 (k := k) K))
      ((comul (R := k) (A := H)) ∘ₗ K.val.toLinearMap) (fun x => hK.comul_mem x x.2)

/-- The comultiplication of `K` is the restriction of that of `H`: `mapVal2 (Δ_K x) = Δ x`. -/
@[simp] lemma mapVal2_subComul (x : ↥K) :
    mapVal2 (k := k) K (subComul K x) = comul (R := k) ((x : H)) := by
  have h := (LinearEquiv.ofInjective (mapVal2 (k := k) K) mapVal2_injective).apply_symm_apply
    (⟨comul (R := k) ((x : H)), hK.comul_mem x x.2⟩ : LinearMap.range (mapVal2 (k := k) K))
  exact Subtype.ext_iff.1 h

/-- Naturality of `Δ ⊗ id` with respect to the inclusion `K → H`. -/
lemma mapVal_rTensor (t : (↥K) ⊗[k] (↥K)) :
    TensorProduct.map (mapVal2 (k := k) K) K.val.toLinearMap
        (LinearMap.rTensor (↥K) (subComul K) t)
      = LinearMap.rTensor H (comul (R := k) (A := H)) (mapVal2 (k := k) K t) := by
  induction t with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Naturality of `id ⊗ Δ` with respect to the inclusion `K → H`. -/
lemma mapVal_lTensor (t : (↥K) ⊗[k] (↥K)) :
    TensorProduct.map K.val.toLinearMap (mapVal2 (k := k) K)
        (LinearMap.lTensor (↥K) (subComul K) t)
      = LinearMap.lTensor H (comul (R := k) (A := H)) (mapVal2 (k := k) K t) := by
  induction t with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]

/-! ### The coalgebra, bialgebra and Hopf algebra structures -/

/-- The coalgebra structure on a sub-Hopf algebra. -/
noncomputable instance subCoalgebra : Coalgebra k (↥K) where
  comul := subComul K
  counit := (Coalgebra.counit (R := k) (A := H)) ∘ₗ K.val.toLinearMap
  coassoc := by
    ext x
    apply (TensorProduct.map_injective_of_flat_flat K.val.toLinearMap (mapVal2 (k := k) K)
      val_injective mapVal2_injective)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    simp only [mapVal_assoc, mapVal_rTensor, mapVal_lTensor, mapVal2_subComul]
    exact Coalgebra.coassoc_apply ((x : H))
  rTensor_counit_comp_comul := by
    ext x
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := k) K.val.toLinearMap
      val_injective
    have h : ∀ t : (↥K) ⊗[k] (↥K), LinearMap.lTensor k K.val.toLinearMap
        (LinearMap.rTensor (↥K) ((Coalgebra.counit (R := k) (A := H)) ∘ₗ K.val.toLinearMap) t)
        = LinearMap.rTensor H (Coalgebra.counit (R := k) (A := H)) (mapVal2 (k := k) K t) := by
      intro t
      induction t with
      | tmul a b => simp
      | add p q hp hq => simp only [map_add, hp, hq]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [h, mapVal2_subComul]
    simp
  lTensor_counit_comp_comul := by
    ext x
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := k) K.val.toLinearMap
      val_injective
    have h : ∀ t : (↥K) ⊗[k] (↥K), LinearMap.rTensor k K.val.toLinearMap
        (LinearMap.lTensor (↥K) ((Coalgebra.counit (R := k) (A := H)) ∘ₗ K.val.toLinearMap) t)
        = LinearMap.lTensor H (Coalgebra.counit (R := k) (A := H)) (mapVal2 (k := k) K t) := by
      intro t
      induction t with
      | tmul a b => simp
      | add p q hp hq => simp only [map_add, hp, hq]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [h, mapVal2_subComul]
    simp

/-- The counit of `K` is the restriction of the counit of `H`. -/
@[simp] lemma subCounit_apply (x : ↥K) :
    Coalgebra.counit (R := k) (A := ↥K) x = Coalgebra.counit (R := k) ((x : H)) := rfl

/-- The comultiplication of `K` maps to the comultiplication of `H` under `K ⊗ K → H ⊗ H`. -/
@[simp] lemma mapVal2_comul (x : ↥K) :
    mapVal2 (k := k) K (comul (R := k) (A := ↥K) x) = comul (R := k) ((x : H)) :=
  mapVal2_subComul x

/-- The bialgebra structure on a sub-Hopf algebra. -/
noncomputable instance subBialgebra : Bialgebra k (↥K) :=
  Bialgebra.mk' k (↥K)
    (by simp)
    (fun {a b} => by simp)
    (by
      apply mapVal2_injective
      rw [show (Coalgebra.comul (R := k) (A := ↥K) 1) = comul (R := k) (A := ↥K) 1 from rfl,
        mapVal2_comul]
      simp [Algebra.TensorProduct.one_def])
    (fun {a b} => by
      apply mapVal2_injective
      rw [show (Coalgebra.comul (R := k) (A := ↥K) (a * b))
          = comul (R := k) (A := ↥K) (a * b) from rfl, mapVal2_comul,
        show (Coalgebra.comul (R := k) (A := ↥K) a * Coalgebra.comul (R := k) (A := ↥K) b)
          = comul (R := k) (A := ↥K) a * comul (R := k) (A := ↥K) b from rfl,
        mapVal2_mul, mapVal2_comul, mapVal2_comul]
      simp)

/-- **A sub-Hopf algebra is a Hopf algebra.** -/
noncomputable instance subHopfAlgebra : HopfAlgebra k (↥K) where
  antipode := subAntipode K
  mul_antipode_rTensor_comul := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [mapVal_mul', mapVal2_rTensor_antipode, mapVal2_comul]
    simp
  mul_antipode_lTensor_comul := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [mapVal_mul', mapVal2_lTensor_antipode, mapVal2_comul]
    simp

/-- The antipode of the Hopf algebra `K` is the restriction of the antipode of `H`. -/
@[simp] lemma subAntipode_apply (x : ↥K) :
    ((antipode k (A := ↥K) x : ↥K) : H) = antipode k ((x : H)) := rfl

/-- The inclusion of a sub-Hopf algebra, as a morphism of Hopf algebras. -/
noncomputable def subInclusion : (↥K) →ₐc[k] H :=
  BialgHom.ofAlgHom K.val rfl (by ext x; exact mapVal2_comul x)

/-- `subInclusion` sends `x : K` to `(x : H)`. -/
@[simp] lemma subInclusion_apply (x : ↥K) : subInclusion (K := K) x = (x : H) := rfl

/-- The inclusion of a sub-Hopf algebra is injective. -/
lemma subInclusion_injective : Function.Injective (subInclusion (k := k) (K := K)) :=
  Subtype.val_injective

end HopfAlgebra
end
