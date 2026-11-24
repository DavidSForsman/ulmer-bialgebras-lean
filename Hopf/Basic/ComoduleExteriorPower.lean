module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Hopf.Basic.SubComodule

/-!
# The exterior algebra of a comodule

Let `H` be a commutative bialgebra over a field `k` and let `V` be a right `H`-comodule.  Takeuchi
uses (in Lemmas 4.10–4.11 of *A correspondence between Hopf ideals and sub-Hopf algebras*,
manuscripta math. **7** (1972)) the fact that the exterior powers `⋀ⁿ V` are again right
`H`-comodules.  Mathlib has exterior powers but no comodules.  This file constructs the
comodule structure on the exterior algebra `⋀ V`.

The construction goes through the exterior *algebra*: the `k`-linear map

```
V → (⋀ V) ⊗ H,  v ↦ ∑ ι(v₍₀₎) ⊗ v₍₁₎
```

has square zero (here commutativity of `H` is used), hence extends to a homomorphism of
`k`-algebras `Λρ : ⋀ V → (⋀ V) ⊗ H`.  Coassociativity and counitality are then checked on the
generators, because all the maps in sight are algebra homomorphisms.

## Main definitions

* `Coalgebra.Comodule.extCoactAlgHom`: the coaction `Λρ` on the exterior algebra, as a homomorphism
  of `k`-algebras;
* `Coalgebra.Comodule.instRightComoduleExteriorAlgebra`: the comodule structure on `⋀ V`.

## Main results

* `Coalgebra.Comodule.coact_exteriorAlgebra`: the coaction of `⋀ V` is `Λρ`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Lemmas
  4.10 and 4.11
-/

@[expose] public section

open TensorProduct Coalgebra

section
open _root_.TensorProduct renaming map → tensorMap, rid → tensorRid, assoc → tensorAssoc

namespace Coalgebra.Comodule

universe u

variable {k H V : Type u} [Field k] [CommRing H] [Bialgebra k H]
  [AddCommGroup V] [Module k V]

variable (k H V) in
/-- The map `V ⊗ H → (⋀ V) ⊗ H` induced by the canonical inclusion `V → ⋀ V`. -/
noncomputable def extIota : V ⊗[k] H →ₗ[k] (ExteriorAlgebra k V) ⊗[k] H :=
  tensorMap (ExteriorAlgebra.ι k) LinearMap.id
/-- `extIota` on pure tensors: `v ⊗ h ↦ ι v ⊗ h`. -/
@[simp] lemma extIota_tmul (v : V) (h : H) :
    extIota k H V (v ⊗ₜ[k] h) = (ExteriorAlgebra.ι k v) ⊗ₜ[k] h := rfl

/-- Two elements of the image of `extIota` anticommute. -/
theorem extIota_anticomm (z w : V ⊗[k] H) :
    extIota k H V z * extIota k H V w + extIota k H V w * extIota k H V z = 0 := by
  induction z with
  | add a b ha hb =>
    have h : extIota k H V (a + b) * extIota k H V w + extIota k H V w * extIota k H V (a + b)
        = (extIota k H V a * extIota k H V w + extIota k H V w * extIota k H V a)
          + (extIota k H V b * extIota k H V w + extIota k H V w * extIota k H V b) := by
      rw [map_add, add_mul, mul_add]; abel
    rw [h, ha, hb, add_zero]
  | tmul v h =>
    induction w with
    | add a b ha hb =>
      have h' : extIota k H V (v ⊗ₜ h) * extIota k H V (a + b)
            + extIota k H V (a + b) * extIota k H V (v ⊗ₜ h)
          = (extIota k H V (v ⊗ₜ h) * extIota k H V a
              + extIota k H V a * extIota k H V (v ⊗ₜ h))
            + (extIota k H V (v ⊗ₜ h) * extIota k H V b
              + extIota k H V b * extIota k H V (v ⊗ₜ h)) := by
        rw [map_add, add_mul, mul_add]; abel
      rw [h', ha, hb, add_zero]
    | tmul v' h' =>
      simp only [extIota_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      rw [mul_comm h h', ← TensorProduct.add_tmul, ExteriorAlgebra.ι_add_mul_swap,
        TensorProduct.zero_tmul]

/-- Every element of the image of `extIota` squares to zero. -/
theorem extIota_sq (z : V ⊗[k] H) : extIota k H V z * extIota k H V z = 0 := by
  induction z with
  | add a b ha hb =>
    have h : extIota k H V (a + b) * extIota k H V (a + b)
        = extIota k H V a * extIota k H V a
          + (extIota k H V a * extIota k H V b + extIota k H V b * extIota k H V a)
          + extIota k H V b * extIota k H V b := by
      rw [map_add, add_mul, mul_add, mul_add]; abel
    rw [h, ha, hb, extIota_anticomm]; simp
  | tmul v h =>
    simp only [extIota_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      ExteriorAlgebra.ι_sq_zero, TensorProduct.zero_tmul]

/-- Compatibility of `comul` and `extIota` for `extCoactAlgHom_coassoc`. -/
private lemma extCoactAlgHom_coassoc_right (z : V ⊗[k] H) :
    (Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V)) (Bialgebra.comulAlgHom k H))
        (extIota k H V z) =
      tensorMap (ExteriorAlgebra.ι k) (LinearMap.id (R := k) (M := H ⊗[k] H))
        (LinearMap.lTensor V (comul (R := k) (A := H)) z) := by
  induction z with
  | tmul v h => simp
  | add p q hp hq => simp only [map_add, hp, hq]

variable [RightComodule k H V]

variable (k H V) in
/-- The coaction of the exterior algebra of a comodule, as a homomorphism of `k`-algebras. -/
noncomputable def extCoactAlgHom :
    ExteriorAlgebra k V →ₐ[k] (ExteriorAlgebra k V) ⊗[k] H :=
  ExteriorAlgebra.lift k ⟨(extIota k H V) ∘ₗ (coact (R := k) (C := H) (M := V)),
    fun _ => extIota_sq _⟩

/-- On generators `ι v`, `extCoactAlgHom` is the coaction of `v` followed by `ι ⊗ id`. -/
@[simp] lemma extCoactAlgHom_ι (v : V) :
    extCoactAlgHom k H V (ExteriorAlgebra.ι k v)
      = extIota k H V (coact (R := k) (C := H) v) := by
  simp [extCoactAlgHom]

/-! ### The comodule axioms -/

/-- Counitality on the exterior algebra. -/
theorem extCoactAlgHom_counit :
    (tensorRid k (ExteriorAlgebra k V)).toLinearMap ∘ₗ
        (LinearMap.lTensor (ExteriorAlgebra k V) (counit (R := k) (A := H))) ∘ₗ
        (extCoactAlgHom k H V).toLinearMap
      = LinearMap.id := by
  -- both sides are algebra homomorphisms, so it suffices to compare them on `ι v`
  set F : (ExteriorAlgebra k V) ⊗[k] H →ₐ[k] ExteriorAlgebra k V :=
    (Algebra.TensorProduct.rid k k (ExteriorAlgebra k V)).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V))
        (Bialgebra.counitAlgHom k H)) with hF
  have hFlin : ∀ z : (ExteriorAlgebra k V) ⊗[k] H,
      F z = (tensorRid k (ExteriorAlgebra k V))
        (LinearMap.lTensor (ExteriorAlgebra k V) (counit (R := k) (A := H)) z) := by
    intro z
    induction z with
    | tmul a h => simp [hF]
    | add p q hp hq => simp only [map_add, hp, hq]
  have hcomp : F.comp (extCoactAlgHom k H V) = AlgHom.id k (ExteriorAlgebra k V) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      AlgHom.id_apply]
    rw [extCoactAlgHom_ι, hFlin]
    -- reduce to the counit axiom of `V`
    have hcu : ∀ z : V ⊗[k] H,
        (tensorRid k (ExteriorAlgebra k V))
            (LinearMap.lTensor (ExteriorAlgebra k V) (counit (R := k) (A := H))
              (extIota k H V z))
          = ExteriorAlgebra.ι k
              ((tensorRid k V) (LinearMap.lTensor V (counit (R := k) (A := H)) z))
                  := by
      intro z
      induction z with
      | tmul v h => simp
      | add p q hp hq => simp only [map_add, hp, hq]
    rw [hcu]
    congr 1
    have hcu2 := congr($(Coalgebra.RightComodule.counit_coact (R := k) (C := H) (M := V)) v)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
      LinearEquiv.coe_coe] at hcu2
    exact hcu2
  refine LinearMap.ext fun x => ?_
  have hx := congr($hcomp x)
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq] at hx
  rw [hFlin] at hx
  simpa using hx

/-- Compatibility of the associator and `extIota` for `extCoactAlgHom_coassoc`. -/
private lemma extCoactAlgHom_coassoc_left (z : V ⊗[k] H) :
    (Algebra.TensorProduct.assoc k k k (ExteriorAlgebra k V) H H).toAlgHom
        (Algebra.TensorProduct.map (extCoactAlgHom k H V) (AlgHom.id k H) (extIota k H V z)) =
      tensorMap (ExteriorAlgebra.ι k) (LinearMap.id (R := k) (M := H ⊗[k] H))
        ((tensorAssoc k V H H)
          (LinearMap.rTensor H (coact (R := k) (C := H) (M := V)) z)) := by
  induction z with
  | tmul v h =>
    simp only [extIota_tmul, Algebra.TensorProduct.map_tmul, extCoactAlgHom_ι,
      AlgHom.coe_id, id_eq, LinearMap.rTensor_tmul]
    generalize coact (R := k) (C := H) (M := V) v = y
    induction y with
    | tmul w g => simp
    | add p q hp hq =>
      simp only [TensorProduct.add_tmul, map_add]
      exact congrArg₂ (· + ·) hp hq
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Transporting the left-hand algebra map of `extCoactAlgHom_coassoc` to linear maps. -/
private lemma extCoactAlgHom_coassoc_lhs (x : ExteriorAlgebra k V) :
    ((Algebra.TensorProduct.assoc k k k (ExteriorAlgebra k V) H H).toAlgHom.comp
      ((Algebra.TensorProduct.map (extCoactAlgHom k H V) (AlgHom.id k H)).comp
        (extCoactAlgHom k H V))) x =
      (tensorAssoc k (ExteriorAlgebra k V) H H)
        (LinearMap.rTensor H (extCoactAlgHom k H V).toLinearMap (extCoactAlgHom k H V x)) := by
  have haux : ∀ z : (ExteriorAlgebra k V) ⊗[k] H,
      (Algebra.TensorProduct.assoc k k k (ExteriorAlgebra k V) H H).toAlgHom
          (Algebra.TensorProduct.map (extCoactAlgHom k H V) (AlgHom.id k H) z) =
        (tensorAssoc k (ExteriorAlgebra k V) H H)
          (LinearMap.rTensor H (extCoactAlgHom k H V).toLinearMap z) := by
    intro z
    induction z with
    | tmul a h =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply]
      generalize extCoactAlgHom k H V a = y
      induction y with
      | tmul b g => simp
      | add p q hp hq =>
        simp only [TensorProduct.add_tmul, map_add]
        exact congrArg₂ (· + ·) hp hq
    | add p q hp hq => simp only [map_add, hp, hq]
  simp only [AlgHom.coe_comp, Function.comp_apply]
  rw [haux]

/-- Transporting the right-hand algebra map of `extCoactAlgHom_coassoc` to linear maps. -/
private lemma extCoactAlgHom_coassoc_rhs (x : ExteriorAlgebra k V) :
    ((Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V))
      (Bialgebra.comulAlgHom k H)).comp (extCoactAlgHom k H V)) x =
      LinearMap.lTensor (ExteriorAlgebra k V) (comul (R := k) (A := H))
        (extCoactAlgHom k H V x) := by
  have haux : ∀ z : (ExteriorAlgebra k V) ⊗[k] H,
      (Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V))
          (Bialgebra.comulAlgHom k H)) z =
        LinearMap.lTensor (ExteriorAlgebra k V) (comul (R := k) (A := H)) z := by
    intro z
    induction z with
    | tmul a h => simp
    | add p q hp hq => simp only [map_add, hp, hq]
  simp only [AlgHom.coe_comp, Function.comp_apply]
  rw [haux]

/-- Coassociativity on the exterior algebra. -/
theorem extCoactAlgHom_coassoc :
    (tensorAssoc k (ExteriorAlgebra k V) H H).toLinearMap ∘ₗ
        (LinearMap.rTensor H (extCoactAlgHom k H V).toLinearMap) ∘ₗ
        (extCoactAlgHom k H V).toLinearMap
      = (LinearMap.lTensor (ExteriorAlgebra k V) (comul (R := k) (A := H))) ∘ₗ
        (extCoactAlgHom k H V).toLinearMap := by
  set L : ExteriorAlgebra k V →ₐ[k] (ExteriorAlgebra k V) ⊗[k] (H ⊗[k] H) :=
    ((Algebra.TensorProduct.assoc k k k (ExteriorAlgebra k V) H H).toAlgHom.comp
      ((Algebra.TensorProduct.map (extCoactAlgHom k H V) (AlgHom.id k H)).comp
        (extCoactAlgHom k H V)))
  set R : ExteriorAlgebra k V →ₐ[k] (ExteriorAlgebra k V) ⊗[k] (H ⊗[k] H) :=
    ((Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V))
      (Bialgebra.comulAlgHom k H)).comp (extCoactAlgHom k H V))
  have hgen : L = R := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, L, R, AlgHom.comp_apply]
    rw [extCoactAlgHom_ι, extCoactAlgHom_coassoc_left, extCoactAlgHom_coassoc_right]
    congr 1
    have hca := congr($(Coalgebra.RightComodule.coassoc (R := k) (C := H) (M := V)) v)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hca
    exact hca
  refine LinearMap.ext fun x => ?_
  have hx := congr($hgen x)
  rw [extCoactAlgHom_coassoc_lhs, extCoactAlgHom_coassoc_rhs] at hx
  simpa using hx

/-- **The exterior algebra of a comodule is a comodule.** -/
noncomputable instance instRightComoduleExteriorAlgebra :
    RightComodule k H (ExteriorAlgebra k V) where
  coact := (extCoactAlgHom k H V).toLinearMap
  coassoc := extCoactAlgHom_coassoc
  counit_coact := extCoactAlgHom_counit

/-- The coaction of the comodule `⋀ V` is `extCoactAlgHom`. -/
@[simp] lemma coact_exteriorAlgebra (x : ExteriorAlgebra k V) :
    coact (R := k) (C := H) x = extCoactAlgHom k H V x := rfl

end Coalgebra.Comodule
end
