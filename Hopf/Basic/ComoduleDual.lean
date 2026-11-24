module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Hopf.Basic.Comodule
public import Hopf.Basic.HopfAdjointCoaction

/-!
# The dual of a finite-dimensional comodule

Let `C` be a commutative Hopf algebra over a field `k` and let `M` be a **finite-dimensional**
right `C`-comodule with coaction `ρ m = ∑ m₍₀₎ ⊗ m₍₁₎`.  The dual space `M*` is again a right
`C`-comodule, with the coaction characterised by

`∑ f₍₀₎ (m) f₍₁₎ = ∑ f (m₍₀₎) S (m₍₁₎)`,

the antipode entering because the dual of a right comodule is naturally a *left* comodule.  This
is Sweedler's Lemma 5.1.4, quoted by M. Takeuchi in the proof of Lemma 4.15 of *A correspondence
between Hopf ideals and sub-Hopf algebras* (manuscripta math. **7** (1972), 251–270).

## Main definitions

* `Coalgebra.Comodule.dualCoactHom f`: the linear map `m ↦ ∑ f (m₍₀₎) S (m₍₁₎)`, the image of the
  coaction of `f` under the isomorphism `M* ⊗ C ≃ Hom(M, C)`;
* `Coalgebra.Comodule.dualCoact`: the coaction on `M*`;
* `Coalgebra.Comodule.dualComodule`: the resulting right comodule structure on `M*`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Lemma 5.1.4
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Lemma
  4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra Coalgebra.Comodule

open _root_.TensorProduct renaming map → tensorMap, map_tmul → tensorMap_tmul,
  rid → tensorRid, assoc → tensorAssoc

namespace Coalgebra.Comodule

universe u

variable {k C M : Type u} [Field k] [CommRing C] [HopfAlgebra k C]
  [AddCommGroup M] [Module k M]

/-- The canonical map `M* ⊗ N → Hom (M, N)` is injective (`M` finite-dimensional). -/
lemma dualTensorHom_injective [FiniteDimensional k M] (N : Type u) [AddCommGroup N] [Module k N] :
    Function.Injective (dualTensorHom k M N) := by
  have h : (dualTensorHomEquiv k M N).toLinearMap = dualTensorHom k M N := by
    ext f c m
    simp
  rw [← h]
  exact (dualTensorHomEquiv k M N).injective

/-! ### Auxiliary computations -/

/-- Evaluation of `dualTensorHom` after re-associating a tensor. -/
lemma dualTensorHom_assoc_tmul (Z : Module.Dual k M ⊗[k] C) (c : C) (m : M) :
    dualTensorHom k M (C ⊗[k] C)
        ((tensorAssoc k (Module.Dual k M) C C) (Z ⊗ₜ[k] c)) m
      = (dualTensorHom k M C Z m) ⊗ₜ[k] c := by
  induction Z with
  | tmul f c' => simp [TensorProduct.smul_tmul']
  | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add, map_add, LinearMap.add_apply, hp, hq, map_add,
        LinearMap.add_apply, TensorProduct.add_tmul]

/-- Evaluation of `dualTensorHom` after applying a linear map in the second factor. -/
lemma dualTensorHom_lTensor {N : Type u} [AddCommGroup N] [Module k N] (φ : C →ₗ[k] N)
    (Y : Module.Dual k M ⊗[k] C) (m : M) :
    dualTensorHom k M N ((LinearMap.lTensor (Module.Dual k M) φ) Y) m
      = φ (dualTensorHom k M C Y m) := by
  induction Y with
  | tmul f c => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]

/-- Evaluation of `dualTensorHom` after applying the comultiplication in the second factor. -/
lemma dualTensorHom_lTensor_comul (Y : Module.Dual k M ⊗[k] C) (m : M) :
    dualTensorHom k M (C ⊗[k] C)
        ((LinearMap.lTensor (Module.Dual k M) (comul (R := k) (A := C))) Y) m
      = comul (R := k) (A := C) (dualTensorHom k M C Y m) :=
  dualTensorHom_lTensor (N := C ⊗[k] C) (comul (R := k) (A := C)) Y m

/-- Evaluation of `dualTensorHom` after applying the counit in the second factor. -/
lemma rid_lTensor_counit (Y : Module.Dual k M ⊗[k] C) (m : M) :
    (tensorRid k (Module.Dual k M))
        ((LinearMap.lTensor (Module.Dual k M) (counit (R := k) (A := C))) Y) m
      = counit (R := k) (A := C) (dualTensorHom k M C Y m) := by
  induction Y with
  | tmul f c => simp [mul_comm]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]

variable [RightComodule k C M]

/-! ### The comparison map `M* → Hom(M, C)` -/

/-- The linear map `m ↦ ∑ f (m₍₀₎) S (m₍₁₎)` attached to a functional `f` on a right
`C`-comodule.  Under the isomorphism `M* ⊗ C ≃ Hom (M, C)` of a finite-dimensional comodule this
is the coaction of `f` in the dual comodule. -/
noncomputable def dualCoactHom (f : Module.Dual k M) : M →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap ∘ₗ
    (tensorMap f (antipode k (A := C))) ∘ₗ coact (R := k) (C := C)

/-- On a Sweedler representation of `m`: `dualCoactHom f m = ∑ f (m₍₀₎) • S (m₍₁₎)`. -/
lemma dualCoactHom_apply_repr (f : Module.Dual k M) {m : M} (r : Repr k C m) :
    dualCoactHom f m = ∑ i ∈ r.index, f (r.left i) • antipode k (r.right i) := by
  rw [dualCoactHom]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [← r.eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

variable (k M) in
/-- The map `f ↦ (m ↦ ∑ f (m₍₀₎) S (m₍₁₎))`, as a linear map. -/
noncomputable def dualCoactHomₗ : Module.Dual k M →ₗ[k] (M →ₗ[k] C) where
  toFun := dualCoactHom
  map_add' f g := by
    ext m
    classical
    rw [LinearMap.add_apply, dualCoactHom_apply_repr _ (Repr.arbitrary k C m),
      dualCoactHom_apply_repr _ (Repr.arbitrary k C m),
      dualCoactHom_apply_repr _ (Repr.arbitrary k C m), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.add_apply, add_smul]
  map_smul' a f := by
    ext m
    classical
    rw [RingHom.id_apply, LinearMap.smul_apply, dualCoactHom_apply_repr _ (Repr.arbitrary k C m),
      dualCoactHom_apply_repr _ (Repr.arbitrary k C m), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, smul_assoc]
/-- `dualCoactHomₗ k M f` is `dualCoactHom f`. -/
@[simp] lemma dualCoactHomₗ_apply (f : Module.Dual k M) :
    dualCoactHomₗ k M f = dualCoactHom (C := C) f := rfl

/-- The Sweedler-form identity behind coassociativity of the dual coaction:
`∑ S (m₍₂₎) ⊗ S (m₍₁₎)` computed in two ways. -/
lemma comm_map_dualCoactHom (f : Module.Dual k M) (m : M) :
    (TensorProduct.comm k C C)
        ((tensorMap (dualCoactHom (C := C) f) (antipode k (A := C)))
          (coact (R := k) (C := C) m))
      = comul (R := k) (A := C) (dualCoactHom (C := C) f m) := by
  classical
  set r := Repr.arbitrary k C m with hr
  set a : (i : r.ι) → Repr k C (r.left i) := fun i => Repr.arbitrary k C (r.left i) with ha
  set b : (i : r.ι) → Coalgebra.Repr k (r.right i) (C × C) := fun i => ℛ k (r.right i) with hb
  -- the linear map `x ⊗ (u ⊗ v) ↦ f x • (S v ⊗ S u)`
  set Φ : M ⊗[k] (C ⊗[k] C) →ₗ[k] C ⊗[k] C :=
    (TensorProduct.lid k (C ⊗[k] C)).toLinearMap ∘ₗ
      (tensorMap f ((TensorProduct.comm k C C).toLinearMap ∘ₗ
        (tensorMap (antipode k (A := C)) (antipode k (A := C))))) with hΦ
  have hΦ_tmul : ∀ (x : M) (u v : C),
      Φ (x ⊗ₜ[k] (u ⊗ₜ[k] v)) = f x • (antipode k v ⊗ₜ[k] antipode k u) := by
    intro x u v
    simp [hΦ]
  have hcoassoc := sum_tmul_tmul_eq r a b
  -- the two sides of the coassociativity identity, pushed through `Φ`
  have hΦX : Φ (∑ i ∈ r.index, ∑ j ∈ (a i).index,
        (a i).left j ⊗ₜ[k] ((a i).right j ⊗ₜ[k] r.right i))
      = ∑ i ∈ r.index, ∑ j ∈ (a i).index,
          f ((a i).left j) • (antipode k (r.right i) ⊗ₜ[k] antipode k ((a i).right j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hΦ_tmul _ _ _
  have hΦY : Φ (∑ i ∈ r.index, ∑ j ∈ (b i).index,
        r.left i ⊗ₜ[k] ((b i).left j ⊗ₜ[k] (b i).right j))
      = ∑ i ∈ r.index, ∑ j ∈ (b i).index,
          f (r.left i) • (antipode k ((b i).right j) ⊗ₜ[k] antipode k ((b i).left j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hΦ_tmul _ _ _
  have hL : (TensorProduct.comm k C C)
      ((tensorMap (dualCoactHom (C := C) f) (antipode k (A := C)))
        (coact (R := k) (C := C) m))
      = ∑ i ∈ r.index, ∑ j ∈ (a i).index,
          f ((a i).left j) • (antipode k (r.right i) ⊗ₜ[k] antipode k ((a i).right j)) := by
    rw [← r.eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensorMap_tmul, dualCoactHom_apply_repr f (a i), TensorProduct.sum_tmul,
        map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have hR : comul (R := k) (A := C) (dualCoactHom (C := C) f m)
      = ∑ i ∈ r.index, ∑ j ∈ (b i).index,
          f (r.left i) • (antipode k ((b i).right j) ⊗ₜ[k] antipode k ((b i).left j)) := by
    rw [dualCoactHom_apply_repr f r, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, HopfAlgebra.comul_antipode_apply (r.right i) (b i), Finset.smul_sum]
  rw [hL, hR, ← hΦX, ← hΦY, hcoassoc]

/-! ### The coaction on the dual -/

variable [FiniteDimensional k M]

variable (k M) in
/-- The coaction of the dual comodule `M*` of a finite-dimensional right `C`-comodule `M`. -/
noncomputable def dualCoact : Module.Dual k M →ₗ[k] (Module.Dual k M) ⊗[k] C :=
  (dualTensorHomEquiv k M C).symm.toLinearMap ∘ₗ dualCoactHomₗ k M

/-- The defining property of the dual coaction: it corresponds to `dualCoactHom` under the
isomorphism `M* ⊗ C ≃ Hom (M, C)`. -/
@[simp] lemma dualTensorHom_dualCoact (f : Module.Dual k M) :
    dualTensorHom k M C (dualCoact k M f) = dualCoactHom (C := C) f := by
  have h : (dualTensorHomEquiv k M C) ((dualTensorHomEquiv k M C).symm (dualCoactHom f))
      = dualCoactHom (C := C) f := (dualTensorHomEquiv k M C).apply_symm_apply _
  simp [dualCoact] at h ⊢

/-- The coaction of the dual, computed through the isomorphism with `Hom (M, C)`. -/
lemma dualTensorHom_rTensor_dualCoact (Y : Module.Dual k M ⊗[k] C) (m : M) :
    dualTensorHom k M (C ⊗[k] C)
        ((tensorAssoc k (Module.Dual k M) C C)
          ((LinearMap.rTensor C (dualCoact k M)) Y)) m
      = (TensorProduct.comm k C C)
          ((tensorMap (dualTensorHom k M C Y) (antipode k (A := C)))
            (coact (R := k) (C := C) m)) := by
  classical
  induction Y with
  | tmul f c =>
      rw [LinearMap.rTensor_tmul, dualTensorHom_assoc_tmul, dualTensorHom_dualCoact]
      set r := Repr.arbitrary k C m with hr
      rw [dualCoactHom_apply_repr f r, ← r.eq, map_sum, map_sum]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [TensorProduct.smul_tmul']
  | add p q hp hq =>
      simp only [map_add, LinearMap.add_apply, hp, hq, TensorProduct.map_add_left,
        LinearMap.add_apply, map_add]

/-! ### The dual comodule -/

variable (k M) in
/-- **The dual of a finite-dimensional right comodule is a right comodule** (Sweedler's
Lemma 5.1.4 [Sweedler]), with coaction determined by `∑ f₍₀₎ (m) f₍₁₎ = ∑ f (m₍₀₎) S (m₍₁₎)`. -/
@[instance_reducible]
noncomputable def dualComodule : RightComodule k C (Module.Dual k M) where
  coact := dualCoact k M
  coassoc := by
    ext f
    refine dualTensorHom_injective (M := M) (k := k) (C ⊗[k] C) ?_
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [dualTensorHom_rTensor_dualCoact, dualTensorHom_lTensor_comul, dualTensorHom_dualCoact,
      comm_map_dualCoactHom]
  counit_coact := by
    ext f m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.id_coe,
      id_eq]
    rw [rid_lTensor_counit, dualTensorHom_dualCoact]
    classical
    set r := Repr.arbitrary k C m with hr
    rw [dualCoactHom_apply_repr f r, map_sum]
    rw [show ∑ i ∈ r.index, counit (R := k) (A := C) (f (r.left i) • antipode k (r.right i))
        = f (∑ i ∈ r.index, counit (R := k) (A := C) (r.right i) • r.left i) from by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, HopfAlgebra.counit_antipode, smul_eq_mul, mul_comm]]
    rw [sum_counit_smul r]

end Coalgebra.Comodule

end
