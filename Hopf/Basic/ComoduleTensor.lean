module

public import Hopf.Basic.Comodule
public import Hopf.Basic.CoalgebraReprMul

/-!
# Tensor products and quotients of comodules

Two general constructions of comodules, needed for §2 of Takeuchi's paper
(*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972)).

* the tensor product `M ⊗[k] N` of two right `C`-comodules over a *bialgebra* `C` is again a
  right `C`-comodule, with the diagonal coaction `m ⊗ n ↦ ∑ (m₍₀₎ ⊗ n₍₀₎) ⊗ m₍₁₎n₍₁₎`;
* a quotient of a comodule by a surjection carrying a compatible coaction is a comodule.

## Main definitions

* `Coalgebra.Comodule.tensorCoact`: the diagonal coaction on `M ⊗[k] N`;
* `Coalgebra.Comodule.tensorComodule`: the resulting comodule structure;
* `Coalgebra.RightComodule.ofSurjective`: the comodule structure transported along a surjection.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Section
  2
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter II
-/

@[expose] public section

section
open TensorProduct Coalgebra Coalgebra.Comodule

open _root_.TensorProduct renaming map → tensorMap, rid → tensorRid, rid_tmul → tensorRid_tmul,
  assoc → tensorAssoc, assoc_tmul → tensorAssoc_tmul

namespace Coalgebra.Comodule

section Tensor

variable {k C M N : Type*} [CommSemiring k] [Semiring C] [Bialgebra k C]
  [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]

variable (k C) in
/-- The `k`-linear map `(C ⊗ C) ⊗ (C ⊗ C) → C ⊗ C`, `(a ⊗ b) ⊗ (c ⊗ d) ↦ (a * c) ⊗ (b * d)`. -/
noncomputable def mul22 : (C ⊗[k] C) ⊗[k] (C ⊗[k] C) →ₗ[k] C ⊗[k] C :=
  (tensorMap (LinearMap.mul' k C) (LinearMap.mul' k C)) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k C C C C).toLinearMap

variable (k C M N) in
/-- The shuffle map `(M ⊗ (C ⊗ C)) ⊗ (N ⊗ (C ⊗ C)) → (M ⊗ N) ⊗ (C ⊗ C)`,
`(m ⊗ (a ⊗ b)) ⊗ (n ⊗ (c ⊗ d)) ↦ (m ⊗ n) ⊗ ((a * c) ⊗ (b * d))`. -/
noncomputable def shuffle22 :
    (M ⊗[k] (C ⊗[k] C)) ⊗[k] (N ⊗[k] (C ⊗[k] C)) →ₗ[k] (M ⊗[k] N) ⊗[k] (C ⊗[k] C) :=
  (LinearMap.lTensor (M ⊗[k] N) (mul22 k C)) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k M (C ⊗[k] C) N (C ⊗[k] C)).toLinearMap

/-- The shuffle map applied to a pair of double sums of pure tensors. -/
lemma shuffle22_sum {ι κ : Type*} {ι' : ι → Type*} {κ' : κ → Type*}
    (I : Finset ι) (J : Finset κ) (P : (i : ι) → Finset (ι' i)) (Q : (j : κ) → Finset (κ' j))
    (f : (i : ι) → ι' i → M) (g h : (i : ι) → ι' i → C)
    (f' : (j : κ) → κ' j → N) (g' h' : (j : κ) → κ' j → C) :
    shuffle22 k C M N ((∑ i ∈ I, ∑ p ∈ P i, f i p ⊗ₜ[k] (g i p ⊗ₜ[k] h i p)) ⊗ₜ[k]
      (∑ j ∈ J, ∑ q ∈ Q j, f' j q ⊗ₜ[k] (g' j q ⊗ₜ[k] h' j q)))
      = ∑ i ∈ I, ∑ j ∈ J, ∑ p ∈ P i, ∑ q ∈ Q j,
          (f i p ⊗ₜ[k] f' j q) ⊗ₜ[k] ((g i p * g' j q) ⊗ₜ[k] (h i p * h' j q)) := by
  rw [TensorProduct.sum_tmul, map_sum (shuffle22 k C M N)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, TensorProduct.sum_tmul, map_sum (shuffle22 k C M N)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [TensorProduct.tmul_sum, map_sum (shuffle22 k C M N)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.tmul_sum, map_sum (shuffle22 k C M N)]
  exact Finset.sum_congr rfl fun q _ => rfl

variable [RightComodule k C M] [RightComodule k C N]

variable (k C M N) in
/-- The diagonal coaction `m ⊗ n ↦ ∑ (m₍₀₎ ⊗ n₍₀₎) ⊗ m₍₁₎n₍₁₎` on the tensor product of two
right `C`-comodules over a bialgebra `C`. -/
noncomputable def tensorCoact : (M ⊗[k] N) →ₗ[k] (M ⊗[k] N) ⊗[k] C :=
  (LinearMap.lTensor (M ⊗[k] N) (LinearMap.mul' k C)) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k M C N C).toLinearMap ∘ₗ
    (tensorMap (coact (R := k) (C := C)) (coact (R := k) (C := C)))

/-- The diagonal coaction in Sweedler form. -/
lemma tensorCoact_tmul_repr {m : M} {n : N} (rm : Repr k C m) (rn : Repr k C n) :
    tensorCoact k C M N (m ⊗ₜ[k] n)
      = ∑ i ∈ rm.index, ∑ j ∈ rn.index,
          (rm.left i ⊗ₜ[k] rn.left j) ⊗ₜ[k] (rm.right i * rn.right j) := by
  change (LinearMap.lTensor (M ⊗[k] N) (LinearMap.mul' k C))
      ((TensorProduct.tensorTensorTensorComm k M C N C)
        ((coact (R := k) (C := C) m) ⊗ₜ[k] (coact (R := k) (C := C) n))) = _
  rw [← rm.eq, ← rn.eq, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl

/-- Coassociativity of the diagonal coaction `tensorCoact k C M N`. -/
lemma tensorCoact_coassoc :
    tensorAssoc k (M ⊗[k] N) C C ∘ₗ
        LinearMap.rTensor C (tensorCoact k C M N) ∘ₗ tensorCoact k C M N =
      LinearMap.lTensor (M ⊗[k] N) (comul (R := k) (A := C)) ∘ₗ tensorCoact k C M N := by
  classical
  apply TensorProduct.ext'
  intro m n
  set rm := Repr.arbitrary k C m
  set rn := Repr.arbitrary k C n
  let am : (i : rm.ι) → Repr k C (rm.left i) := fun i => Repr.arbitrary k C (rm.left i)
  let an : (j : rn.ι) → Repr k C (rn.left j) := fun j => Repr.arbitrary k C (rn.left j)
  let bm : (i : rm.ι) → Coalgebra.Repr k (rm.right i) (C × C) := fun i => ℛ k (rm.right i)
  let bn : (j : rn.ι) → Coalgebra.Repr k (rn.right j) (C × C) := fun j => ℛ k (rn.right j)
  set XM : M ⊗[k] (C ⊗[k] C) := ∑ i ∈ rm.index, ∑ p ∈ (am i).index,
    (am i).left p ⊗ₜ[k] ((am i).right p ⊗ₜ[k] rm.right i) with hXM
  set XN : N ⊗[k] (C ⊗[k] C) := ∑ j ∈ rn.index, ∑ q ∈ (an j).index,
    (an j).left q ⊗ₜ[k] ((an j).right q ⊗ₜ[k] rn.right j) with hXN
  set YM : M ⊗[k] (C ⊗[k] C) := ∑ i ∈ rm.index, ∑ u ∈ (bm i).index,
    rm.left i ⊗ₜ[k] ((bm i).left u ⊗ₜ[k] (bm i).right u) with hYM
  set YN : N ⊗[k] (C ⊗[k] C) := ∑ j ∈ rn.index, ∑ v ∈ (bn j).index,
    rn.left j ⊗ₜ[k] ((bn j).left v ⊗ₜ[k] (bn j).right v) with hYN
  have hL : (tensorAssoc k (M ⊗[k] N) C C)
        ((LinearMap.rTensor C (tensorCoact k C M N)) (tensorCoact k C M N (m ⊗ₜ[k] n)))
      = shuffle22 k C M N (XM ⊗ₜ[k] XN) := by
    rw [hXM, hXN, shuffle22_sum, tensorCoact_tmul_repr rm rn]
    simp only [map_sum, LinearMap.rTensor_tmul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [tensorCoact_tmul_repr (am i) (an j)]
    simp only [TensorProduct.sum_tmul, map_sum, tensorAssoc_tmul]
  have hR : (LinearMap.lTensor (M ⊗[k] N) (comul (R := k) (A := C)))
        (tensorCoact k C M N (m ⊗ₜ[k] n)) = shuffle22 k C M N (YM ⊗ₜ[k] YN) := by
    rw [hYM, hYN, shuffle22_sum, tensorCoact_tmul_repr rm rn]
    simp only [map_sum, LinearMap.lTensor_tmul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show comul (R := k) (rm.right i * rn.right j)
        = ∑ u ∈ (bm i).index, ∑ v ∈ (bn j).index,
          ((bm i).left u * (bn j).left v) ⊗ₜ[k] ((bm i).right u * (bn j).right v) from by
      rw [← ((bm i).mul (bn j)).eq]
      simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left, Coalgebra.Repr.mul_right]
      rw [← Finset.sum_product']]
    simp only [TensorProduct.tmul_sum]
  have hXYM : XM = YM := sum_tmul_tmul_eq rm am bm
  have hXYN : XN = YN := sum_tmul_tmul_eq rn an bn
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [hL, hR, hXYM, hXYN]

variable (k C M N) in
/-- The tensor product of two right comodules over a bialgebra is a right comodule, with the
diagonal coaction. -/
@[instance_reducible]
noncomputable def tensorComodule : RightComodule k C (M ⊗[k] N) where
  coact := tensorCoact k C M N
  coassoc := tensorCoact_coassoc
  counit_coact := by
    classical
    apply TensorProduct.ext'
    intro m n
    set rm := Repr.arbitrary k C m with hrm
    set rn := Repr.arbitrary k C n with hrn
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    rw [tensorCoact_tmul_repr rm rn]
    simp only [map_sum, LinearMap.lTensor_tmul, tensorRid_tmul, Bialgebra.counit_mul,
      LinearEquiv.coe_coe]
    have h : ∀ i ∈ rm.index, ∑ j ∈ rn.index,
        (counit (R := k) (rm.right i) * counit (R := k) (rn.right j)) •
          (rm.left i ⊗ₜ[k] rn.left j)
        = (counit (R := k) (rm.right i) • rm.left i) ⊗ₜ[k] n := by
      intro i _
      conv_rhs => rw [← sum_counit_smul rn]
      rw [TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          ← mul_smul, mul_comm]
    rw [Finset.sum_congr rfl h, ← TensorProduct.sum_tmul, sum_counit_smul rm]

end Tensor

end Coalgebra.Comodule

namespace Coalgebra.RightComodule

open Coalgebra.Comodule

section OfSurjective

variable {k C M Q : Type*} [CommSemiring k] [AddCommMonoid C] [Module k C] [CoalgebraStruct k C]
  [AddCommMonoid M] [Module k M] [AddCommMonoid Q] [Module k Q] [RightComodule k C M]

/-- A quotient of a comodule carrying a compatible coaction is a comodule. -/
@[instance_reducible]
noncomputable def ofSurjective (q : M →ₗ[k] Q) (hq : Function.Surjective q)
    (rho : Q →ₗ[k] Q ⊗[k] C)
    (hcompat : ∀ x : M, rho (q x) = (LinearMap.rTensor C q) (coact (R := k) (C := C) x)) :
    RightComodule k C Q where
  coact := rho
  coassoc := by
    have h1 : ∀ u : M ⊗[k] C,
        (LinearMap.rTensor C rho) ((LinearMap.rTensor C q) u)
          = (LinearMap.rTensor C (LinearMap.rTensor C q))
              ((LinearMap.rTensor C (coact (R := k) (C := C))) u) := by
      intro u
      induction u with
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul x c => simp [hcompat x]
    have h2 : (tensorAssoc k Q C C).toLinearMap ∘ₗ
          (LinearMap.rTensor C (LinearMap.rTensor C q))
        = (LinearMap.rTensor (C ⊗[k] C) q) ∘ₗ (tensorAssoc k M C C).toLinearMap := by
      ext x c d
      simp
    have h3 : (LinearMap.lTensor Q (comul (R := k) (A := C))) ∘ₗ (LinearMap.rTensor C q)
        = (LinearMap.rTensor (C ⊗[k] C) q) ∘ₗ
            (LinearMap.lTensor M (comul (R := k) (A := C))) := by
      ext x c
      simp
    ext z
    obtain ⟨t, rfl⟩ := hq z
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hcompat t, h1]
    have e2 := congr($h2 ((LinearMap.rTensor C (coact (R := k) (C := C))) (coact (R := k) t)))
    have e3 := congr($h3 (coact (R := k) (C := C) t))
    simp only [LinearMap.coe_comp, Function.comp_apply] at e2 e3
    rw [e2, e3]
    congr 1
    exact congr($(Coalgebra.RightComodule.coassoc (R := k) (C := C) (M := M)) t)
  counit_coact := by
    have h : (tensorRid k Q).toLinearMap ∘ₗ
          (LinearMap.lTensor Q (counit (R := k) (A := C))) ∘ₗ (LinearMap.rTensor C q)
        = q ∘ₗ (tensorRid k M).toLinearMap ∘ₗ
            (LinearMap.lTensor M (counit (R := k) (A := C))) := by
      ext x c
      simp
    ext z
    obtain ⟨t, rfl⟩ := hq z
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    rw [hcompat t]
    have e := congr($h (coact (R := k) (C := C) t))
    simp only [LinearMap.coe_comp, Function.comp_apply] at e
    rw [e]
    congr 1
    exact congr($(Coalgebra.RightComodule.counit_coact (R := k) (C := C) (M := M)) t)

end OfSurjective

end Coalgebra.RightComodule

end
