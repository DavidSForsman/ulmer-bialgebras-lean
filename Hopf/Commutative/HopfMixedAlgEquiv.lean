module

public import Hopf.Commutative.HopfMixedTensorQuot
public import Hopf.Basic.CoalgebraReprMul

/-!
# Takeuchi's Lemma 3.9 is an isomorphism of algebras

`Hopf/Commutative/HopfMixedTensorQuot.lean` constructs, for Hopf algebra maps `A → K → H` over
a field `k`, the `A`-linear isomorphism

`Φ : K ⊗[A] H ≅ H ⊗[k] (K / A⁺K)`,  `x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]`.

Here we show that `Φ` is multiplicative and unital, so that it is an isomorphism of `k`-algebras
(`HopfAlgebra.Commutative.mixedTensorAlgEquiv`). This is what makes it usable for transporting
faithful flatness in Takeuchi's proof of Theorem 3.1.

## Main results

* `HopfAlgebra.Commutative.mixedTensorAlgEquiv`: an isomorphism of `k`-algebras
  `K ⊗[A] H ≃ₐ[k] H ⊗[k] (K / A⁺K)` (Takeuchi's Lemma 3.9).
* `HopfAlgebra.Commutative.mixedTensorAlgEquiv_apply`: it agrees with the map
  `HopfAlgebra.Commutative.mixedTensor`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Lemma 3.9, Theorem 3.1
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra

variable {k A K H : Type*} [Field k] [CommRing A] [CommRing K] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k K] [HopfAlgebra k H]
  [Algebra A K]

variable (j : K →ₐc[k] H)

/-- The trivial Sweedler representation of `1`. -/
noncomputable def oneRepr : Coalgebra.Repr k (1 : K) Unit where
  index := {()}
  left := fun _ => 1
  right := fun _ => 1
  eq := by simp [Algebra.TensorProduct.one_def]

/-- `mixedQuot` sends `1 ⊗ 1` to `1`. -/
lemma mixedQuot_one_tmul_one : mixedQuot k A K H j ((1 : K) ⊗ₜ[k] (1 : H)) = 1 := by
  rw [mixedQuot_tmul j 1 1 (oneRepr (k := k) (K := K))]
  simp only [oneRepr, Finset.sum_singleton, map_one, mul_one]
  exact (Algebra.TensorProduct.one_def (R := k) (A := H) (B := QuotAug k A K)).symm

/-- Multiplicativity of `Φ` on pure tensors. -/
lemma mixedQuot_tmul_mul_tmul (x x' : K) (y y' : H) :
    mixedQuot k A K H j ((x * x') ⊗ₜ[k] (y * y'))
      = mixedQuot k A K H j (x ⊗ₜ[k] y) * mixedQuot k A K H j (x' ⊗ₜ[k] y') := by
  classical
  rw [mixedQuot_tmul j (x * x') (y * y') (((ℛ k x).mul (ℛ k x'))),
    mixedQuot_tmul j x y (ℛ k x), mixedQuot_tmul j x' y' (ℛ k x'),
    Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  congr 1
  · simp only [Coalgebra.Repr.mul_right, map_mul]; ring

variable [Algebra A H] [IsScalarTower k A K] [IsScalarTower k A H]

variable (fAK : A →ₐc[k] K) (halgK : ∀ a, algebraMap A K a = fAK a)
  (halgH : ∀ a, algebraMap A H a = j (fAK a))

include halgK halgH

/-- `Φ` is multiplicative. -/
lemma mixedTensor_mul (u v : K ⊗[A] H) :
    mixedTensor j fAK halgK halgH (u * v)
      = mixedTensor j fAK halgK halgH u * mixedTensor j fAK halgK halgH v := by
  induction u using TensorProduct.inductionOn with
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | tmul x' y' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mixedTensor_tmul, mixedTensor_tmul,
        mixedTensor_tmul, mixedQuot_tmul_mul_tmul]
    | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, mul_add]
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_mul]

/-- `Φ` preserves the unit. -/
lemma mixedTensor_one :
    mixedTensor j fAK halgK halgH (1 : K ⊗[A] H) = 1 := by
  rw [Algebra.TensorProduct.one_def, mixedTensor_tmul, mixedQuot_one_tmul_one]

/-- **Takeuchi's Lemma 3.9 as an isomorphism of algebras** ([Takeuchi1972]):
`K ⊗[A] H ≃ₐ[k] H ⊗[k] (K / A⁺K)`. -/
noncomputable def mixedTensorAlgEquiv : (K ⊗[A] H) ≃ₐ[k] H ⊗[k] QuotAug k A K :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap ((mixedTensor j fAK halgK halgH).restrictScalars k)
      (mixedTensor_one j fAK halgK halgH) (mixedTensor_mul j fAK halgK halgH))
    (mixedTensorEquiv j fAK halgK halgH).bijective

/-- The algebra isomorphism `mixedTensorAlgEquiv` agrees with the map `mixedTensor`. -/
@[simp] lemma mixedTensorAlgEquiv_apply (u : K ⊗[A] H) :
    mixedTensorAlgEquiv j fAK halgK halgH u = mixedTensor j fAK halgK halgH u := rfl

end HopfAlgebra.Commutative
end
