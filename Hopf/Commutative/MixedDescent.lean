module

public import Hopf.Commutative.HopfMixedAlgEquiv
public import Hopf.Commutative.HopfMixedSquare
public import Foundations.RingTheory.FaithfullyFlatMixedDescent

/-!
# Takeuchi's descent step: from `A ⊆ H` and `K/A⁺K ⊆ H/A⁺H` to `K ⊆ H`

Let `A → K → H` be morphisms of commutative Hopf algebras over a field `k`.  Takeuchi's
Lemma 3.9 identifies the square
```
K ⊗[A] H  ⟶  H ⊗[A] H
   ≅             ≅
(K/A⁺K) ⊗[k] H ⟶ (H/A⁺H) ⊗[k] H
```
Consequently, if `H` is faithfully flat over `A` and `H/A⁺H` is faithfully flat over `K/A⁺K`,
then `H ⊗[A] H` is faithfully flat over `K ⊗[A] H`, hence over `K`, and therefore `H` itself is
faithfully flat over `K` (being a `K`-module retract of `H ⊗[A] H`).

This is `HopfAlgebra.Commutative.faithfullyFlat_of_quotAug_faithfullyFlat`, the last step of
Takeuchi's proof of Theorem 3.1 in characteristic `p`.

## Main results

* `HopfAlgebra.Commutative.faithfullyFlat_of_quotAug_faithfullyFlat`: if `H` is faithfully flat over
  `A` and `H/A⁺H` is faithfully flat over `K/A⁺K`, then `H` is faithfully flat over `K`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 3.9 and Theorem 3.1
-/

@[expose] public section

section
open Module.FaithfullyFlat
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra

variable {k A K H : Type*} [Field k] [CommRing A] [CommRing K] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k K] [HopfAlgebra k H]
  [Algebra A K] [Algebra A H]

variable (j : K →ₐc[k] H) (fAK : A →ₐc[k] K) (halgK : ∀ a, algebraMap A K a = fAK a)
  (halgH : ∀ a, algebraMap A H a = j (fAK a))

section

variable [Algebra K H] [IsScalarTower A K H] (halgKH : ∀ x, algebraMap K H x = j x)

include halgK halgH halgKH

/-- The map `K ⊗[A] H → H ⊗[A] H` of `Foundations/RingTheory/FaithfullyFlatMixedDescent.lean` is the
one induced by `j`. -/
lemma tensorLeftMap_eq_rTensor (z : K ⊗[A] H) :
    tensorLeftMap (A := A) (K := K) (H := H) z
      = LinearMap.rTensor H (jLinear j fAK halgK halgH) z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, jLinear_apply]
    change (IsScalarTower.toAlgHom A K H x) ⊗ₜ[A] (AlgHom.id A H y) = _
    rw [show (IsScalarTower.toAlgHom A K H) x = algebraMap K H x from rfl, halgKH]
    rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv]

end

section Descent

variable [Algebra (QuotAug k A K) (QuotAug k A H)]

include halgK halgH in
/-- Compatibility of the commutation isomorphism with the induced map of quotients. -/
lemma comm_lTensor_quotAugMap
    (hq : ∀ u, algebraMap (QuotAug k A K) (QuotAug k A H) u = quotAugMap j fAK halgK halgH u)
    [IsScalarTower k (QuotAug k A K) (QuotAug k A H)]
    (w : H ⊗[k] QuotAug k A K) :
    Algebra.TensorProduct.comm k H (QuotAug k A H)
        (LinearMap.lTensor H (quotAugMap j fAK halgK halgH).toLinearMap w)
      = tensorRightMap k (QuotAug k A K) (QuotAug k A H) H
          (Algebra.TensorProduct.comm k H (QuotAug k A K) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y u =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.comm_tmul,
      tensorRightMap, Algebra.TensorProduct.map_tmul]
    rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', AlgHom.id_apply, hq]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]

variable [IsScalarTower k A K] [IsScalarTower k A H] [Algebra K H] [IsScalarTower A K H]
  (halgKH : ∀ x, algebraMap K H x = j x)

include halgK halgH halgKH

/-- **Takeuchi's descent step** ([Takeuchi1972], Lemma 3.9).  If `H` is faithfully flat over the
Hopf subalgebra `A` and `H/A⁺H` is faithfully flat over `K/A⁺K`, then `H` is faithfully flat over
`K`. -/
theorem faithfullyFlat_of_quotAug_faithfullyFlat
    (hq : ∀ u, algebraMap (QuotAug k A K) (QuotAug k A H) u = quotAugMap j fAK halgK halgH u)
    [IsScalarTower k (QuotAug k A K) (QuotAug k A H)]
    [Module.FaithfullyFlat A H]
    [Module.FaithfullyFlat (QuotAug k A K) (QuotAug k A H)] :
    Module.FaithfullyFlat K H := by
  set α : (K ⊗[A] H) ≃ₐ[k] (QuotAug k A K) ⊗[k] H :=
    (mixedTensorAlgEquiv j fAK halgK halgH).trans
      (Algebra.TensorProduct.comm k H (QuotAug k A K)) with hα
  set β : (H ⊗[A] H) ≃ₐ[k] (QuotAug k A H) ⊗[k] H :=
    (mixedTensorAlgEquiv (BialgHom.id k H) (fAH j fAK)
      (algebraMap_eq_fAH j fAK halgH) (algebraMap_eq_id_fAH j fAK halgH)).trans
      (Algebra.TensorProduct.comm k H (QuotAug k A H)) with hβ
  refine faithfullyFlat_of_mixed_square (k := k) (A := A) (K := K) (H := H)
    (L := QuotAug k A K) (M := QuotAug k A H) α.toRingEquiv β.toRingEquiv fun z => ?_
  rw [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv, hα, hβ, AlgEquiv.trans_apply,
    AlgEquiv.trans_apply, mixedTensorAlgEquiv_apply,
    mixedTensorAlgEquiv_apply, tensorLeftMap_eq_rTensor j fAK halgK halgH halgKH z,
    mixedTensor_naturality j fAK halgK halgH z]
  exact comm_lTensor_quotAugMap j fAK halgK halgH hq _

end Descent

end HopfAlgebra.Commutative
end
