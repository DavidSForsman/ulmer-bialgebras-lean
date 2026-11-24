module

public import Hopf.Basic.ComoduleTensor
public import Hopf.Commutative.RelInvGroupLike

/-!
# Twisting a relatively invariant vector into a coinvariant one

Let `H` be a commutative Hopf algebra over a field `k` and let `I` be an ideal of `H`. A vector `v`
of a right `H`-comodule `V` which is *relatively invariant modulo `I`* with coefficient `g`
(`HopfAlgebra.Commutative.IsRelInvMod`, the situation produced by Takeuchi's Lemma 4.13 in
`Hopf/Commutative/RelInvGroupLike.lean`) is made *coinvariant* modulo `I`
(`HopfAlgebra.Commutative.IsCoinvMod`) by tensoring it with a vector whose coefficient is inverse to
`g` modulo `I`. This is the twisting step of Takeuchi's Lemma 4.15 (*A correspondence between Hopf
ideals and sub-Hopf algebras*, manuscripta math. **7** (1972), 251–270).

## Main results

* `HopfAlgebra.Commutative.isRelInvMod_tmul`: the coefficients multiply, i.e. the diagonal coaction
  of `v ⊗ u` on the tensor product of two comodules is `(v ⊗ u) ⊗ g g'` modulo `I`;
* `HopfAlgebra.Commutative.isCoinvMod_tmul_of_isRelInvMod`: hence `v ⊗ u` is coinvariant modulo `I`
  as soon as `g g' ≡ 1 mod I`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra Coalgebra.Comodule HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V U : Type u} [AddCommGroup V] [Module k V] [RightComodule k H V]
  [AddCommGroup U] [Module k U] [RightComodule k H U]

/-- The diagonal comodule structure on the tensor product of two right `H`-comodules. -/
noncomputable scoped instance tensorComoduleInstance : RightComodule k H (V ⊗[k] U) :=
  Coalgebra.Comodule.tensorComodule k H V U

variable (k H V U) in
/-- The shuffle map `(V ⊗ H/I) ⊗ (U ⊗ H/I) → (V ⊗ U) ⊗ H/I`,
`(v ⊗ a) ⊗ (u ⊗ b) ↦ (v ⊗ u) ⊗ a b`, used to express the reduction modulo `I` of the diagonal
coaction. -/
noncomputable def shuffleQuot (I : Ideal H) :
    (V ⊗[k] (H ⧸ I)) ⊗[k] (U ⊗[k] (H ⧸ I)) →ₗ[k] (V ⊗[k] U) ⊗[k] (H ⧸ I) :=
  (LinearMap.lTensor (V ⊗[k] U) (LinearMap.mul' k (H ⧸ I))) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k V (H ⧸ I) U (H ⧸ I)).toLinearMap

omit [RightComodule k H V] [RightComodule k H U] in
/-- `shuffleQuot ((v ⊗ a) ⊗ (u ⊗ b)) = (v ⊗ u) ⊗ a b`. -/
@[simp] lemma shuffleQuot_tmul (I : Ideal H) (v : V) (a : H ⧸ I) (u : U) (b : H ⧸ I) :
    shuffleQuot k H V U I ((v ⊗ₜ[k] a) ⊗ₜ[k] (u ⊗ₜ[k] b)) = (v ⊗ₜ[k] u) ⊗ₜ[k] (a * b) := rfl

/-- Reduction modulo `I` of the diagonal coaction of a pure tensor: it is the shuffle of the
reductions of the two coactions. -/
lemma lTensor_mk_coact_tmul (I : Ideal H) (v : V) (u : U) :
    LinearMap.lTensor (V ⊗[k] U) (Ideal.Quotient.mkₐ k I).toLinearMap
        (coact (R := k) (C := H) (v ⊗ₜ[k] u))
      = shuffleQuot k H V U I
          ((LinearMap.lTensor V (Ideal.Quotient.mkₐ k I).toLinearMap
              (coact (R := k) (C := H) v)) ⊗ₜ[k]
            (LinearMap.lTensor U (Ideal.Quotient.mkₐ k I).toLinearMap
              (coact (R := k) (C := H) u))) := by
  classical
  set rv := Repr.arbitrary k H v with hrv
  set ru := Repr.arbitrary k H u with hru
  have hv : LinearMap.lTensor V (Ideal.Quotient.mkₐ k I).toLinearMap
      (coact (R := k) (C := H) v)
      = ∑ i ∈ rv.index, rv.left i ⊗ₜ[k] (Ideal.Quotient.mk I (rv.right i)) := by
    rw [← rv.eq, map_sum]
    rfl
  have hu : LinearMap.lTensor U (Ideal.Quotient.mkₐ k I).toLinearMap
      (coact (R := k) (C := H) u)
      = ∑ j ∈ ru.index, ru.left j ⊗ₜ[k] (Ideal.Quotient.mk I (ru.right j)) := by
    rw [← ru.eq, map_sum]
    rfl
  have hcoact : coact (R := k) (C := H) (v ⊗ₜ[k] u)
      = ∑ i ∈ rv.index, ∑ j ∈ ru.index,
          (rv.left i ⊗ₜ[k] ru.left j) ⊗ₜ[k] (rv.right i * ru.right j) :=
    Coalgebra.Comodule.tensorCoact_tmul_repr rv ru
  rw [hcoact, hv, hu, map_sum]
  rw [TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.lTensor_tmul, shuffleQuot_tmul]
  simp [Ideal.Quotient.mkₐ_eq_mk]

/-- **The coefficients of relative invariance multiply.**  If `ρ v ≡ v ⊗ g` and `ρ u ≡ u ⊗ g'`
modulo `I`, then the diagonal coaction of `v ⊗ u` is `(v ⊗ u) ⊗ g g'` modulo `I`. -/
theorem isRelInvMod_tmul {I : Ideal H} {v : V} {u : U} {g g' : H}
    (hv : IsRelInvMod k I v g) (hu : IsRelInvMod k I u g') :
    IsRelInvMod k I (v ⊗ₜ[k] u) (g * g') := by
  rw [IsRelInvMod, lTensor_mk_coact_tmul, hv, hu, shuffleQuot_tmul, map_mul]

/-- **The twisting step of Takeuchi's Lemma 4.15.**  A vector which is relatively invariant
modulo `I` with coefficient `g` becomes *coinvariant* modulo `I` after tensoring with a vector
whose coefficient is inverse to `g` modulo `I`. -/
theorem isCoinvMod_tmul_of_isRelInvMod {I : Ideal H} {v : V} {u : U} {g g' : H}
    (hv : IsRelInvMod k I v g) (hu : IsRelInvMod k I u g')
    (hgg : Ideal.Quotient.mk I (g * g') = 1) :
    IsCoinvMod k I (v ⊗ₜ[k] u) := by
  rw [isCoinvMod_iff_isRelInvMod, IsRelInvMod, lTensor_mk_coact_tmul, hv, hu, shuffleQuot_tmul,
    ← map_mul, hgg, map_one]

end HopfAlgebra.Commutative
end
