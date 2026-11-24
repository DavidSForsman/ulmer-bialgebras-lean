module

public import Hopf.Basic.AntipodeAlgHom

/-!
# The antipode of a commutative Hopf algebra is involutive

For a *commutative* Hopf algebra `A` over a commutative ring `R` we prove the classical
structural fact about the antipode `S` that is used in Takeuchi's study of normal Hopf ideals
(*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972)):

* `HopfAlgebra.antipode_antipode`: `S (S a) = a`, i.e. `S` is an involution.

It is proved by the standard convolution argument: in the convolution monoid of `R`-linear maps
`A → A` one exhibits two inverses of one and the same element
(`HopfAlgebra.antipodeSq_convMul_antipode`) and appeals to the uniqueness of inverses in a monoid.

## Main results

* `HopfAlgebra.antipodeSq_convMul_antipode`: for a commutative Hopf algebra, `S ∘ S` is a left
  convolution inverse of the antipode `S`.
* `HopfAlgebra.antipode_antipode`: for a commutative Hopf algebra, `antipode R (antipode R a) = a`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.5
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra WithConv LinearMap

namespace HopfAlgebra

section Involutive

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- `S ∘ S` is a left convolution inverse of `S`. -/
lemma antipodeSq_convMul_antipode :
    (toConv ((antipode R : A →ₗ[R] A) ∘ₗ (antipode R : A →ₗ[R] A))) *
      (toConv (antipode R : A →ₗ[R] A)) = 1 := by
  apply toConv_injective
  ext x
  rw [show ((toConv ((antipode R : A →ₗ[R] A) ∘ₗ (antipode R : A →ₗ[R] A))) *
      (toConv (antipode R : A →ₗ[R] A)) : WithConv (A →ₗ[R] A)).ofConv x
      = ((toConv ((antipode R : A →ₗ[R] A) ∘ₗ (antipode R : A →ₗ[R] A))) *
      (toConv (antipode R : A →ₗ[R] A)) : WithConv (A →ₗ[R] A)) x from rfl,
    (ℛ R x).convMul_apply]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Finset.sum_congr rfl (fun i _ => (HopfAlgebra.antipode_mul_distrib (R := R) (A := A)
      (antipode R ((ℛ R x).left i)) ((ℛ R x).right i)).symm), ← map_sum,
    HopfAlgebra.sum_antipode_mul_eq_smul (ℛ R x)]
  simp [Algebra.algebraMap_eq_smul_one]

variable {R A}

/-- **The antipode of a commutative Hopf algebra is involutive**: `S (S a) = a`. -/
@[simp] theorem antipode_antipode (a : A) : antipode R (antipode R a) = a := by
  have h := left_inv_eq_right_inv (a := toConv (antipode R : A →ₗ[R] A))
    (b := toConv ((antipode R : A →ₗ[R] A) ∘ₗ (antipode R : A →ₗ[R] A)))
    (c := toConv (LinearMap.id : A →ₗ[R] A)) (antipodeSq_convMul_antipode R A)
    (LinearMap.antipode_mul_id (R := R) (C := A))
  have := congrArg (fun t : WithConv (A →ₗ[R] A) => t.ofConv a) h
  simpa using this

end Involutive

end HopfAlgebra
