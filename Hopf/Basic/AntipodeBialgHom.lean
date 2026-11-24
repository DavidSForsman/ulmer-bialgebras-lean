module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Hopf.Basic.AntipodeAlgHom

/-!
# Morphisms of Hopf algebras commute with the antipodes

A morphism of bialgebras between two Hopf algebras automatically commutes with the antipodes:
for `f : A →ₐc[R] B` we prove `antipode R ∘ f = f ∘ antipode R`.

The proof is the standard convolution argument, carried out in the convolution monoid of
`R`-linear maps `A →ₗ[R] B` (`A` is a coalgebra and `B` an algebra):

* `antipode ∘ f` is a *left* convolution inverse of `f`, because `f` is a morphism of coalgebras
  and `antipode` is a left convolution inverse of `id` on `B`;
* `f ∘ antipode` is a *right* convolution inverse of `f`, because `f` is a morphism of algebras
  and `antipode` is a right convolution inverse of `id` on `A`;

and a left inverse and a right inverse in a monoid coincide.

No commutativity of `A` or `B` is required.  This is the statement that ensures that the image of
a morphism of Hopf algebras is stable under the antipode.

## Main results

* `HopfAlgebra.antipode_comp_bialgHom`: for a bialgebra morphism `f : A →ₐc[R] B` between Hopf
  algebras, `antipode R ∘ₗ f = f ∘ₗ antipode R`.
* `HopfAlgebra.antipode_bialgHom_apply`: the pointwise form `antipode R (f a) = f (antipode R a)`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.4
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.5
-/

@[expose] public section

open TensorProduct Coalgebra LinearMap WithConv HopfAlgebra

namespace HopfAlgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- `antipode ∘ f` is a left convolution inverse of a morphism of bialgebras `f`. -/
lemma antipode_comp_convMul_bialgHom (f : A →ₐc[R] B) :
    (toConv ((antipode R : B →ₗ[R] B) ∘ₗ (f : A →ₗ[R] B))) * (toConv (f : A →ₗ[R] B)) = 1 := by
  have key := LinearMap.convMul_comp_coalgHom_distrib (toConv (antipode R : B →ₗ[R] B))
    (toConv (LinearMap.id : B →ₗ[R] B)) (f : A →ₗc[R] B)
  rw [LinearMap.antipode_mul_id] at key
  simp only [LinearMap.id_comp] at key
  have h1 : (1 : WithConv (B →ₗ[R] B)).ofConv ∘ₗ (f : A →ₗ[R] B)
      = (1 : WithConv (A →ₗ[R] B)).ofConv := by
    rw [LinearMap.convOne_def, LinearMap.convOne_def]
    simp only [LinearMap.comp_assoc]
    congr 1
    exact (f : A →ₗc[R] B).counit_comp
  exact ofConv_injective (h1.symm.trans key).symm

/-- `f ∘ antipode` is a right convolution inverse of a morphism of bialgebras `f`. -/
lemma bialgHom_convMul_comp_antipode (f : A →ₐc[R] B) :
    (toConv (f : A →ₗ[R] B)) * (toConv ((f : A →ₗ[R] B) ∘ₗ (antipode R : A →ₗ[R] A))) = 1 := by
  have key := LinearMap.algHom_comp_convMul_distrib (f : A →ₐ[R] B)
    (toConv (LinearMap.id : A →ₗ[R] A)) (toConv (antipode R : A →ₗ[R] A))
  rw [LinearMap.id_mul_antipode] at key
  simp only [LinearMap.comp_id] at key
  have h1 : ((f : A →ₐ[R] B) : A →ₗ[R] B) ∘ₗ (1 : WithConv (A →ₗ[R] A)).ofConv
      = (1 : WithConv (A →ₗ[R] B)).ofConv := by
    rw [LinearMap.convOne_def, LinearMap.convOne_def]
    ext a
    exact (f : A →ₐ[R] B).commutes _
  exact (ofConv_injective (h1.symm.trans key)).symm

/-- **A morphism of bialgebras between Hopf algebras commutes with the antipodes.** -/
theorem antipode_comp_bialgHom (f : A →ₐc[R] B) :
    (antipode R : B →ₗ[R] B) ∘ₗ (f : A →ₗ[R] B)
      = (f : A →ₗ[R] B) ∘ₗ (antipode R : A →ₗ[R] A) :=
  toConv_injective
    (left_inv_eq_right_inv (antipode_comp_convMul_bialgHom f) (bialgHom_convMul_comp_antipode f))

/-- **A morphism of bialgebras between Hopf algebras commutes with the antipodes**, pointwise. -/
@[simp]
theorem antipode_bialgHom_apply (f : A →ₐc[R] B) (a : A) :
    antipode R (f a) = f (antipode R a) :=
  congr($(antipode_comp_bialgHom f) a)

end HopfAlgebra
