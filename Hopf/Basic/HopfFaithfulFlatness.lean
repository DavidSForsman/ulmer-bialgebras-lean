module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Foundations.RingTheory.VonNeumannRegular
public import Foundations.RingTheory.FaithfullyFlatLocal

/-!
# Faithful flatness of injections of commutative Hopf algebras over von Neumann regular rings

Takeuchi's theorem states that an injective morphism of commutative Hopf algebras over a *field*
is faithfully flat.  This file contains the local-to-global argument of Section 4 of
[forsman2026semiabeliannessaffinegroupschemes], which upgrades this statement from fields to
arbitrary commutative von Neumann regular base rings: if `R` is a commutative von Neumann regular
ring and `f : A → B` is an injective morphism of commutative Hopf `R`-algebras, then `B` is
faithfully flat over `A`.

Takeuchi's theorem itself is not available in Mathlib; it enters here as the explicit hypothesis
`InjectiveIsFaithfullyFlat`, which is proved in
`Hopf/Commutative/FaithfulFlatnessUnconditional.lean`
(`HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_holds`).

The cocommutative counterpart of the statement is not formalized here: it concerns flatness of a
module over a *noncommutative* ring (a cocommutative Hopf algebra need not be commutative), and
neither tensor products nor flatness over noncommutative rings are available in Mathlib.

## Main results

* `HopfAlgebra.InjectiveIsFaithfullyFlat`: the statement of Takeuchi's theorem over fields, that an
  injective morphism of commutative Hopf algebras over a field is faithfully flat.
* `HopfAlgebra.isFaithfullyFlatAt_of_injectiveIsFaithfullyFlat`: assuming
  `InjectiveIsFaithfullyFlat`, an injective morphism `f : A →ₐc[R] B` over a von Neumann regular
  ring `R` makes `B` faithfully flat over `A` at the image in `A` of the complement of each prime
  ideal of `R`.
* `HopfAlgebra.faithfullyFlat_of_injective_of_isVonNeumannRegular`: assuming
  `InjectiveIsFaithfullyFlat`, for `R` commutative von Neumann regular and `f : A →ₐc[R] B` an
  injective morphism of commutative Hopf `R`-algebras, `B` is faithfully flat over `A` via `f`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Theorem 3.1
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Section 4
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative
  Algebra*][atiyah_introduction_1969], Chapter 3, Exercise 10
-/

@[expose] public section

namespace HopfAlgebra
open Module.FaithfullyFlat
open HopfAlgebra

open TensorProduct
open Algebra (algebraMapSubmonoid)

universe u

/-- The `A`-algebra structure on `B` determined by a morphism of bialgebras `f : A →ₐc[R] B`. -/
@[instance_reducible]
noncomputable def algebraOfBialgHom {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] [CoalgebraStruct R A] [CoalgebraStruct R B]
    (f : A →ₐc[R] B) : Algebra A B :=
  RingHom.toAlgebra ((f : A →ₐ[R] B) : A →+* B)

/-- **Takeuchi's theorem** (Takeuchi [Takeuchi1972], Theorem 3.1) over a field: an injective
morphism of commutative Hopf algebras over a field `k` is faithfully flat.

This deep result is not available in Mathlib; it is used as an explicit hypothesis, and proved as
`HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_holds` in
`Hopf/Commutative/FaithfulFlatnessUnconditional.lean`.
-/
def InjectiveIsFaithfullyFlat : Prop :=
  ∀ (k A B : Type u) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]
    (f : A →ₐc[k] B), Function.Injective f →
      letI := algebraOfBialgHom f
      Module.FaithfullyFlat A B

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Iterated images of a multiplicative subset along a tower of algebras. -/
theorem algebraMapSubmonoid_algebraMapSubmonoid {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (T : Submonoid R) :
    algebraMapSubmonoid B (algebraMapSubmonoid A T) = algebraMapSubmonoid B T := by
  ext x
  simp [Algebra.algebraMapSubmonoid, IsScalarTower.algebraMap_apply R A B]

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- The base change of an injective morphism of Hopf algebras along a localization `k` of the
base ring which happens to be a field is faithfully flat, assuming Takeuchi's theorem over
fields. -/
theorem isFaithfullyFlatAt_of_injectiveIsFaithfullyFlat_of_isLocalization
    (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    (k : Type u) [Field k] [Algebra R k] (T : Submonoid R) [IsLocalization T k]
    (f : A →ₐc[R] B) (hf : Function.Injective f) :
    letI := algebraOfBialgHom f
    IsFaithfullyFlatAt A B (algebraMapSubmonoid A T) := by
  let := algebraOfBialgHom f
  have : IsScalarTower R A B :=
    .of_algebraMap_eq fun r => ((f : A →ₐ[R] B).commutes r).symm
  have hkflat : Module.Flat R k := IsLocalization.flat k T
  let f' : k ⊗[R] A →ₐc[k] k ⊗[R] B := Bialgebra.TensorProduct.map (BialgHom.id k k) f
  have hcoe : ∀ x : k ⊗[R] A, f' x = LinearMap.lTensor k ((f : A →ₐ[R] B) : A →ₗ[R] B) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c a => simp [f']
    | add x y hx hy => simp [map_add, hx, hy]
  have hf' : Function.Injective f' := by
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := k)
      ((f : A →ₐ[R] B) : A →ₗ[R] B) hf
    intro x y hxy
    apply hinj
    rw [← hcoe, ← hcoe]
    exact hxy
  let := algebraOfBialgHom f'
  have hFF := hInjFlat k (k ⊗[R] A) (k ⊗[R] B) f' hf'
  have : IsLocalization (algebraMapSubmonoid A T) (k ⊗[R] A) :=
    IsLocalization.tensorRight k T
  have : IsLocalization (algebraMapSubmonoid B (algebraMapSubmonoid A T))
      (k ⊗[R] B) := by
    rw [algebraMapSubmonoid_algebraMapSubmonoid]
    exact IsLocalization.tensorRight k T
  let : Algebra A (k ⊗[R] B) := ((algebraMap B (k ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B (k ⊗[R] B) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (k ⊗[R] A) (k ⊗[R] B) := by
    refine .of_algebraMap_eq fun a => ?_
    change algebraMap B (k ⊗[R] B) (f a) = f' (algebraMap A (k ⊗[R] A) a)
    have h1 : algebraMap A (k ⊗[R] A) a = (1 : k) ⊗ₜ[R] a := rfl
    have h2 : algebraMap B (k ⊗[R] B) (f a) = (1 : k) ⊗ₜ[R] (f a) := rfl
    rw [h1, h2]
    exact (Bialgebra.TensorProduct.map_tmul (BialgHom.id k k) f 1 a).symm
  exact isFaithfullyFlatAt_of_model _ hFF

/-- The base change of an injective morphism of Hopf algebras over a von Neumann regular ring
along the localization at a prime is faithfully flat, assuming Takeuchi's theorem over fields. -/
theorem isFaithfullyFlatAt_of_injectiveIsFaithfullyFlat
    (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    (hR : IsVonNeumannRegular R) (f : A →ₐc[R] B) (hf : Function.Injective f)
    (p : Ideal R) [p.IsPrime] :
    letI := algebraOfBialgHom f
    IsFaithfullyFlatAt A B (algebraMapSubmonoid A p.primeCompl) :=
  letI : Field (Localization.AtPrime p) := (hR.isField_localizationAtPrime p).toField
  isFaithfullyFlatAt_of_injectiveIsFaithfullyFlat_of_isLocalization hInjFlat
    (Localization.AtPrime p) p.primeCompl f hf

/-- **Faithful flatness of injections of commutative Hopf algebras over a commutative von Neumann
regular ring.**  If `R` is a commutative von Neumann regular ring and `f : A →ₐc[R] B` is an
injective morphism of commutative Hopf `R`-algebras, then `B` is faithfully flat over `A`.

The proof reduces, by a local-to-global argument, to Takeuchi's theorem over the residue fields
`Rₚ` of `R`, which is the hypothesis `hInjFlat`. -/
theorem faithfullyFlat_of_injective_of_isVonNeumannRegular
    (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    (hR : IsVonNeumannRegular R) (f : A →ₐc[R] B) (hf : Function.Injective f) :
    letI := algebraOfBialgHom f
    Module.FaithfullyFlat A B := by
  let := algebraOfBialgHom f
  have : IsScalarTower R A B :=
    .of_algebraMap_eq fun r => ((f : A →ₐ[R] B).commutes r).symm
  exact faithfullyFlat_of_isFaithfullyFlatAt_prime
    (fun p _ => isFaithfullyFlatAt_of_injectiveIsFaithfullyFlat hInjFlat hR f hf p)

end

end HopfAlgebra
