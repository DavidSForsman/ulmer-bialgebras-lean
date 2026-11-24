module

public import Hopf.Commutative.FaithfulFlatnessUnconditional

/-!
# Faithful flatness over von Neumann regular base rings, without hypotheses

The results of `Hopf/Basic/HopfFaithfulFlatness.lean` — the extension of Takeuchi's theorem from
fields to commutative von Neumann regular base rings — were stated relative to the explicit
hypothesis `HopfAlgebra.InjectiveIsFaithfullyFlat` (Takeuchi's Theorem 3.1 over a field). That
hypothesis is now a theorem, `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_holds`, so the main
one becomes unconditional:

* `AffineGroupSchemes.faithfullyFlat_of_injective_of_isVonNeumannRegular_holds`: over a commutative
  von Neumann regular ring `R`, an injective morphism `f : A →ₐc[R] B` of commutative Hopf
  `R`-algebras makes `B` a faithfully flat `A`-module.

## Main results

* `AffineGroupSchemes.faithfullyFlat_of_injective_of_isVonNeumannRegular_holds`: over a commutative
  von Neumann regular ring `R`, an injective morphism `f : A →ₐc[R] B` of commutative Hopf
  `R`-algebras makes `B` a faithfully flat `A`-module.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27
* [D. Forsman,
  *On the semi-abelianness of affine group schemes*][forsman2026semiabeliannessaffinegroupschemes],
  Section 4
-/

@[expose] public section

universe u

namespace AffineGroupSchemes

open HopfAlgebra.Commutative
open HopfAlgebra

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B]

/-- **Faithful flatness of injections of commutative Hopf algebras over a commutative von Neumann
regular ring**, unconditionally: if `R` is a commutative von Neumann regular ring and
`f : A →ₐc[R] B` is an injective morphism of commutative Hopf `R`-algebras, then `B` is
faithfully flat over `A`. -/
theorem faithfullyFlat_of_injective_of_isVonNeumannRegular_holds (hR : IsVonNeumannRegular R)
    (f : A →ₐc[R] B) (hf : Function.Injective f) :
    letI := algebraOfBialgHom f
    Module.FaithfullyFlat A B :=
  faithfullyFlat_of_injective_of_isVonNeumannRegular injectiveIsFaithfullyFlat_holds hR f hf

end AffineGroupSchemes
