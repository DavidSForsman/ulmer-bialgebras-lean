module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Foundations.RingTheory.VonNeumannRegular
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness over von Neumann regular rings

The flatness consequence of the von Neumann regular ring condition.

## Main results

* `IsVonNeumannRegular.flat`: every module over a commutative von Neumann regular ring is
  flat.

## References

* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27; Chapter 3, Exercise 10
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10
* [D. Forsman,
  *On the semi-abelianness of affine group schemes*][forsman2026semiabeliannessaffinegroupschemes],
  Section 4
-/

@[expose] public section

section

variable {A : Type*} [CommRing A]

namespace IsVonNeumannRegular

/-- **Every module over a commutative von Neumann regular ring is flat.**

Localizing at a maximal ideal turns `A` into a field, over which every module is free, and
flatness can be checked locally. -/
theorem flat (hA : IsVonNeumannRegular A) (M : Type*) [AddCommGroup M] [Module A M] :
    Module.Flat A M := by
  refine Module.flat_of_localized_maximal (M := M) fun P hP => ?_
  let : Field (Localization.AtPrime P) := (hA.isField_localizationAtPrime P).toField
  rw [← Module.flat_iff_of_isLocalization (R := A) (S := Localization.AtPrime P)
    (M := LocalizedModule P.primeCompl M) P.primeCompl]
  infer_instance

end IsVonNeumannRegular

end
