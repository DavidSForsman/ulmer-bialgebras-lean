module

public import Foundations.RingTheory.VonNeumannRegular
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Foundations.CategoryTheory.Factorization.ExactCriterion

/-!
# Commutative von Neumann regular rings, and localization

This file collects the ring-theoretic content of the passage "from fields to commutative von Neumann
regular rings" (Section 6.3): a commutative ring `R` is **von Neumann regular** when every `a : R`
satisfies `a * b * a = a` for some `b : R`, and these are exactly the commutative rings all of whose
localizations at prime (equivalently, maximal) ideals are fields. Such a characterisation is what
makes local–global arguments along the jointly conservative family of localization functors
(`CategoryTheory.isBarrExact_of_jointlyConservative`) available over these rings (Lemma 6.10,
Corollary 6.11).

The converse (a ring all of whose localizations at primes are fields is von Neumann regular)
is not formalized here.

Earlier versions of this file also derived, from the (in general false) exactness of the
category `CommComon (ModuleCat k)` of cocommutative coalgebras over a field, the exactness of
the category of cocommutative Hopf algebras over a commutative von Neumann regular ring.  That
route has been removed: the category of cocommutative comonoids is in general not regular, so
it is not exact, and the correspondence between subobjects and quotients has to be obtained by
*descent* instead, through the effective coset relations of `InternalGroups/CosetKernel.lean`.
This file is used by `UlmerBialgebras/Paper/Sec3DefsLoc.lean` and
`UlmerBialgebras/Proofs/Sec6/AffGrpLoc.lean`.

## Main results

* `UlmerBialgebras.IsVonNeumannRegularRing`: every `a : R` satisfies `a * b * a = a` for some
  `b : R`.
* its localizations at primes are fields: `IsVonNeumannRegular.isField_localizationAtPrime`
  (`Foundations/RingTheory/VonNeumannRegular.lean`), which applies to it as it stands.
* `UlmerBialgebras.IsVonNeumannRegularRing.of_isField`: fields are von Neumann regular.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10,
  Corollary 6.11
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27; Chapter 3, Exercise 10
-/

@[expose] public section

universe u

namespace UlmerBialgebras

open CategoryTheory Limits

/-- A commutative ring `R` is **von Neumann regular** if for every `a : R` there is a `b : R`
with `a * b * a = a`. This is an alias of `IsVonNeumannRegular`, the definition used in
`Foundations`. -/
abbrev IsVonNeumannRegularRing (R : Type*) [CommRing R] : Prop :=
  IsVonNeumannRegular R

namespace IsVonNeumannRegularRing

/-- A field is von Neumann regular. -/
theorem of_isField {R : Type*} [CommRing R] (h : IsField R) : IsVonNeumannRegularRing R := by
  intro a
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  · obtain ⟨b, hb⟩ := h.mul_inv_cancel ha
    exact ⟨b, by rw [hb, one_mul]⟩

end IsVonNeumannRegularRing

end UlmerBialgebras
