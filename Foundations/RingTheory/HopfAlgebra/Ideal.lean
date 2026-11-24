module

public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Hopf ideals and quotient conditions

Mathlib characterizes a Hopf ideal by a coideal condition and antipode stability. The theorem
below combines that characterization with Mathlib's coideal characterization, stated using
algebra quotient maps.

## Main results

* `Ideal.isHopfIdeal_iff_quotient_conditions`: the counit, quotient comultiplication and
  antipode conditions are equivalent to Mathlib's Hopf-ideal condition.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

open Coalgebra HopfAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- An ideal `I` of a Hopf algebra `A` is a Hopf ideal (Mathlib's `Ideal.IsHopfIdeal`) if and only
if the counit vanishes on `I`, the comultiplication followed by the quotient map
`A ⊗ A → A ⧸ I ⊗ A ⧸ I` vanishes on `I`, and the antipode maps `I` into `I`. -/
theorem Ideal.isHopfIdeal_iff_quotient_conditions (I : Ideal A) :
    Ideal.IsHopfIdeal R I ↔
      (∀ x ∈ I, Coalgebra.counit (R := R) x = 0) ∧
      (∀ x ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
        (Ideal.Quotient.mkₐ R I) (comul (R := R) x) = 0) ∧
      ∀ x ∈ I, antipode R x ∈ I := by
  rw [Ideal.isHopfIdeal_iff, Submodule.isCoideal_iff]
  exact and_assoc
