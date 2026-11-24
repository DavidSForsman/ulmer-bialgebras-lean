module

public import Hopf.Commutative.FaithfulFlatnessCharP

/-!
# Takeuchi's Theorem 3.1 for finitely generated Hopf algebras

Combining the two characteristic cases of Takeuchi's proof of Theorem 3.1:

* in characteristic `p > 0` the result is
  `HopfAlgebra.Commutative.faithfullyFlat_of_injective_of_charP`, proved via the Frobenius sub-Hopf
  algebra;
* in characteristic zero, *Cartier's theorem* says that a commutative Hopf algebra over a field
  of characteristic zero is reduced, so Takeuchi's Proposition 3.7
  (`HopfAlgebra.Commutative.faithfullyFlat_of_isReduced`) applies directly to the given inclusion.

Cartier's theorem is not available in Mathlib; as elsewhere in this development, it is *not* assumed
as an axiom, but carried as an explicit hypothesis, the proposition
`HopfAlgebra.Commutative.CharZeroReduced`. That hypothesis is *proved* in
`Hopf/CharZero/Reduced.lean` (`HopfAlgebra.CharZero.charZeroReduced_holds`), which imports
this file; unconditional versions of the results below are collected in
`Hopf/Commutative/FaithfulFlatnessUnconditional.lean`.

The main result is `HopfAlgebra.Commutative.faithfullyFlat_of_injective_finiteType`.

## Main results

* `HopfAlgebra.Commutative.CharZeroReduced`: Cartier's theorem as a proposition: a commutative Hopf
  algebra over a field of characteristic zero is reduced.
* `HopfAlgebra.Commutative.faithfullyFlat_of_injective_of_charZero`: given `CharZeroReduced`, over
  an algebraically closed field of characteristic zero an injective morphism `j : K →ₐc[k] H` of
  finitely generated commutative Hopf algebras makes `H` faithfully flat over `K`.
* `HopfAlgebra.Commutative.faithfullyFlat_of_injective_finiteType`: the same over an algebraically
  closed field of any characteristic, given `CharZeroReduced`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1 and Proposition 3.7
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 11.4 (Cartier's theorem)
-/

@[expose] public section

section
namespace HopfAlgebra.Commutative

open TensorProduct _root_.Coalgebra

universe u

/-- **Cartier's theorem** ([waterhouseIntroductionAffineGroup1979], Section 11.4), stated as a
proposition: a commutative Hopf algebra over a field of characteristic zero is reduced.

This statement is *not proved here*; it is carried as an explicit hypothesis by the results that
use it, rather than being assumed as an axiom.  It is proved in
`Hopf/CharZero/Reduced.lean`, as `HopfAlgebra.CharZero.charZeroReduced_holds`. -/
def CharZeroReduced : Prop :=
  ∀ (k K : Type u) [Field k] [CharZero k] [CommRing K] [HopfAlgebra k K], IsReduced K

/-- The characteristic zero case of Takeuchi's Theorem 3.1, given Cartier's theorem: over a field
of characteristic zero the Hopf subalgebra `K` is reduced, so Proposition 3.7 applies. -/
theorem faithfullyFlat_of_injective_of_charZero (hReduced : CharZeroReduced.{u})
    {k K H : Type u} [Field k] [IsAlgClosed k] [CharZero k] [CommRing K] [CommRing H]
    [HopfAlgebra k K] [HopfAlgebra k H] [Algebra.FiniteType k K] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H]
    (j : K →ₐc[k] H) (halgKH : ∀ x, algebraMap K H x = j x)
    (hinj : Function.Injective j) :
    Module.FaithfullyFlat K H := by
  have : Nontrivial K := nontrivial_of_hopfAlgebra k K
  have : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  have : IsReduced K := hReduced k K
  exact faithfullyFlat_of_isReduced j (fun x => (halgKH x).symm)
    (fun a b hab => hinj (by rw [← halgKH, ← halgKH, hab]))

/-- **Takeuchi's Theorem 3.1 for finitely generated Hopf algebras over an algebraically closed
field**: if `j : K →ₐc[k] H` is an injective morphism of finitely generated commutative Hopf
algebras over an algebraically closed field, then `H` is faithfully flat over `K`.

In positive characteristic this is unconditional; in characteristic zero it uses Cartier's
theorem, which enters as the explicit hypothesis `hReduced`. -/
theorem faithfullyFlat_of_injective_finiteType (hReduced : CharZeroReduced.{u})
    {k K H : Type u} [Field k] [IsAlgClosed k] [CommRing K] [CommRing H]
    [HopfAlgebra k K] [HopfAlgebra k H] [Algebra.FiniteType k K] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H]
    (j : K →ₐc[k] H) (halgKH : ∀ x, algebraMap K H x = j x)
    (hinj : Function.Injective j) :
    Module.FaithfullyFlat K H := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases (CharP.char_is_prime_or_zero k p).symm with h0 | hprime
  · subst h0
    have : CharZero k := CharP.charP_to_charZero k
    exact faithfullyFlat_of_injective_of_charZero hReduced j halgKH hinj
  · have : Fact p.Prime := ⟨hprime⟩
    exact faithfullyFlat_of_injective_of_charP p j halgKH hinj

end HopfAlgebra.Commutative
end
