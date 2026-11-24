module

public import Hopf.Commutative.AugSpanBaseChange
public import Hopf.Commutative.AugSpanFiniteType

/-!
# Takeuchi's Theorem 4.3 over an arbitrary field

`Hopf/Commutative/AugSpanFiniteType.lean` proves the surjectivity half of Takeuchi's
Theorem 4.3 over an algebraically closed field, and
`Hopf/Commutative/AugSpanBaseChange.lean` proves Takeuchi's Lemma 4.6, the descent of
that statement along an extension of the base field.  Taking the extension to be an algebraic
closure we obtain the theorem over an arbitrary field:

* `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_holds`: every normal Hopf ideal of a commutative
  Hopf algebra over a field is the augmentation ideal `K⁺H` of a sub-Hopf algebra `K` (the
  surjectivity half of **Takeuchi's Theorem 4.3**).

## Main results

* `HopfAlgebra.Commutative.BaseChange.normalHopfIdealEqAugSpan_of_baseChange`: the surjectivity half
  of Theorem 4.3 for `L ⊗[k] H` over `L` implies it for `H` over `k` (Takeuchi's Lemma 4.6).
* `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_holds`: every normal Hopf ideal `I` of a
  commutative Hopf algebra over a field satisfies `I = K(I)⁺H` (Takeuchi's Theorem 4.3, surjectivity
  half).

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.6 and Theorem 4.3
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

namespace BaseChange

variable (L : Type u) [Field L] [Algebra k L]

/-- **Takeuchi's Lemma 4.6**: the surjectivity half of Theorem 4.3 descends from `L ⊗[k] H` to
`H`. -/
theorem normalHopfIdealEqAugSpan_of_baseChange
    (hSurj : NormalHopfIdealEqAugSpan L (L ⊗[k] H)) : NormalHopfIdealEqAugSpan k H :=
  HopfExt.normalHopfIdealEqAugSpan_of_ext L (incl k L H) comul_incl counit_incl antipode_incl
    (extAlg_incl_bijective k H L) (FaithfulSMul.algebraMap_injective k L) hSurj

end BaseChange

/-- **The surjectivity half of Takeuchi's Theorem 4.3** [Takeuchi1972], over an arbitrary field:
every normal Hopf ideal of a commutative Hopf algebra `H` over a field `k` is of the form `K⁺H` for
a sub-Hopf algebra `K` of `H`. -/
theorem normalHopfIdealEqAugSpan_holds : NormalHopfIdealEqAugSpan k H :=
  BaseChange.normalHopfIdealEqAugSpan_of_baseChange (L := AlgebraicClosure k)
    normalHopfIdealEqAugSpan_of_isAlgClosed

end HopfAlgebra.Commutative
end
