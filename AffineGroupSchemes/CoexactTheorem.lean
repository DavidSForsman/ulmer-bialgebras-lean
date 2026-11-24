module

public import AffineGroupSchemes.CoexactUnconditional
public import Hopf.Commutative.AugSpanUnconditional

/-!
# Coexactness of the category of commutative Hopf algebras

`AffineGroupSchemes/CoexactUnconditional.lean` reduces Forsman's Theorem 3.15 to the
surjectivity half of Takeuchi's Theorem 4.3, and
`Hopf/Commutative/AugSpanUnconditional.lean` proves the latter for every field.
Combining the two (`HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_holds`, Takeuchi's
surjectivity statement for every field) we obtain Theorem 3.15 unconditionally:

* `AffineGroupSchemes.isBarrExact_commHopfAlgCat_op`: **Theorem 3.15** — the opposite of the
  category of commutative Hopf `k`-algebras (i.e. the category of affine group `k`-schemes) is
  Barr-exact.

## Main results

* `AffineGroupSchemes.isBarrExact_commHopfAlgCat_op`: Theorem 3.15 of
  [forsman2026semiabeliannessaffinegroupschemes] — `(CommHopfAlgCat k)ᵒᵖ` is Barr-exact for
  every field `k`.

## References

* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.15
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  4.3
* [M. Barr, *Exact categories*][Ba]
* [G. Janelidze, L. Márki, W. Tholen, *Semi-abelian categories*][JANELIDZE2002367]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.11
-/

@[expose] public section

universe u

open CategoryTheory

namespace AffineGroupSchemes
open HopfAlgebra.Commutative

variable (k : Type u) [Field k]

/-- **Theorem 3.15** of [forsman2026semiabeliannessaffinegroupschemes]: the opposite of the
category of commutative Hopf algebras over a field —
that is, the category of affine group schemes over that field — is Barr-exact (the category of
commutative Hopf algebras is coexact). -/
theorem isBarrExact_commHopfAlgCat_op : IsBarrExact (CommHopfAlgCat.{u} k)ᵒᵖ :=
  coexact_commHopfAlgCat_of_normalHopfIdealEqAugSpan k
    (fun _ _ _ _ _ => normalHopfIdealEqAugSpan_holds)

end AffineGroupSchemes
