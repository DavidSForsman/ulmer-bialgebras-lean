module

public import Hopf.Commutative.HopfDirectedUnion
public import Hopf.Commutative.FaithfullyFlatOverSubHopf

/-!
# Takeuchi's faithful flatness theorem

Putting together the pieces of Takeuchi's proof of Theorem 3.1 of *A correspondence between Hopf
ideals and sub-Hopf algebras* (manuscripta math. **7** (1972)), in the commutative case:

* Proposition 3.7 (`HopfAlgebra.Commutative.faithfullyFlat_of_isReduced`) for a reduced finitely
  generated Hopf subalgebra over an algebraically closed field;
* the characteristic `p` case via the Frobenius sub-Hopf algebra, Waterhouse's §14.2 and
  Lemma 3.9 (`HopfAlgebra.Commutative.faithfullyFlat_of_injective_of_charP`);
* the reduction of arbitrary commutative Hopf algebras to finitely generated ones, using local
  finiteness (`HopfAlgebra.LocallyFinite.exists_fg_isSubHopfAlgebra`), which gives Theorem 3.1 over
  an algebraically closed field (`HopfAlgebra.Commutative.faithfullyFlat_of_injective_algClosed`);
* base change to the algebraic closure (`HopfAlgebra.Commutative.faithfullyFlat_of_injective`),
  which gives the theorem over an arbitrary field.

The one ingredient which is *not* proved here is **Cartier's theorem** — a commutative Hopf algebra
over a field of characteristic zero is reduced — which is not available in Mathlib. As everywhere in
this development it is not assumed as an axiom, but carried as the explicit hypothesis
`HopfAlgebra.Commutative.CharZeroReduced`. In particular, in positive characteristic all the results
below are unconditional.

Cartier's theorem is proved in `Hopf/CharZero/Reduced.lean`
(`HopfAlgebra.CharZero.charZeroReduced_holds`), so the results below hold unconditionally; they are
restated without the hypothesis in `Hopf/Commutative/FaithfulFlatnessUnconditional.lean`.

## Main results

* `HopfAlgebra.Commutative.injectiveIsFaithfullyFlatAlgClosed_of_charZeroReduced`:
  `HopfAlgebra.Commutative.InjectiveIsFaithfullyFlatAlgClosed`, the theorem over an algebraically
  closed field;
* `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_of_charZeroReduced`:
  `HopfAlgebra.InjectiveIsFaithfullyFlat`, the theorem over an arbitrary field;
* `HopfAlgebra.Commutative.faithfullyFlatOverSubHopf_of_charZeroReduced`: the formulation of the
  paper, a commutative Hopf algebra is faithfully flat over any sub-Hopf algebra.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1, Proposition 3.7 and Lemma 3.9
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3, Section 11.4 (Cartier's theorem) and Chapter 14
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

universe u

/-- **Takeuchi's theorem over an algebraically closed field**
(`InjectiveIsFaithfullyFlatAlgClosed`), given Cartier's theorem in characteristic zero. -/
theorem injectiveIsFaithfullyFlatAlgClosed_of_charZeroReduced (hReduced : CharZeroReduced.{u}) :
    HopfAlgebra.Commutative.InjectiveIsFaithfullyFlatAlgClosed.{u} := by
  intro k A B _ _ _ _ _ _ f hf
  let := algebraOfBialgHom f
  exact faithfullyFlat_of_injective_algClosed f (fun _ => rfl) hf hReduced

/-- **Takeuchi's theorem over an arbitrary field** (`InjectiveIsFaithfullyFlat`), given Cartier's
theorem in characteristic zero: an injective morphism of commutative Hopf algebras over a field
makes the target a faithfully flat module over the source. -/
theorem injectiveIsFaithfullyFlat_of_charZeroReduced (hReduced : CharZeroReduced.{u}) :
    HopfAlgebra.InjectiveIsFaithfullyFlat.{u} :=
  HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_of_algClosed
      (injectiveIsFaithfullyFlatAlgClosed_of_charZeroReduced hReduced)

/-- **Takeuchi's Theorem 3.1** [Takeuchi1972], in the formulation of the paper: a commutative Hopf
algebra over a field is faithfully flat over each of its sub-Hopf algebras (given Cartier's theorem
in characteristic zero). -/
theorem faithfullyFlatOverSubHopf_of_charZeroReduced (hReduced : CharZeroReduced.{u}) :
    HopfAlgebra.Commutative.FaithfullyFlatOverSubHopf.{u} :=
  HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_iff_faithfullyFlatOverSubHopf.1
      (injectiveIsFaithfullyFlat_of_charZeroReduced hReduced)

end HopfAlgebra.Commutative
end
