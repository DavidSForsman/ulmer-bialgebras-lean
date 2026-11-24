module

public import UlmerBialgebras.Factorization.SubTheoryLimits
public import UlmerBialgebras.Factorization.RepCat
public import UlmerBialgebras.Monadicity.SubTheoryColimits
public import Foundations.CategoryTheory.Factorization.ExactCriterion

/-!
# Corollary 6.9: exactness of `M^{T₂}` for a sub-theory `T₁ ⊂ T₂`

The exactness part of Corollary 6.9.  In addition to the hypotheses of the regular case
(`SubTheoryRegular.lean`) we assume that `M^{T₁}` is exact, that each `M_c` has reflexive
coequalizers and that the interpretation of every functor symbol preserves them
componentwise.  Then `M^{T₂}` is exact.

The proof combines:

* the exactness criterion of Lemma 6.5 (3) (`ExactCriterion.lean`);
* the fact that the forgetful functor `M^{T₂} → M^{T₁}` creates, hence preserves, reflexive
  coequalizers (Corollary 4.17);
* the fact that it preserves finite limits;
* the conservativity of `M^{T₂} → M^{T₁}`, which follows from the fact that `M^T` is a full
  subcategory of `M^σ`.

Only helper lemmas remain in this file; the assembled statement, for extensions of
1-signatures, is `UlmerBialgebras/Proofs/Sec6/SubSigExact.lean`.

## Main results

* `UlmerBialgebras.preservesFiniteLimits_of_equivalenceSquare'`: preservation of finite limits
  transports along a square of equivalences.
* `UlmerBialgebras.preservesFiniteLimits_of_repPreservesFiniteLimits`: in `CAT`, representable
  preservation of finite limits gives ordinary preservation of finite limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.5,
  Corollary 6.8, Corollary 6.9
-/

@[expose] public section

universe v u

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## Transport of preservation of finite limits -/

/-- Preservation of finite limits transports along a square of equivalences. -/
theorem preservesFiniteLimits_of_equivalenceSquare' {A A' B B' : Type*} [Category A]
    [Category A'] [Category B] [Category B'] (F : A ⥤ B) (F' : A' ⥤ B') (eA : A' ≌ A)
    (eB : B' ≌ B) (i : eA.functor ⋙ F ≅ F' ⋙ eB.functor) [PreservesFiniteLimits F'] :
    PreservesFiniteLimits F := by
  have : PreservesFiniteLimits (eA.inverse ⋙ F' ⋙ eB.functor) := inferInstance
  refine preservesFiniteLimits_of_natIso (F := eA.inverse ⋙ F' ⋙ eB.functor) ?_
  calc eA.inverse ⋙ F' ⋙ eB.functor
      ≅ eA.inverse ⋙ eA.functor ⋙ F := Functor.isoWhiskerLeft _ i.symm
    _ ≅ (eA.inverse ⋙ eA.functor) ⋙ F := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ F := Functor.isoWhiskerRight eA.counitIso F
    _ ≅ F := Functor.leftUnitor F

/-- In `CAT`, representable preservation of finite limits is ordinary preservation of finite
limits. -/
theorem preservesFiniteLimits_of_repPreservesFiniteLimits {C D : Cat.{v, u}} (F : C ⟶ D)
    (h : RepPreservesFiniteLimits F) :
    PreservesFiniteLimits F.toFunctor := by
  have := (h One).some
  exact preservesFiniteLimits_of_equivalenceSquare' _ (postcomp One F) ((catHomEquivalence One
      C).trans (oneEquiv C)) ((catHomEquivalence One D).trans (oneEquiv D))
    (Iso.refl _)

/-! ## Corollary 6.9: the exact case -/

variable {Sg : TwoSig}

namespace Model

end Model

end UlmerBialgebras
