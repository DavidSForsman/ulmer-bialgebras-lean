module

public import Foundations.CategoryTheory.Factorization.ExactCategory
public import UlmerBialgebras.Proofs.Sec6.ExactBridge
public import UlmerBialgebras.Proofs.Sec6.RegularTransfer
public import Foundations.CategoryTheory.Factorization.RegularMathlib

/-!
# Regularity and exactness: the characterizations through orthogonal factorization systems

The checked statements use Mathlib's regular categories `CategoryTheory.Regular`, Mathlib's
equivalence relations `CategoryTheory.IsEquivalenceRelation`, and the Barr-exact categories
`CategoryTheory.BarrExact` of `Foundations/CategoryTheory/Factorization/ExactCategory.lean`. The
development
works with the paper's Definition 6.4, through an orthogonal factorization system:
`UlmerBialgebras.IsRegularCat`, `UlmerBialgebras.IsExactCat` and `UlmerBialgebras.IsEquivRel`. This
file and `Foundations/CategoryTheory/Factorization/RegularMathlib.lean` prove that the two sets of
notions agree, so that the existing proofs carry over unchanged.

## Main results

* `UlmerBialgebras.extremalEpi_iff_strongEpi`: with equalizers, a morphism is left orthogonal to all
  monomorphisms (`UlmerBialgebras.extremalEpi`) iff it is a strong epimorphism.
* `UlmerBialgebras.extremalEpi_iff_extremalEpi`: with pullbacks and equalizers as well, iff it is an
  extremal epimorphism in Mathlib's sense.
* `CategoryTheory.isBarrExact_iff_barrExact`: `CategoryTheory.IsBarrExact` is Barr-exactness.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4 and the paragraph after it
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- With equalizers, a morphism is left orthogonal to all monomorphisms exactly when it is a
strong epimorphism. -/
lemma extremalEpi_iff_strongEpi [HasEqualizers C] {X Y : C} (f : X ⟶ Y) :
    extremalEpi C f ↔ StrongEpi f :=
  ⟨strongEpi_of_leftOrth_monomorphisms, fun _ _ _ m hm => by
    have : Mono m := hm
    exact OFS.orthogonal_of_strongEpi_of_mono f m⟩

/-- With pullbacks and equalizers, a morphism is left orthogonal to all monomorphisms exactly when
it is an extremal epimorphism in Mathlib's sense (`CategoryTheory.ExtremalEpi`). -/
lemma extremalEpi_iff_extremalEpi [HasPullbacks C] [HasEqualizers C] {X Y : C} (f : X ⟶ Y) :
    extremalEpi C f ↔ ExtremalEpi f :=
  (extremalEpi_iff_strongEpi f).trans (extremalEpi_iff_strongEpi_of_hasPullbacks f).symm

end UlmerBialgebras

namespace CategoryTheory
open CategoryTheory

open CategoryTheory Limits UlmerBialgebras

variable {C : Type u} [Category.{v} C]

/-- An internal equivalence relation in the sense of `CategoryTheory.IsInternalEquivalenceRelation`
is one in the paper's sense. -/
lemma IsInternalEquivalenceRelation.isEquivRel {R X : C} {r₁ r₂ : R ⟶ X}
    (h : IsInternalEquivalenceRelation r₁ r₂) : IsEquivRel r₁ r₂ where
  jointly_mono a b h₁ h₂ := h.jointly_mono a b h₁ h₂
  refl f := ⟨f ≫ h.refl.choose, by simp [h.refl.choose_spec.1],
    by simp [h.refl.choose_spec.2]⟩
  symm d := ⟨d ≫ h.symm.choose, by simp [h.symm.choose_spec.1],
    by simp [h.symm.choose_spec.2]⟩
  trans a b hab := h.trans a b hab

/-- With pullbacks, `CategoryTheory.IsInternalEquivalenceRelation` is Mathlib's notion of an
equivalence relation. -/
lemma isInternalEquivalenceRelation_iff [HasPullbacks C] {R X : C} (r₁ r₂ : R ⟶ X) :
    IsInternalEquivalenceRelation r₁ r₂ ↔ IsEquivalenceRelation r₁ r₂ :=
  ⟨fun h => (isEquivRel_iff_isEquivalenceRelation r₁ r₂).1 h.isEquivRel,
    fun h => isInternalEquivalenceRelation_of_isEquivRel
      ((isEquivRel_iff_isEquivalenceRelation r₁ r₂).2 h)⟩

/-- **`CategoryTheory.IsBarrExact` is Barr-exactness.** -/
theorem isBarrExact_iff_barrExact : IsBarrExact C ↔ BarrExact C := by
  constructor
  · intro h
    have := h.toRegular
    exact BarrExact.mk' fun p₁ p₂ _ => h.isKernelPair_of_isInternalEquivalenceRelation
      ((isInternalEquivalenceRelation_iff p₁ p₂).2 inferInstance)
  · intro h
    exact { toRegular := h.toRegular
            isKernelPair_of_isInternalEquivalenceRelation := fun {_ _ r₁ r₂} hr => by
              have := (isInternalEquivalenceRelation_iff r₁ r₂).1 hr
              exact BarrExact.exists_isKernelPair r₁ r₂ }

/-- A category satisfying `CategoryTheory.IsBarrExact` is Barr-exact. -/
theorem IsBarrExact.barrExact (h : IsBarrExact C) : BarrExact C :=
    CategoryTheory.isBarrExact_iff_barrExact.1 h

end CategoryTheory
