module

public import Foundations.CategoryTheory.Factorization.RegularCharacterization
public import Foundations.CategoryTheory.Factorization.RegularTools

/-!
# Kernel-pair relations

The relation represented by a kernel pair, its membership criterion, and the associated
coequalizer construction.

## Main results

* `UlmerBialgebras.Related`: two generalized elements are related by a relation `(r, s)` when the
  pair factors through `(r, s)`;
* `UlmerBialgebras.IsKernelPair.related_iff`: if `(r, s)` is a kernel pair of `f`, then `x` and `y`
  are related by `(r, s)` iff `x ≫ f = y ≫ f`;
* `UlmerBialgebras.isColimitCoforkOfIsKernelPair`: in a regular category an extremal epimorphism is
  the coequalizer of its kernel pair.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 6
* [A. Carboni, J. Lambek, M. C. Pedicchio, *Diagram chasing in Mal'cev
  categories*][Carboni-Lambek-Pedicchio]
* [A. Carboni, G. M. Kelly, M. C. Pedicchio, *Some remarks on Maltsev and Goursat
  categories*][CarboniKellyPedicchio1993]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- Two generalized elements are **related** by the relation `(r, s)` when the pair factors
through `(r, s)`.  The two legs are allowed to have different codomains, so that this also
covers relations *from* `X` *to* `Y`. -/
def Related {R X Y : C} (r : R ⟶ X) (s : R ⟶ Y) {T : C} (x : T ⟶ X) (y : T ⟶ Y) : Prop :=
  ∃ z : T ⟶ R, z ≫ r = x ∧ z ≫ s = y

/-! ## Kernel pairs as relations -/

/-- If `(r, s)` is a kernel pair of `f`, then `x` and `y` are related by `(r, s)` iff
`x ≫ f = y ≫ f`. -/
lemma IsKernelPair.related_iff {R X Y : C} {f : X ⟶ Y} {r s : R ⟶ X} (h : IsKernelPair f r s)
    {T : C} (x y : T ⟶ X) : Related r s x y ↔ x ≫ f = y ≫ f := by
  constructor
  · rintro ⟨z, rfl, rfl⟩
    rw [Category.assoc, Category.assoc, h.w]
  · intro hxy
    exact ⟨h.lift x y hxy, h.lift_fst _ _ _, h.lift_snd _ _ _⟩

/-! ## Coequalizer of a kernel pair -/

/-- **In a regular category an extremal epimorphism is the coequalizer of its kernel
pair.** -/
noncomputable def isColimitCoforkOfIsKernelPair (hC : IsRegularCat C) {R X Y : C} {r s : R ⟶ X}
    {ε : X ⟶ Y} (hkp : IsKernelPair ε r s) (hε : extremalEpi C ε) (w : r ≫ ε = s ≫ ε) :
    IsColimit (Cofork.ofπ ε w) := by
  have := hC.hasFiniteLimits
  have : Regular C := regular_of_isRegularCat hC
  have hreg : IsRegularEpi ε :=
    (isRegularEpi_iff_isExtremalEpi ε).2 ((extremalEpi_iff ε).1 hε)
  have : IsRegularEpi ε := hreg
  exact isColimitCoforkOfEffectiveEpi ε (PullbackCone.mk r s w) (Classical.choice hkp.isLimit')

end UlmerBialgebras
