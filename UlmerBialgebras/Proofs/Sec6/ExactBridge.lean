module

public import UlmerBialgebras.Factorization.LPMonoFactorization
public import Foundations.CategoryTheory.Factorization.Malcev
public import InternalGroups.SubgroupCorrespondence
public import AffineGroupSchemes.CoexactTheorem

/-!
# From Barr-exactness to Ulmer's notion of an exact category

Two notions of exactness occur in this development:

* `CategoryTheory.IsBarrExact`, which extends Mathlib's `CategoryTheory.Regular` and asks that every
  internal equivalence relation be a kernel pair;
* `UlmerBialgebras.IsExactCat`, which asks for an orthogonal factorization system whose right class
  is the class of monomorphisms, stability of the left class under base change, and effectiveness of
  every internal equivalence relation.

This file bridges the two.

## Main results

* `UlmerBialgebras.ofsMonoOfStrongEpiMono`: the (extremal epi, mono) factorization system of a
  category with strong epi-mono factorizations.
* `CategoryTheory.isExactCat_of_isBarrExact`: a Barr-exact category is exact in Ulmer's sense.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 6.4
* [M. Barr, *Exact categories*][Ba]
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable (D : Type u) [Category.{v} D]

/-- **The (extremal epi, mono) factorization system of a category with strong epi-mono
factorizations.**  The right class is the class of monomorphisms and the left class is its
left orthogonal, the class of extremal epimorphisms. -/
def ofsMonoOfStrongEpiMono [HasStrongEpiMonoFactorisations D] : OFS D :=
  OFS.mk' (leftOrth (MorphismProperty.monomorphisms D)) (MorphismProperty.monomorphisms D)
    (by
      intro X Y f
      obtain ⟨F⟩ := HasStrongEpiMonoFactorisations.has_fac f
      refine ⟨F.I, F.e, F.m, ?_, ?_, F.fac⟩
      · intro c d m' hm'
        have : Mono m' := hm'
        exact OFS.orthogonal_of_strongEpi_of_mono F.e m'
      · rw [MorphismProperty.monomorphisms.iff]; infer_instance)
    (fun _ _ _ _ _ _ he hm => he _ hm)
    (leftOrth_isStableUnderRetracts _)
    MorphismProperty.IsStableUnderRetracts.monomorphisms

end UlmerBialgebras

namespace CategoryTheory
open CategoryTheory

open CategoryTheory Limits UlmerBialgebras

variable {C : Type u} [Category.{v} C]

/-- In a regular category (in the sense of Mathlib) an extremal epimorphism, i.e. a morphism
left orthogonal to all monomorphisms, is a regular epimorphism. -/
lemma isRegularEpi_of_extremalEpi [Regular C] {X Y : C} {f : X ⟶ Y} (hf : extremalEpi C f) :
    IsRegularEpi f := by
  have : StrongEpi f := strongEpi_of_leftOrth_monomorphisms hf
  infer_instance

/-- In a regular category (in the sense of Mathlib) a regular epimorphism is left orthogonal
to all monomorphisms. -/
lemma extremalEpi_of_isRegularEpi {X Y : C} (f : X ⟶ Y) [IsRegularEpi f] :
    extremalEpi C f := by
  intro c d m hm
  have : Mono m := hm
  exact OFS.orthogonal_of_strongEpi_of_mono f m

/-- In a regular category the extremal epimorphisms are exactly the regular epimorphisms. -/
lemma extremalEpi_eq_regularEpi [Regular C] :
    extremalEpi C = MorphismProperty.regularEpi C := by
  ext X Y f
  rw [MorphismProperty.regularEpi_iff]
  exact ⟨fun h => isRegularEpi_of_extremalEpi h, fun h => extremalEpi_of_isRegularEpi f⟩

/-- An internal equivalence relation in Ulmer's sense is one in Forsman's sense. -/
lemma isInternalEquivalenceRelation_of_isEquivRel {R X : C} {r s : R ⟶ X} (h : IsEquivRel r s) :
    IsInternalEquivalenceRelation r s where
  jointly_mono := fun _ a b h₁ h₂ => h.jointly_mono a b h₁ h₂
  refl := h.refl (𝟙 X)
  symm := by
    obtain ⟨σ, hfst, hsnd⟩ := h.symm (𝟙 R)
    exact ⟨σ, by simpa using hfst, by simpa using hsnd⟩
  trans := fun _ a b hab => h.trans a b hab

/-- **A Barr-exact category is exact in Ulmer's sense.** -/
theorem isExactCat_of_isBarrExact [h : IsBarrExact C] : IsExactCat C := by
  have : Regular C := h.toRegular
  refine ⟨UlmerBialgebras.isRegularCat_of_regular, ?_⟩
  intro R c r s hrs
  obtain ⟨Y, f, hkp⟩ :=
    h.isKernelPair_of_isInternalEquivalenceRelation
      (isInternalEquivalenceRelation_of_isEquivRel hrs)
  -- factor `f` as an extremal epimorphism followed by a monomorphism
  obtain ⟨F⟩ := HasStrongEpiMonoFactorisations.has_fac f
  have hkp' : IsKernelPair F.e r s := by
    have : IsKernelPair (F.e ≫ F.m) r s := by rw [F.fac]; exact hkp
    exact this.cancel_right_of_mono
  have he : extremalEpi C F.e := by
    intro cc d m hm
    have : Mono m := hm
    exact OFS.orthogonal_of_strongEpi_of_mono F.e m
  exact ⟨F.I, F.e, hkp',
    ⟨isColimitCoforkOfIsKernelPair UlmerBialgebras.isRegularCat_of_regular hkp' he hkp'.w⟩⟩

end CategoryTheory
