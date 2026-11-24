module

public import Foundations.CategoryTheory.Factorization.RegularExact

/-!
# Elementary toolkit for regular categories

This file collects the basic "regular logic" toolkit that is used to reason with
generalized elements in a regular category (`UlmerBialgebras.IsRegularCat`).

## Main results

* `UlmerBialgebras.extremalEpi_epi` — in a category with equalizers, an extremal epimorphism is an
  epimorphism;
* `UlmerBialgebras.IsRegularCat.exists_cover` — every generalized element of the codomain of an
  extremal epimorphism lifts along it after precomposition with another extremal epimorphism
  (a *cover*);
* `UlmerBialgebras.IsRegularCat.exists_extremalEpi_mono_factorization` — image factorizations;
* `UlmerBialgebras.Factors` — a generalized element factors through a morphism.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 6.4
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- A morphism left orthogonal to all monomorphisms is an epimorphism, as soon as
equalizers exist. -/
lemma extremalEpi_epi [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (hf : extremalEpi C f) : Epi f := by
  constructor
  intro Z g h hgh
  have hmono : (MorphismProperty.monomorphisms C) (equalizer.ι g h) := by
    rw [MorphismProperty.monomorphisms.iff]; infer_instance
  obtain ⟨k, ⟨-, k2⟩, -⟩ := hf (equalizer.ι g h) hmono (equalizer.lift f hgh) (𝟙 Y)
    (by rw [equalizer.lift_ι, Category.comp_id])
  calc g = (k ≫ equalizer.ι g h) ≫ g := by rw [k2, Category.id_comp]
    _ = (k ≫ equalizer.ι g h) ≫ h := by rw [Category.assoc, Category.assoc, equalizer.condition]
    _ = h := by rw [k2, Category.id_comp]

/-- The class of extremal epimorphisms contains the isomorphisms. -/
lemma extremalEpi_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : extremalEpi C f :=
  leftOrth_of_isIso _ f

/-- The class of extremal epimorphisms is closed under composition. -/
lemma extremalEpi_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : extremalEpi C f)
    (hg : extremalEpi C g) : extremalEpi C (f ≫ g) :=
  leftOrth_comp hf hg

/-- An extremal epimorphism which is a monomorphism is an isomorphism. -/
lemma isIso_of_extremalEpi_of_mono {X Y : C} {f : X ⟶ Y} (hf : extremalEpi C f) (hm : Mono f) :
    IsIso f := by
  obtain ⟨h, ⟨h1, h2⟩, -⟩ := hf f hm (𝟙 X) (𝟙 Y) (by simp)
  exact ⟨h, h1, h2⟩

namespace IsRegularCat

variable (hC : IsRegularCat C)
include hC

/-- Image factorizations in a regular category. -/
lemma exists_extremalEpi_mono_factorization {X Y : C} (f : X ⟶ Y) :
    ∃ (I : C) (e : X ⟶ I) (m : I ⟶ Y), extremalEpi C e ∧ Mono m ∧ e ≫ m = f := by
  obtain ⟨S, hSM⟩ := hC.exists_ofs
  obtain ⟨I, e, m, he, hm, hfac⟩ := S.fact f
  exact ⟨I, e, m, by rwa [← S.e_eq_extremalEpi hSM], by rwa [hSM] at hm, hfac⟩

/-- Every generalized element of the codomain of an extremal epimorphism lifts along it,
after passing to a cover. -/
lemma exists_cover {A B : C} {f : A ⟶ B} (hf : extremalEpi C f) {T : C} (b : T ⟶ B) :
    ∃ (T' : C) (p : T' ⟶ T) (a : T' ⟶ A), extremalEpi C p ∧ a ≫ f = p ≫ b := by
  have := hC.hasFiniteLimits
  refine ⟨pullback f b, pullback.snd f b, pullback.fst f b, ?_, pullback.condition⟩
  exact hC.stable.of_isPullback (IsPullback.of_hasPullback f b) hf

end IsRegularCat

/-- A generalized element `x` of `B` **factors through** the subobject `m`. -/
def Factors {I B : C} (m : I ⟶ B) {T : C} (x : T ⟶ B) : Prop := ∃ y : T ⟶ I, y ≫ m = x

end UlmerBialgebras
