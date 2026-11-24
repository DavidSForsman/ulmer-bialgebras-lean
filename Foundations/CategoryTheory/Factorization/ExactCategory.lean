module

public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# Barr-exact categories

A category is *(Barr-)exact* if it is regular (`CategoryTheory.Regular`) and every equivalence
relation (`CategoryTheory.IsEquivalenceRelation`) is effective
(`CategoryTheory.IsEffectiveEquivalenceRelation`), i.e. the kernel pair of its coequalizer.

Mathlib provides regular categories and effective equivalence relations, but no class for exact
categories. This file adds one, `CategoryTheory.BarrExact`, written in Mathlib's conventions so that
it could be upstreamed. The name avoids a clash with the unrelated notion of a Quillen exact
category, and with exactness of functors and of complexes.

## Main definitions and results

* `CategoryTheory.BarrExact` — a regular category in which every equivalence relation is effective.
* `CategoryTheory.Regular.isEffectiveEquivalenceRelation_of_isKernelPair` — in a regular category,
  a kernel pair is an effective equivalence relation.
* `CategoryTheory.BarrExact.mk'` — a regular category is exact as soon as every equivalence relation
  is the kernel pair of *some* morphism (Barr's original definition).
* `CategoryTheory.BarrExact.exists_isKernelPair` — the converse.

## References

* [M. Barr, *Exact categories*][Ba]
* [M. Gran, *An Introduction to Regular Categories*][inbook]
* <https://ncatlab.org/nlab/show/exact+category>
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/-- A category is **Barr-exact** (or *exact* in the sense of Barr) if it is regular and every
equivalence relation in it is effective, i.e. it is the kernel pair of its coequalizer. -/
class BarrExact : Prop extends Regular C where
  /-- Every equivalence relation is effective. -/
  isEffectiveEquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) [IsEquivalenceRelation p₁ p₂] :
    IsEffectiveEquivalenceRelation p₁ p₂

variable {C}

/-- The coequalizer cofork of a reflexive pair is a pushout square. -/
lemma IsPushout.of_isColimit_cofork_of_reflexive {R X Q : C} {p₁ p₂ : R ⟶ X} {π : X ⟶ Q}
    {w : p₁ ≫ π = p₂ ≫ π} (h : IsColimit (Cofork.ofπ π w)) (r : X ⟶ R) (h₁ : r ≫ p₁ = 𝟙 X)
    (h₂ : r ≫ p₂ = 𝟙 X) : IsPushout p₁ p₂ π π := by
  have heq : ∀ {W : C} (a b : X ⟶ W), p₁ ≫ a = p₂ ≫ b → a = b := fun a b hab => by
    calc a = (r ≫ p₁) ≫ a := by rw [h₁, Category.id_comp]
      _ = (r ≫ p₂) ≫ b := by rw [Category.assoc, hab, Category.assoc]
      _ = b := by rw [h₂, Category.id_comp]
  have hepi : Epi π := epi_of_isColimit_cofork h
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ (fun s => Cofork.IsColimit.desc h s.inl
    (by rw [s.condition, heq s.inl s.inr s.condition])) (fun s => ?_) (fun s => ?_)
    (fun s m h₁' _ => ?_)⟩⟩
  · exact Cofork.IsColimit.π_desc h
  · exact (Cofork.IsColimit.π_desc h).trans (heq s.inl s.inr s.condition)
  · rw [← cancel_epi π, h₁']
    exact (Cofork.IsColimit.π_desc' h _ _).symm

namespace Regular

variable [Regular C]

/-- In a regular category, the kernel pair of a morphism is the kernel pair of its coequalizer. -/
lemma isKernelPair_coequalizer_π {R X Y : C} {f : X ⟶ Y} {p₁ p₂ : R ⟶ X}
    (hf : IsKernelPair f p₁ p₂) :
    haveI : HasCoequalizer p₁ p₂ := hasCoequalizer_of_isKernelPair hf
    IsKernelPair (coequalizer.π p₁ p₂) p₁ p₂ := by
  have : HasCoequalizer p₁ p₂ := hasCoequalizer_of_isKernelPair hf
  refine IsKernelPair.cancel_right (f₂ := coequalizer.desc f hf.w) (coequalizer.condition _ _) ?_
  simpa using hf

/-- In a regular category, a kernel pair is an effective equivalence relation. -/
lemma isEffectiveEquivalenceRelation_of_isKernelPair {R X Y : C} {f : X ⟶ Y} {p₁ p₂ : R ⟶ X}
    (hf : IsKernelPair f p₁ p₂) : IsEffectiveEquivalenceRelation p₁ p₂ := by
  have : HasCoequalizer p₁ p₂ := hasCoequalizer_of_isKernelPair hf
  let e : EquivalenceRelation p₁ p₂ :=
    IsKernelPair.equivalenceRelation f p₁ p₂ (pullbackIsPullback p₂ p₁) hf
  exact ⟨⟨{ e with
    B := coequalizer p₁ p₂
    π := coequalizer.π p₁ p₂
    isKernelPair := isKernelPair_coequalizer_π hf
    isPushout := IsPushout.of_isColimit_cofork_of_reflexive (coequalizerIsCoequalizer p₁ p₂)
      e.r e.reflexivity₁ e.reflexivity₂ }⟩⟩

end Regular

namespace BarrExact

/-- A regular category in which every equivalence relation is the kernel pair of some morphism is
Barr-exact. -/
lemma mk' [Regular C]
    (h : ∀ {R X : C} (p₁ p₂ : R ⟶ X) [IsEquivalenceRelation p₁ p₂],
      ∃ (Y : C) (f : X ⟶ Y), IsKernelPair f p₁ p₂) : BarrExact C where
  isEffectiveEquivalenceRelation p₁ p₂ _ := by
    obtain ⟨_, _, hf⟩ := h p₁ p₂
    exact Regular.isEffectiveEquivalenceRelation_of_isKernelPair hf

/-- In a Barr-exact category every equivalence relation is the kernel pair of some morphism. -/
lemma exists_isKernelPair [BarrExact C] {R X : C} (p₁ p₂ : R ⟶ X) [IsEquivalenceRelation p₁ p₂] :
    ∃ (Y : C) (f : X ⟶ Y), IsKernelPair f p₁ p₂ := by
  obtain ⟨e⟩ :=
    (BarrExact.isEffectiveEquivalenceRelation p₁ p₂).nonempty_effectiveEquivalenceRelation
  exact ⟨e.B, e.π, e.isKernelPair⟩

end BarrExact

end CategoryTheory
