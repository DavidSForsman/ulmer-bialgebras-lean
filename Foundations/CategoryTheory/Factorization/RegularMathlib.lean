module

public import Foundations.CategoryTheory.Factorization.ExactCategory
public import Foundations.CategoryTheory.Factorization.StableRegularOFS
public import Foundations.CategoryTheory.Factorization.RegularCharacterization

/-!
# The paper's regular and exact categories are Mathlib's

Definition 6.4 of the paper defines regular and exact categories through an orthogonal
factorization system (`UlmerBialgebras.IsRegularCat`, `UlmerBialgebras.IsExactCat`). This file
shows that they are Mathlib's regular categories (`CategoryTheory.Regular`) and the Barr-exact
ones (`CategoryTheory.BarrExact`). Proofs that follow the paper use the paper's form; everything
else uses Mathlib's.

## Main results

* `UlmerBialgebras.isEquivRel_iff_isEquivalenceRelation`: with pullbacks, the paper's internal
  equivalence relations are Mathlib's;
* `UlmerBialgebras.isRegularCat_iff_regular`: the paper's regular categories are Mathlib's;
* `UlmerBialgebras.isExactCat_iff_barrExact`: the paper's exact categories are the Barr-exact ones.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4
* [M. Barr, *Exact Categories*][Ba]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

/-- A Mathlib equivalence relation is an internal equivalence relation in the paper's sense. -/
lemma EquivalenceRelation.isEquivRel {R X : C} {p₁ p₂ : R ⟶ X} (e : EquivalenceRelation p₁ p₂) :
    IsEquivRel p₁ p₂ where
  jointly_mono a b h₁ h₂ := e.right_cancellation a b h₁ h₂
  refl f := ⟨f ≫ e.r, by simp, by simp⟩
  symm d := ⟨d ≫ e.s, by rw [Category.assoc, e.symmetry₁], by rw [Category.assoc, e.symmetry₂]⟩
  trans d d' hdd' := ⟨PullbackCone.IsLimit.lift e.isLimit d d' hdd' ≫ e.t,
    by rw [Category.assoc, e.transitivity₁, ← Category.assoc, PullbackCone.IsLimit.lift_fst],
    by rw [Category.assoc, e.transitivity₂, ← Category.assoc, PullbackCone.IsLimit.lift_snd]⟩

/-- With pullbacks, an internal equivalence relation in the paper's sense is a Mathlib
equivalence relation (Mathlib asks for a limiting pullback cone for transitivity). -/
noncomputable def IsEquivRel.equivalenceRelation [HasPullbacks C] {R X : C} {p₁ p₂ : R ⟶ X}
    (h : IsEquivRel p₁ p₂) : EquivalenceRelation p₁ p₂ where
  right_cancellation _ a b h₁ h₂ := h.jointly_mono a b h₁ h₂
  r := h.diagonal.choose
  reflexivity₁ := h.diagonal.choose_spec.1
  reflexivity₂ := h.diagonal.choose_spec.2
  s := h.involution.choose
  symmetry₁ := h.involution.choose_spec.1
  symmetry₂ := h.involution.choose_spec.2
  c := PullbackCone.mk (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition
  isLimit := pullbackIsPullback p₂ p₁
  t := (h.trans (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition).choose
  transitivity₁ :=
    (h.trans (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition).choose_spec.1
  transitivity₂ :=
    (h.trans (pullback.fst p₂ p₁) (pullback.snd p₂ p₁) pullback.condition).choose_spec.2

/-- With pullbacks, the paper's internal equivalence relations are exactly Mathlib's equivalence
relations. -/
lemma isEquivRel_iff_isEquivalenceRelation [HasPullbacks C] {R X : C} (p₁ p₂ : R ⟶ X) :
    IsEquivRel p₁ p₂ ↔ IsEquivalenceRelation p₁ p₂ :=
  ⟨fun h => h.equivalenceRelation.isEquivalenceRelation,
    fun ⟨⟨e⟩⟩ => EquivalenceRelation.isEquivRel e⟩

/-- **Definition 6.4 versus Mathlib, regularity.** A category is regular in the paper's sense
(finite limits and a stable orthogonal factorization system whose right class is the class of
monomorphisms) if and only if it is regular in Mathlib's sense. -/
theorem isRegularCat_iff_regular : IsRegularCat C ↔ Regular C :=
  ⟨regular_of_isRegularCat, fun _ => isRegularCat_of_regular⟩

/-- **Definition 6.4 versus Mathlib, exactness.** A category is exact in the paper's sense if and
only if it is Barr-exact. -/
theorem isExactCat_iff_barrExact : IsExactCat C ↔ BarrExact C := by
  constructor
  · intro hC
    have := regular_of_isRegularCat hC.regular
    refine BarrExact.mk' fun p₁ p₂ _ => ?_
    obtain ⟨d, f, hk, -⟩ :=
      hC.effective p₁ p₂ ((isEquivRel_iff_isEquivalenceRelation p₁ p₂).2 inferInstance)
    exact ⟨d, f, hk⟩
  · intro hC
    refine ⟨UlmerBialgebras.isRegularCat_of_regular, fun r s hrs => ?_⟩
    have := (isEquivRel_iff_isEquivalenceRelation r s).1 hrs
    obtain ⟨e⟩ :=
      (BarrExact.isEffectiveEquivalenceRelation r s).nonempty_effectiveEquivalenceRelation
    exact ⟨e.B, e.π, e.isKernelPair, ⟨e.isCoequalizer⟩⟩

/-- In a Barr-exact category, every internal equivalence relation in the paper's sense is the
kernel pair of some morphism. -/
lemma BarrExact.exists_isKernelPair_of_isEquivRel [BarrExact C] {R X : C} {p₁ p₂ : R ⟶ X}
    (h : IsEquivRel p₁ p₂) : ∃ (Y : C) (f : X ⟶ Y), IsKernelPair f p₁ p₂ := by
  have := (isEquivRel_iff_isEquivalenceRelation p₁ p₂).1 h
  exact BarrExact.exists_isKernelPair p₁ p₂

end UlmerBialgebras
