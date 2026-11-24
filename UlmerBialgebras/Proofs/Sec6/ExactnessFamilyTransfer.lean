module

public import UlmerBialgebras.Proofs.Sec6.Sec6Factorization
public import Foundations.CategoryTheory.Exact.JointlyConservative
public import Foundations.CategoryTheory.Limits.PiColimits
public import Foundations.CategoryTheory.Limits.PiLimits

/-!
# Exactness transfer to a jointly conservative family

Lemma 6.5 (3) applies to the single functor into the product of a jointly conservative
family. This file packages that step for the descent argument of Corollary 6.11.

## Main results

* `UlmerBialgebras.Paper.isBarrExact_pi`: products of exact categories with reflexive
  coequalizers are exact.
* `UlmerBialgebras.Paper.isBarrExact_of_family_transfer`: Lemma 6.5 (3) for a jointly
  conservative family preserving finite limits and reflexive coequalizers.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.5 (3) and Corollary 6.11
-/

@[expose] public section

universe w v v₂ u u₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

variable {I : Type w} {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

/-- A product has reflexive coequalizers when its factors do. -/
lemma hasReflexiveCoequalizers_pi [∀ i, HasReflexiveCoequalizers (D i)] :
    HasReflexiveCoequalizers (∀ i, D i) := by
  have : ∀ i, HasColimitsOfShape WalkingReflexivePair (D i) :=
    fun _ => hasReflexiveCoequalizers_iff.2 inferInstance
  exact hasReflexiveCoequalizers_iff.1 inferInstance

/-- Products of Barr-exact categories with reflexive coequalizers are Barr-exact. -/
lemma isBarrExact_pi [∀ i, CategoryTheory.IsBarrExact (D i)]
    [∀ i, HasReflexiveCoequalizers (D i)] : CategoryTheory.IsBarrExact (∀ i, D i) := by
  have := hasReflexiveCoequalizers_pi (D := D)
  have hcons : CategoryTheory.JointlyConservative (fun i => Pi.eval D i) := by
    constructor
    intro X Y f hf
    exact (isIso_pi_iff f).2 fun i => hf i
  refine CategoryTheory.isBarrExact_of_jointlyConservative (fun i => Pi.eval D i)
    hcons ?_ ?_ ?_
  · refine fun i => ⟨fun X Y r s h => ?_⟩
    have := h
    infer_instance
  · intro X Y Z f r s h
    have : IsReflexivePair r s := IsReflexivePair.mk'
      (h.lift (𝟙 X) (𝟙 X) rfl) (h.lift_fst _ _ _) (h.lift_snd _ _ _)
    infer_instance
  · intro R X r s h
    have := h.isReflexivePair
    infer_instance

/-- A category `C` with finite limits and reflexive coequalizers is Barr-exact if a jointly
conservative family of functors `F i : C ⥤ D i` to Barr-exact categories preserves finite limits
and reflexive coequalizers (Lemma 6.5 (3) for the functor into the product). -/
theorem isBarrExact_of_family_transfer {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    [HasReflexiveCoequalizers C] [∀ i, CategoryTheory.IsBarrExact (D i)]
    [∀ i, HasReflexiveCoequalizers (D i)] (F : ∀ i, C ⥤ D i)
    [∀ i, PreservesFiniteLimits (F i)]
    (hrefl : ∀ i, CategoryTheory.PreservesReflexiveCoeq (F i))
    (hcons : CategoryTheory.JointlyConservative F) : CategoryTheory.IsBarrExact C := by
  let U := Functor.pi' F
  have : U.ReflectsIsomorphisms := ⟨fun f hf => hcons.isIso_of_forall f fun i => by
    have : IsIso (U.map f) := hf
    exact (isIso_pi_iff (U.map f)).1 inferInstance i⟩
  have : PreservesFiniteLimits U := ⟨fun _ _ _ => inferInstance⟩
  have hmono : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Mono (U.map f) → Mono f := by
    intro X Y f hf
    have : ReflectsLimitsOfShape WalkingCospan U :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact U.mono_of_mono_map hf
  have hce : ∀ ⦃R X : C⦄ (r s : R ⟶ X), IsEquivalenceRelation r s →
      HasCoequalizer r s ∧ PreservesColimit (parallelPair r s) U := by
    intro R X r s h
    have hr := ((CategoryTheory.isInternalEquivalenceRelation_iff r s).2 h).isReflexivePair
    have := hr
    have : ∀ i, PreservesColimit (parallelPair r s) (F i) := fun i => (hrefl i).preserves r s hr
    exact ⟨inferInstance, inferInstance⟩
  have := isBarrExact_pi (D := D)
  exact CategoryTheory.isBarrExact_iff_barrExact.2
    ((lem_6_5 U hmono).2.2 hce inferInstance
      (CategoryTheory.isBarrExact_iff_barrExact.1 inferInstance))

end UlmerBialgebras.Paper
