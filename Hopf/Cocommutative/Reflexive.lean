module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# From (co)reflexive (co)equalizers to all finite (co)limits

This file collects the elementary category-theoretic constructions needed to verify the
standing hypotheses of Newman's correspondence (`InternalGroups/SubgroupCorrespondence.lean`) in
concrete categories of (co)monoid objects.

The categories of interest — commutative monoid objects and cocommutative comonoid objects of
a symmetric monoidal category — do not have all (co)limits computed in the base, but they do
have

* all **reflexive coequalizers** and all **finite coproducts** (for monoid objects), resp.
* all **coreflexive equalizers** and all **finite products** (for comonoid objects),

and this is enough. This file treats the comonoid side:

* `UlmerBialgebras.hasEqualizer_of_coreflexive` — the equalizer of `f, g : A ⟶ B` is the equalizer
  of the coreflexive pair `⟨𝟙, f⟩, ⟨𝟙, g⟩ : A ⟶ A ⨯ B`;
* `UlmerBialgebras.hasEqualizers_of_coreflexive`, `UlmerBialgebras.hasFiniteLimits_of_coreflexive` —
  hence coreflexive equalizers and finite products give all finite limits.

The monoid side is the dual statement.

None of these results is declared as an instance: `HasCoequalizers C` implies
`HasReflexiveCoequalizers C` in Mathlib, so declaring the converse implication as an instance
would create a loop in typeclass resolution.  They are applied by hand in the files setting up
the two categories of interest.

## Main results

* `UlmerBialgebras.hasEqualizer_of_coreflexive`: in a category with coreflexive equalizers,
  `f, g : A ⟶ B` have an equalizer as soon as the product `A ⨯ B` exists.
* `UlmerBialgebras.hasEqualizers_of_coreflexive`: coreflexive equalizers and binary products give
  all equalizers.
* `UlmerBialgebras.hasFiniteLimits_of_coreflexive`: coreflexive equalizers and finite products give
  all finite limits.

## References

* Mathlib's `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` records the reduction of
  coequalizers to reflexive coequalizers using binary coproducts. The proofs here give the
  pair with its common section explicitly, and dualize it to equalizers.
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits Opposite

variable {C : Type u} [Category.{v} C]

/-! ## Coequalizers from reflexive coequalizers -/

/-! ## Equalizers from coreflexive equalizers -/

/-- **An equalizer as a coreflexive equalizer.**  The equalizer of `f, g : A ⟶ B` agrees with
the equalizer of the coreflexive pair `⟨𝟙 A, f⟩, ⟨𝟙 A, g⟩ : A ⟶ A ⨯ B`. -/
theorem hasEqualizer_of_coreflexive [HasCoreflexiveEqualizers C] {A B : C} (f g : A ⟶ B)
    [HasBinaryProduct A B] : HasEqualizer f g := by
  have : IsCoreflexivePair (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g) :=
    IsCoreflexivePair.mk' prod.fst (by simp) (by simp)
  have := HasCoreflexiveEqualizers.has_eq (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g)
  have hcond := equalizer.condition (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g)
  have hw : equalizer.ι (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g) ≫ f
      = equalizer.ι (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g) ≫ g := by
    have := congrArg (fun t => t ≫ (prod.snd : A ⨯ B ⟶ B)) hcond
    simpa using this
  have key : ∀ {Z : C} (h : Z ⟶ A), h ≫ f = h ≫ g →
      h ≫ prod.lift (𝟙 A) f = h ≫ prod.lift (𝟙 A) g := by
    intro Z h hh
    apply prod.hom_ext <;> simp [hh]
  refine HasLimit.mk ⟨Fork.ofι _ hw, Fork.IsLimit.mk _
    (fun s => equalizer.lift s.ι (key s.ι (Fork.condition s))) (fun s => ?_) (fun s m hm => ?_)⟩
  · exact equalizer.lift_ι _ _
  · have hm' : m ≫ equalizer.ι (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g) = s.ι := hm
    rw [← cancel_mono (equalizer.ι (prod.lift (𝟙 A) f) (prod.lift (𝟙 A) g)), hm',
      equalizer.lift_ι]

/-- A category with coreflexive equalizers and binary products has all equalizers. -/
theorem hasEqualizers_of_coreflexive [HasCoreflexiveEqualizers C] [HasBinaryProducts C] :
    HasEqualizers C := by
  constructor
  intro F
  have := hasEqualizer_of_coreflexive (F.map WalkingParallelPairHom.left)
    (F.map WalkingParallelPairHom.right)
  exact hasLimit_of_iso (diagramIsoParallelPair F).symm

/-- **A category with coreflexive equalizers and finite products has finite limits.** -/
theorem hasFiniteLimits_of_coreflexive [HasCoreflexiveEqualizers C] [HasFiniteProducts C] :
    HasFiniteLimits C :=
  haveI := hasEqualizers_of_coreflexive (C := C)
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-! ## Opposite categories -/

end UlmerBialgebras
