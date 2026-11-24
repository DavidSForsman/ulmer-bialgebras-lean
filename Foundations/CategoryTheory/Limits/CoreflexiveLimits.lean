module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# All equalizers and pullbacks from coreflexive equalizers and binary products

A **coreflexive pair** is a pair `f g : X ⟶ Y` with a common retraction `r : Y ⟶ X`, i.e.
`f ≫ r = 𝟙 X = g ≫ r`.  This file shows that binary products together with coreflexive
equalizers already give *all* equalizers and *all* pullbacks, hence (with a terminal object)
all finite limits.

The equalizer of an arbitrary pair `f g : X ⟶ Y` is the equalizer of the **coreflexive** pair
`⟨𝟙, f⟩, ⟨𝟙, g⟩ : X ⟶ X × Y`, whose common retraction is the first projection.  Pullbacks are
then equalizers of `π₁ ≫ f` and `π₂ ≫ g` over the product, and finite limits come from
Mathlib's `hasFiniteLimits_of_hasTerminal_and_pullbacks`.

This is the generic finite-limit bridge required for the cocommutative-comonoid setting, where
the tensor product of `A` is the categorical product and the tensor preserves coreflexive
equalizers; nothing here depends on comonoids.

## Main results

* `CategoryTheory.diagPair`, `isCoreflexivePair_diagPair`: the coreflexive pair attached to two
  parallel morphisms;
* `CategoryTheory.hasEqualizer_of_hasCoreflexiveEqualizers`;
* `CategoryTheory.hasEqualizers_of_hasCoreflexiveEqualizers`;
* `CategoryTheory.hasPullbacks_of_hasCoreflexiveEqualizers`;
* `CategoryTheory.hasFiniteLimits_of_hasTerminal_and_coreflexiveEqualizers`.

## References

* P. T. Johnstone, *Sketches of an Elephant: A Topos Theory Compendium*, Vol. 1 (2002), §A1.2
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Equalizers

variable [HasBinaryProducts C]

/-- The pairing `⟨𝟙, f⟩ : X ⟶ X ⨯ Y`. -/
noncomputable def diagPair {X Y : C} (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 X) f

/-- The first component of `⟨𝟙, f⟩` is the identity. -/
@[simp]
lemma diagPair_fst {X Y : C} (f : X ⟶ Y) : diagPair f ≫ prod.fst = 𝟙 X :=
  prod.lift_fst _ _

/-- The second component of `⟨𝟙, f⟩` is `f`. -/
@[simp]
lemma diagPair_snd {X Y : C} (f : X ⟶ Y) : diagPair f ≫ prod.snd = f :=
  prod.lift_snd _ _

variable [HasCoreflexiveEqualizers C]

/-- The pair `⟨𝟙, f⟩, ⟨𝟙, g⟩` is coreflexive, with common retraction the first projection. -/
instance isCoreflexivePair_diagPair {X Y : C} (f g : X ⟶ Y) :
    IsCoreflexivePair (diagPair f) (diagPair g) :=
  IsCoreflexivePair.mk' prod.fst (diagPair_fst f) (diagPair_fst g)

/-- In a category with binary products and coreflexive equalizers, two parallel morphisms `f`
and `g` have an equalizer: the equalizer of the coreflexive pair `⟨𝟙, f⟩, ⟨𝟙, g⟩`. -/
theorem hasEqualizer_of_hasCoreflexiveEqualizers {X Y : C} (f g : X ⟶ Y) :
    HasEqualizer f g := by
  refine ⟨Fork.ofι (equalizer.ι (diagPair f) (diagPair g)) ?_, ?_⟩
  · have h := equalizer.condition (diagPair f) (diagPair g)
    have h' := h =≫ prod.snd
    simpa only [Category.assoc, diagPair_snd] using h'
  · refine Fork.IsLimit.mk _ (fun c => ?_) ?_ ?_
    · have h : c.ι ≫ diagPair f = c.ι ≫ diagPair g := by
        apply prod.hom_ext <;> simp [c.condition]
      exact equalizer.lift (f := diagPair f) (g := diagPair g) c.ι h
    · intro c
      exact equalizer.lift_ι _ _
    · intro c m hm
      exact equalizer.hom_ext (f := diagPair f) (g := diagPair g) (by
        rw [equalizer.lift_ι]
        exact hm)

/-- **All equalizers from coreflexive equalizers and binary products.** -/
theorem hasEqualizers_of_hasCoreflexiveEqualizers : HasEqualizers C := by
  have : ∀ {X Y : C} {f g : X ⟶ Y}, HasLimit (parallelPair f g) :=
    fun {X Y} {f g} => hasEqualizer_of_hasCoreflexiveEqualizers f g
  exact hasEqualizers_of_hasLimit_parallelPair C

end Equalizers

section Pullbacks

variable [HasBinaryProducts C]

/-- **All pullbacks from coreflexive equalizers and binary products.** -/
theorem hasPullbacks_of_hasCoreflexiveEqualizers [HasCoreflexiveEqualizers C] :
    HasPullbacks C :=
  letI := hasEqualizers_of_hasCoreflexiveEqualizers (C := C)
  hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C

end Pullbacks

section FiniteLimits

/-- **All finite limits from a terminal object, coreflexive equalizers and binary products.** -/
theorem hasFiniteLimits_of_hasTerminal_and_coreflexiveEqualizers [HasTerminal C]
    [HasBinaryProducts C] [HasCoreflexiveEqualizers C] : HasFiniteLimits C :=
  letI := hasPullbacks_of_hasCoreflexiveEqualizers (C := C)
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end FiniteLimits

end CategoryTheory
