module

public import InternalGroups.GrpObjEffectiveRelation
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Foundations.CategoryTheory.Exact.SemiAbelian

/-!
# A criterion for the category of internal groups to be regular and Barr-exact

Let `C` be a cartesian monoidal category with finite limits, so that `Grp C` is pointed, finitely
complete and protomodular.  This file assembles the three ingredients which make `Grp C` an exact
category, in a form which asks nothing of `C` beyond properties available for the categories of
this development (cocommutative comonoids, affine schemes):

1. **Quotients.**  `Grp C` has reflexive coequalizers as soon as `C` does and the binary product
   of `C` preserves them (`Foundations/CategoryTheory/Grp/GrpReflexiveCoeq.lean`).  Since kernel
   pairs are
   reflexive, `Grp C` then has coequalizers of kernel pairs — the first requirement of
   regularity — *unconditionally*
   (`InternalGroups.Internal.hasCoequalizer_of_isKernelPair_of_hasReflexiveCoequalizers`).
2. **Stability.**  Regular epimorphisms have to be stable under base change; for internal groups
   of an extensive category the crucial instance of this, stability along kernels, comes from
   extensivity.
3. **Normality.**  An internal equivalence relation has to be recovered from its quotient.  This
   is `InternalGroups.Internal.RelNormalDetectsQuotient`: a generalized element of `X` killed by the
   coequalizer of the relation factors through the normal subobject `κ` of the relation.  It is
   the only genuinely non-formal input, and the one which in the Hopf setting is a Takeuchi-type
   faithful-flatness statement.

Granting 1–3, internal equivalence relations are effective
(`InternalGroups.Internal.exists_isKernelPair_of_relNormalDetectsQuotient`) and `Grp C` is regular
and Barr-exact (`InternalGroups.Internal.regular_of_relNormalDetectsQuotient`,
`InternalGroups.Internal.isBarrExact_of_relNormalDetectsQuotient`).

## Main definitions and results

* `InternalGroups.Internal.hasCoequalizer_of_isKernelPair_of_hasReflexiveCoequalizers`;
* `InternalGroups.Internal.RelNormalDetectsQuotient`;
* `InternalGroups.Internal.exists_isKernelPair_of_relNormalDetectsQuotient`;
* `InternalGroups.Internal.regular_of_relNormalDetectsQuotient`,
  `InternalGroups.Internal.isBarrExact_of_relNormalDetectsQuotient`.

## References

* [M. Barr, *Exact categories*][Ba]
* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
* [A. Carboni, S. Lack, R. F. C. Walters, *Introduction to extensive and distributive
  categories*][Lextensive]
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace InternalGroups
open CategoryTheory

namespace Internal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- **Kernel pairs of `Grp C` have coequalizers** as soon as `Grp C` has reflexive coequalizers:
a kernel pair is a reflexive pair, split by the lift of the identity. -/
theorem hasCoequalizer_of_isKernelPair_of_hasReflexiveCoequalizers
    [HasReflexiveCoequalizers (Grp C)] {X Y Z : Grp C} {f : X ⟶ Y}
    {g₁ g₂ : Z ⟶ X} (hk : IsKernelPair f g₁ g₂) : HasCoequalizer g₁ g₂ :=
  haveI : IsReflexivePair g₁ g₂ :=
    IsReflexivePair.mk' (hk.lift (𝟙 X) (𝟙 X) rfl) (hk.lift_fst _ _ _) (hk.lift_snd _ _ _)
  HasReflexiveCoequalizers.has_coeq _ _

variable [HasFiniteLimits C]

variable (C) in
/-- **The normality condition.**  For a reflexive, jointly monic relation `r₁, r₂ : R ⇉ X` of
`Grp C` and a coequalizer `q` of that relation, every generalized element of `X` annihilated by
`q` factors through the normal subobject `κ = (ker r₁ ↪ R) ≫ r₂` of the relation.

For `C = Set` this is the statement that the kernel of `X ⟶ X / N` is `N`; in the Hopf setting it
is the injectivity of Newman's correspondence between normal sub-Hopf-monoids and quotients. -/
def RelNormalDetectsQuotient : Prop :=
  ∀ ⦃R X Q : Grp C⦄ (r₁ r₂ : R ⟶ X) (q : X ⟶ Q) (w : r₁ ≫ q = r₂ ≫ q),
    IsColimit (Cofork.ofπ q w) →
    (∃ d : X ⟶ R, d ≫ r₁ = 𝟙 X ∧ d ≫ r₂ = 𝟙 X) →
    (∀ ⦃T : Grp C⦄ (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b) →
    ∀ ⦃T : Grp C⦄ (t : T ⟶ X), t ≫ q = (0 : T ⟶ Q) →
      ∃ v : T ⟶ relKernel r₁, v ≫ relNormal r₁ r₂ = t

/-- The normal subobject of a relation is annihilated by any morphism coequalizing the
relation. -/
theorem relNormal_comp_eq_trivial {R X Q : Grp C} (r₁ r₂ : R ⟶ X) (q : X ⟶ Q)
    (w : r₁ ≫ q = r₂ ≫ q) : relNormal r₁ r₂ ≫ q = (0 : relKernel r₁ ⟶ Q) := by
  rw [relNormal, Category.assoc, ← w, ← Category.assoc, relKernelι_comp, zero_comp]

variable [HasReflexiveCoequalizers (Grp C)]

/-- **Internal equivalence relations of `Grp C` are effective**, granting the normality condition:
a reflexive, jointly monic relation is the kernel pair of its coequalizer, which exists because
the relation is reflexive. -/
theorem exists_isKernelPair_of_relNormalDetectsQuotient (h : RelNormalDetectsQuotient C)
    {R X : Grp C} {r₁ r₂ : R ⟶ X} (hrefl : ∃ d : X ⟶ R, d ≫ r₁ = 𝟙 X ∧ d ≫ r₂ = 𝟙 X)
    (hjm : ∀ ⦃T : Grp C⦄ (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b) :
    ∃ (Q : Grp C) (q : X ⟶ Q), IsKernelPair q r₁ r₂ ∧ IsRegularEpi q := by
  obtain ⟨d, hd₁, hd₂⟩ := hrefl
  have : IsReflexivePair r₁ r₂ := IsReflexivePair.mk' d hd₁ hd₂
  have := HasReflexiveCoequalizers.has_coeq r₁ r₂
  have hq := coequalizerIsCoequalizer r₁ r₂
  have hreg : IsRegularEpi (coequalizer.π r₁ r₂) :=
    ⟨⟨{ W := R
        left := r₁
        right := r₂
        w := coequalizer.condition r₁ r₂
        isColimit := hq }⟩⟩
  refine ⟨coequalizer r₁ r₂, coequalizer.π r₁ r₂, ?_, hreg⟩
  refine isKernelPair_of_relNormal_isKernel ⟨d, hd₁, hd₂⟩ hjm _
    (relNormal_comp_eq_trivial r₁ r₂ _ (coequalizer.condition r₁ r₂)) ?_
  intro T t ht
  exact h r₁ r₂ _ (coequalizer.condition r₁ r₂) hq ⟨d, hd₁, hd₂⟩ hjm t ht

/-- **`Grp C` is a regular category** granting the normality condition and the stability of
regular epimorphisms under base change: quotients by kernel pairs are available for free. -/
theorem regular_of_relNormalDetectsQuotient
    (hstab : MorphismProperty.IsStableUnderBaseChange (MorphismProperty.regularEpi (Grp C))) :
    Regular (Grp C) :=
  { __ := (inferInstance : HasFiniteLimits (Grp C))
    hasCoequalizer_of_isKernelPair := fun hk =>
      hasCoequalizer_of_isKernelPair_of_hasReflexiveCoequalizers hk
    regularEpiIsStableUnderBaseChange := hstab }

/-- **`Grp C` is Barr-exact** granting the normality condition and the stability of regular
epimorphisms under base change. -/
theorem isBarrExact_of_relNormalDetectsQuotient (h : RelNormalDetectsQuotient C)
    (hstab : MorphismProperty.IsStableUnderBaseChange (MorphismProperty.regularEpi (Grp C))) :
    IsBarrExact (Grp C) where
  __ := regular_of_relNormalDetectsQuotient hstab
  isKernelPair_of_isInternalEquivalenceRelation hrel :=
    let ⟨Q, q, hk, _⟩ :=
      exists_isKernelPair_of_relNormalDetectsQuotient h hrel.refl hrel.jointly_mono
    ⟨Q, q, hk⟩

end Internal

end InternalGroups
