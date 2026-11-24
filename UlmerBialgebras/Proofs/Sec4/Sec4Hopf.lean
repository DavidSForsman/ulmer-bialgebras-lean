module

public import Foundations.CategoryTheory.Limits.DegenerateWide
public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import UlmerBialgebras.Proofs.Sec4.HopfModelLimits
public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushoutModel
public import UlmerBialgebras.Proofs.Sec4.RegMonoWidePullbackModel
public import UlmerBialgebras.Kan.ColimKanCreates

/-!
# Solution: Example 4.20 (limits and colimits of Hopf monoids)

`C` is a braided monoidal category and `U : M^{T_Hopf} → M₀` the forgetful 1-cell of its
Hopf model (`UlmerBialgebras/Paper/Sec3DefsHopfModel.lean`); `M₀` is `C` itself, indexed by the
single sort.
The paper assumes `C` symmetric monoidal closed, complete and cocomplete, with `⊗`
preserving finite limits in each variable; each statement below uses only the part of
these hypotheses it needs. The statements are instances of Corollary 4.17 (and its dual)
and Theorem 4.19 (and its dual).

## Main results

* `UlmerBialgebras.Paper.ex_4_20_1_coeq`: Example 4.20 (1), for `C` monoidal closed, `U` strictly
  creates reflexive coequalizers.
* `UlmerBialgebras.Paper.ex_4_20_1_eq`: Example 4.20 (1), if `⊗` preserves finite limits in each
  variable, `U` strictly creates coreflexive equalizers.
* `UlmerBialgebras.Paper.ex_4_20_2_pushout`: Example 4.20 (2), for `C` monoidal closed with
  pullbacks, `U` strictly creates wide pushouts of families it sends to regular epimorphisms.
* `UlmerBialgebras.Paper.ex_4_20_2_pullback`: Example 4.20 (2), if `⊗` preserves finite limits in
  each variable and `C` has pushouts, `U` strictly creates finite wide pullbacks of families it
  sends to regular monomorphisms.
* `UlmerBialgebras.Paper.ex_4_20_3`: Example 4.20 (3), for `C` monoidal closed, `U` strictly creates
  filtered colimits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20,
  Corollary 4.17 and Theorem 4.19
-/

@[expose] public section

universe u v

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory Limits

/-- **Example 4.20 (1)** ([forsman2026syntactic]), reflexive coequalizers: if `C` is monoidal
closed, `U` strictly creates reflexive coequalizers. -/
theorem ex_4_20_1_coeq (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (J : Cat.{v, u})
    (e : WalkingReflexivePair ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C) :
    StrictlyCreatesLeftKan (toOne J) d (HopfModel.forget C) := by
  have : IsSifted (J : Type u) := IsSifted.isSifted_of_equiv e.symm
  exact thy_strictlyCreates_colimits (HopfModel.hopfModel C) HopfEx.oneSig HopfEx.theory J
    (HopfModel.Internal.colimitsComponentwise _ (fun _ => inferInstance)) d

/-- **Example 4.20 (1)** ([forsman2026syntactic]), coreflexive equalizers: if `⊗` preserves finite
limits in each variable, `U` strictly creates coreflexive equalizers. -/
theorem ex_4_20_1_eq (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [∀ X : C, PreservesFiniteLimits (tensorLeft X)] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] [HasChosenProductsOfSize.{0} Cat.{v, u}]
    (J : Cat.{v, u}) (e : WalkingCoreflexivePair ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C) :
    StrictlyCreatesRightKan (toOne J) d (HopfModel.forget C) := by
  have : IsCosifted (J : Type u) :=
    IsSifted.isSifted_of_equiv (C := WalkingCoreflexivePairᵒᵖ) e.op.symm
  exact thy_strictlyCreates_limits (HopfModel.hopfModel C) HopfEx.oneSig HopfEx.theory J
    (HopfModel.Internal.limitsComponentwise _
      (fun X => HopfModel.Internal.preservesCoreflexive_of_equiv (tensorLeft X) e)) d

/-- **Example 4.20 (2)** ([forsman2026syntactic]), wide pushouts: if `C` is monoidal closed and has
pullbacks, `U` strictly creates the wide pushouts of families of morphisms of `M^{T_Hopf}` that `U`
sends to regular epimorphisms. -/
theorem ex_4_20_2_pushout (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] [HasPullbacks C] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] [HasChosenProductsOfSize.{0} Cat.{v, u}] (K : Type v)
    (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C)
    (hd : ∀ j, Nonempty (RegularEpi ((d ≫ HopfModel.forget C).toFunctor.map
        (e.functor.map (WidePushoutShape.Hom.init j))))) :
    StrictlyCreatesLeftKan (toOne J) d (HopfModel.forget C) := by
  classical
  cases subsingleton_or_nontrivial K with
  | inr h =>
    have := h
    exact RegEpiWide.thy_strictlyCreates_widePushouts (HopfModel.hopfModel C)
      HopfEx.oneSig HopfEx.theory K
      (fun _ => HopfModel.Internal.regEpisAreReflexiveCoequalizers_of_hasPullbacks (X := C))
      (HopfModel.Internal.widePushoutsComponentwise K) J e d hd
  | inl h =>
    have := h
    obtain ⟨j, ⟨hj⟩⟩ := widePushoutShape_exists_isTerminal K
    apply (HopfModel.hopfModel C).thy_strictlyCreates_leftKan_of_fn
      HopfEx.oneSig HopfEx.theory _ ?_ d
    intro B dd
    have : PreservesColimitsOfShape (J : Type u) ((HopfModel.hopfModel C).fn B).toFunctor :=
      preservesColimitsOfShape_of_isTerminal (hj.isTerminalObj e.functor) _
    exact RegEpiWide.preservesLeftKan_of_preservesColimit_single _ dd

/-- **Example 4.20 (2)** ([forsman2026syntactic]), joint pullbacks: if `⊗` preserves finite limits
in each variable and `C` has pushouts, `U` strictly creates the joint pullbacks of finite families
of morphisms of `M^{T_Hopf}` that `U` sends to regular monomorphisms. -/
theorem ex_4_20_2_pullback (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [∀ X : C, PreservesFiniteLimits (tensorLeft X)] [HasPushouts C]
    [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (K : Type v) [Finite K]
    (J : Cat.{v, u}) (e : WidePullbackShape K ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C)
    (hd : ∀ j, Nonempty (RegularMono ((d ≫ HopfModel.forget C).toFunctor.map
        (e.functor.map (WidePullbackShape.Hom.term j))))) :
    StrictlyCreatesRightKan (toOne J) d (HopfModel.forget C) := by
  classical
  cases subsingleton_or_nontrivial K with
  | inr h =>
    have := h
    exact RegMonoWide.thy_strictlyCreates_widePullbacks (HopfModel.hopfModel C) HopfEx.oneSig
      HopfEx.theory K
      (fun _ => RegMonoWide.regularMonosAreCoreflexiveEqualizers_of_hasCokernelPairs (X := C)
        (fun ⦃_ _⦄ _ => inferInstance))
      (HopfModel.Internal.widePullbacksComponentwise K) J e d hd
  | inl h =>
    have := h
    obtain ⟨j, ⟨hj⟩⟩ := widePullbackShape_exists_isInitial K
    apply (HopfModel.hopfModel C).thy_strictlyCreates_rightKan_of_fn
      HopfEx.oneSig HopfEx.theory _ ?_ d
    intro B dd
    have : PreservesLimitsOfShape (J : Type u) ((HopfModel.hopfModel C).fn B).toFunctor :=
      preservesLimitsOfShape_of_isInitial (hj.isInitialObj e.functor) _
    exact RegMonoWide.Internal.preservesRightKan_of_preservesLimit_single _ dd

/-- **Example 4.20 (3)** ([forsman2026syntactic]): if `C` is monoidal closed, `U` strictly creates
filtered colimits. -/
theorem ex_4_20_3 (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (I : Cat.{v, u}) [IsFiltered (I : Type u)]
    (d : I ⟶ HopfModel.thyCat C) :
    StrictlyCreatesLeftKan (toOne I) d (HopfModel.forget C) := by
  have : IsSifted (I : Type u) := IsFiltered.isSifted
  exact thy_strictlyCreates_colimits (HopfModel.hopfModel C) HopfEx.oneSig HopfEx.theory I
    (HopfModel.Internal.colimitsComponentwise _ (fun _ => inferInstance)) d

universe w

/-- **Example 4.20 (3), small shapes** ([forsman2026syntactic]): if `C` is monoidal closed, `U`
creates the colimits of any filtered shape that is small with respect to `C`. -/
theorem ex_4_20_3_small (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (J : Type w) [Category.{w} J] [Small.{u} J]
    [LocallySmall.{v} J] [IsFiltered J] :
    Nonempty (CreatesColimitsOfShape J (HopfModel.forget C).toFunctor) :=
  nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan _ J fun J' _ e _ d =>
    have : IsFiltered (Cat.of J' : Type u) := IsFiltered.of_equivalence e
    ex_4_20_3 C (Cat.of J') d

end UlmerBialgebras.Paper
