module

public import UlmerBialgebras.Paper.Sec4DefsEx420
public import UlmerBialgebras.Proofs.Sec4.Sec4Hopf
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import UlmerBialgebras.Proofs.Sec4.Ex420WidePullback

/-!
# Solution: Example 4.20, the case of `Vect_k`, and the closing remark

* `ex_4_20_2_vect` is `ex_4_20_2_pullback` for `C = Vect_k = ModuleCat k`: every vector space is
  flat, so tensoring preserves finite limits, and an injective linear map is a regular
  monomorphism (`ModuleCat k` is abelian).
* `ex_4_20_general`, items (1) and (3), are Corollary 4.17 and its dual
  (`thy_strictlyCreates_colimits`, `thy_strictlyCreates_limits`) under the componentwise
  conditions; a coreflexive pair `J ≌ WalkingCoreflexivePair` is transported along the
  equivalence.
* `ex_4_20_general_2` (item (2)) is `thy_strictlyCreates_widePushouts_of_regularEpi` and
  `thy_strictlyCreates_widePullbacks_of_regularMono`
  (`UlmerBialgebras/Proofs/Sec4/Ex420WidePushout.lean`,
  `UlmerBialgebras/Proofs/Sec4/Ex420WidePullback.lean`), by the paper's argument: a wide pushout of
  regular
  epimorphisms is the colimit of the kernel pairs of its legs, a diagram of the sifted shape
  `MultiReflexivePair`, and dually.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20
-/

@[expose] public section


universe v u w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory Limits

/-- **Example 4.20 (2)** ([forsman2026syntactic]), the case of `Vect_k`: "This explains why for a
field `k` one can compute finite intersections of Hopf subalgebras in `Hopf_k` in the underlying
category `Vect_k` of `k`-vector spaces."

For a finite family of morphisms `fⱼ : xⱼ → y` of Hopf monoids in `Vect_k` whose underlying
`k`-linear maps are injective, the forgetful functor `U : M^{T_Hopf} → Vect_k` strictly creates
their joint pullback. -/
theorem ex_4_20_2_vect (k : Type u) [Field k] (K : Type u) [Finite K] (J : Cat.{u, u + 1})
    (e : WidePullbackShape K ≌ (J : Type (u + 1)))
    (d : J ⟶ HopfModel.thyCat (ModuleCat.{u} k))
    (hd : ∀ j, Function.Injective ((hopfVectForget k).map
      (d.toFunctor.map (e.functor.map (WidePullbackShape.Hom.term j)))).hom) :
    StrictlyCreatesRightKan (toOne J) d (HopfModel.forget (ModuleCat.{u} k))  := by
  have : ∀ X : ModuleCat.{u} k, PreservesFiniteLimits (tensorLeft X) := fun X => by
    have : Module.Flat k X := Module.Flat.of_free
    infer_instance
  refine ex_4_20_2_pullback (ModuleCat.{u} k) K J e d (fun j => ?_)
  refine (RegMonoWide.Internal.isRegularMono_of_piRegMono _ (fun _ => ?_)).regularMono
  have : Mono ((hopfVectForget k).map
      (d.toFunctor.map (e.functor.map (WidePullbackShape.Hom.term j)))) :=
    (ModuleCat.mono_iff_injective _).2 (hd j)
  have : NormalMono ((hopfVectForget k).map
      (d.toFunctor.map (e.functor.map (WidePullbackShape.Hom.term j)))) := normalMonoOfMono _
  exact (inferInstance : IsRegularMono ((hopfVectForget k).map
      (d.toFunctor.map (e.functor.map (WidePullbackShape.Hom.term j)))))

/-- **Example 4.20** ([forsman2026syntactic]), the closing remark, items (1) and (3): "Of
course, there is nothing special about `Hopf`. We could have chosen any bialgebraic theory `T` and
considered `C^T`, and obtained the same results. Similarly, nothing depends on the symmetric
monoidal structure: we could have chosen any `Σ`-model `M`, where the categories `M_c` have and the
functors `M(B)` (componentwise) preserve sifted colimits and finite cosifted limits, and the
categories `M_c` have kernel pairs and cokernel pairs."

For a `Σ`-model `M` in `CAT = Cat.{v, u}` and any theory `T`, the forgetful functor
`U : M^T → M₀` strictly creates

1. reflexive coequalizers, if `M` has sifted colimits componentwise, and coreflexive equalizers,
   if `M` has finite cosifted limits componentwise;
3. filtered colimits, if `M` has sifted colimits componentwise.

Item (2) is `ex_4_20_general_2`. The statement is the conjunction, each part with only the
condition it needs (`Model.SiftedColimitsComponentwise`, `Model.FinCosiftedLimitsComponentwise`,
`UlmerBialgebras/Paper/Sec4DefsEx420.lean`). Sifted shapes are small relative to `CAT` (objects and
morphisms
in `Type v`), filtered shapes are the essentially small filtered `I : Cat.{v, u}`, finite cosifted
shapes are in `Type`, and a shape `J` of a constructed kind is any `J : Cat.{v, u}` equivalent to
the standard one. -/
theorem ex_4_20_general [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] :
    -- (1) reflexive coequalizers and coreflexive equalizers
    (M.SiftedColimitsComponentwise →
      ∀ (J : Cat.{v, u}) (_ : WalkingReflexivePair ≌ (J : Type u)) (d : J ⟶ M.thyObj sg T),
        StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg)) ∧
    (M.FinCosiftedLimitsComponentwise →
      ∀ (J : Cat.{v, u}) (_ : WalkingCoreflexivePair ≌ (J : Type u)) (d : J ⟶ M.thyObj sg T),
        StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg)) ∧
    -- (3) filtered colimits
    (M.SiftedColimitsComponentwise →
      ∀ (I : Cat.{v, u}) [IsFiltered (I : Type u)] [EssentiallySmall.{v} (I : Type u)]
        (d : I ⟶ M.thyObj sg T),
        StrictlyCreatesLeftKan (toOne I) d (M.e sg T ≫ M.u sg))  := by
  refine ⟨fun h J e d => ?_, fun h J e d => ?_, fun h I _ _ d => ?_⟩
  · have : IsSifted (J : Type u) := IsSifted.isSifted_of_equiv e.symm
    exact thy_strictlyCreates_colimits M sg T J (preservesColimitsComponentwise_of_sifted M h _
      (e.symm.trans (ULiftHomULiftCategory.equiv.{v, v} WalkingReflexivePair))) d
  · have : IsCosifted (J : Type u) :=
      IsSifted.isSifted_of_equiv (C := WalkingCoreflexivePairᵒᵖ) e.op.symm
    refine thy_strictlyCreates_limits M sg T J (fun B i x => ?_) d
    obtain ⟨hp⟩ := (h WalkingCoreflexivePair).2 B i x
    exact ⟨preservesLimitsOfShape_of_equiv e _⟩
  · have : IsSifted (I : Type u) := IsFiltered.isSifted
    exact thy_strictlyCreates_colimits M sg T I
      (preservesColimitsComponentwise_of_sifted M h _ (equivSmallModel.{v} (I : Type u))) d

/-- **Example 4.20** ([forsman2026syntactic]), the closing remark, item (2) (see
`ex_4_20_general` for the quoted remark). For a `Σ`-model `M` in `CAT = Cat.{v, u}` and any theory
`T`, the forgetful functor `U : M^T → M₀` strictly creates joint pullbacks of finite families of
morphisms that `U` sends to regular monomorphisms, if `M` has finite cosifted limits componentwise
and its categories have cokernel pairs, and wide pushouts of families of morphisms that `U` sends
to regular epimorphisms, if `M` has sifted colimits componentwise and its categories have kernel
pairs. -/
theorem ex_4_20_general_2 [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] :
    (M.FinCosiftedLimitsComponentwise → M.HasCokernelPairs →
      ∀ (K : Type v) [Finite K] (J : Cat.{v, u}) (e : WidePullbackShape K ≌ (J : Type u))
        (d : J ⟶ M.thyObj sg T),
        (∀ j, Nonempty (RegularMono ((d ≫ M.e sg T ≫ M.u sg).toFunctor.map
          (e.functor.map (WidePullbackShape.Hom.term j))))) →
        StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg)) ∧
    (M.SiftedColimitsComponentwise → M.HasKernelPairs →
      ∀ (K : Type v) (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u))
        (d : J ⟶ M.thyObj sg T),
        (∀ j, Nonempty (RegularEpi ((d ≫ M.e sg T ≫ M.u sg).toFunctor.map
          (e.functor.map (WidePushoutShape.Hom.init j))))) →
        StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg)) := by
  exact ⟨fun h hc K _ J e d hd =>
      thy_strictlyCreates_widePullbacks_of_regularMono M sg T h hc K J e d hd,
    fun h hk K J e d hd => thy_strictlyCreates_widePushouts_of_regularEpi M sg T h hk K J e d hd⟩

end UlmerBialgebras.Paper
