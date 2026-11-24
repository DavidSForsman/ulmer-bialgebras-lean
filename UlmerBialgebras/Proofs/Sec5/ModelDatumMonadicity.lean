module

public import UlmerBialgebras.Models.DeduplicateTheory
public import UlmerBialgebras.Proofs.Sec5.ColimitsOfAlgebras
public import UlmerBialgebras.Proofs.Sec5.KanPiAdj
public import UlmerBialgebras.Proofs.Sec2.Sec2
public import UlmerBialgebras.Proofs.Sec3.Sec3
public import UlmerBialgebras.Monadicity.KappaShapes
public import Foundations.CategoryTheory.Limits.SiftedShapes

/-!
# Corollary 5.8

Theorem 5.7 applied to the bialgebraic datum `B_{M,T}` (`modelDatum`). For an algebraic theory
the coarity 1-cells are products of projections, which have left adjoints built from the
coproducts of size at most `λ` (`isRightAdjoint_codCell`); composing gives the relative left
adjoints. The functor symbols preserve `κ`-chain colimits componentwise, hence so do the term
supports. The colimit clause, for shapes of size at most `max λ κ`, comes from the Kan clause
along `J ⥤ 1`, and the Kan clause of the corollary from that of Theorem 5.7 through
`hasLeftKanExtension_pi` and `hasLeftKanExtension_comp_leftAdjoint`.

## Main results

* `UlmerBialgebras.Paper.ModelDatumMonadicity.hasLeftKanExtension_of_thyForget`: Corollary 5.8, for
  an algebraic theory `T` the forgetful functor of `M^T` is monadic, `M^T` has colimits of size at
  most `max λ κ`, and a diagram `d` in `M^T` has a left Kan extension along `k` under the Kan
  hypotheses of the corollary.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 5.8 (from Theorem 5.7 and Corollary 4.17)
-/

@[expose] public section

universe v u u₁ v₁ u₂ v₂ t₁ t₂ t₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper.ModelDatumMonadicity

open CategoryTheory Limits Functor

/-- Colimits of size at most `κ` (`HasColimitsOfSizeLE`) give `HasKappaColimits κ`, the same
condition stated for small categories. -/
theorem hasKappaColimits_of_sizeLE {κ : Cardinal.{v}} {C : Type u} [Category.{v} C]
    (h : HasColimitsOfSizeLE κ C) : HasKappaColimits κ C :=
  fun J _ hJ => h J hJ

/-- A functor preserving colimits of shape `J` preserves the joint epicness of colimiting cocones of
shape `J`. -/
theorem jointEpi_of_preserves {J : Type*} [Category J] {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [PreservesColimitsOfShape J F] : PreservesJointEpiOfShape J F :=
  fun _ _ hc _ _ _ h => (isColimitOfPreserves F hc).hom_ext h

/-- The tuple of the left-hand sides of the equations preserves the colimits of a sifted shape
`J` that the function symbols preserve componentwise. -/
theorem preservesColimitsOfShape_lift_tm_dom {Sg : TwoSig.{t₁, t₂, t₃}}
    (sg : OneSig.{t₁, t₂, t₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (T : Theory.{t₁, t₂, t₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, u}]
    (M : Model Sg Cat.{v, u}) (J : Type*) [Category J] [IsSifted J]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M J B) :
    PreservesColimitsOfShape J ((M.Peq sg T).lift fun r => M.tm sg (T.dom r)).toFunctor := by
  constructor
  intro K
  have : ∀ r : T.Eqn, PreservesColimit K (M.tm sg (T.dom r)).toFunctor :=
    fun r => (preservesColimitsOfShape_tm M sg J hB (T.dom r)).preservesColimit
  exact Product.lift_preservesColimit _ _ K

/-- A diagram `X` in `P₀` whose images under the arities of the function symbols have left Kan
extensions along `k` has one after the domain cell and the left adjoint of the codomain cell. -/
theorem hasLeftKanExtension_domCell_leftAdjoint {Sg : TwoSig.{t₁, t₂, t₃}}
    (sg : OneSig.{t₁, t₂, t₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (M : Model Sg Cat.{v, u}) [(M.codCell sg).toFunctor.IsRightAdjoint]
    {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
    (X : I ⥤ ((M.P0 sg).pt : Type u)) (k : I ⥤ Kc)
    (h2 : ∀ f : sg.Fn, k.HasLeftKanExtension (X ⋙ (M.funArity sg f).toFunctor)) :
    k.HasLeftKanExtension
      ((X ⋙ (M.domCell sg).toFunctor) ⋙ (M.codCell sg).toFunctor.leftAdjoint) := by
  let adj₁ := Adjunction.ofIsRightAdjoint (M.codCell sg).toFunctor
  let Y := X ⋙ (M.domCell sg).toFunctor
  let e := (Product.toPi (M.Pfn sg)).asEquivalence
  have : ∀ f : sg.Fn, k.HasLeftKanExtension
      ((Y ⋙ Product.toPi (M.Pfn sg)) ⋙
        Pi.eval (fun f : sg.Fn => (M.obj (sg.fnty f) : Type u)) f) := fun f =>
    (Functor.hasLeftExtension_iff_of_iso₂ k (eqToIso (by
      change X ⋙ ((M.domCell sg) ≫ (M.Pfn sg).π f).toFunctor = _
      rw [Model.domCell, (M.Pfn sg).lift_π]
      rfl))).2 (h2 f)
  have hX := hasLeftKanExtension_pi k (Y ⋙ Product.toPi (M.Pfn sg))
  have hL := @hasLeftKanExtension_comp_leftAdjoint _ _ _ _ _ _ _ _ _ k
    (Y ⋙ Product.toPi (M.Pfn sg)) _ (e.symm.toAdjunction.comp adj₁) hX
  refine (Functor.hasLeftExtension_iff_of_iso₂ k ?_).1 hL
  exact Functor.isoWhiskerLeft Y
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm _ ≪≫ Functor.leftUnitor _)

/-- If `U : C ⥤ P₀` has the left Kan extensions of the Kan extension clause of Corollary 5.8 along
the shapes `J → 1`, then `C` has the colimits of size at most `lam` that `P₀` has. -/
theorem hasColimitsOfSizeLE_of_leftKan {Sg : TwoSig.{t₁, t₂, t₃}}
    (sg : OneSig.{t₁, t₂, t₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (M : Model Sg Cat.{v, u}) [(M.codCell sg).toFunctor.IsRightAdjoint]
    {C : Type u} [Category.{v} C] (U : C ⥤ ((M.P0 sg).pt : Type u)) (lam : Cardinal.{v})
    (hP0 : HasKappaColimits lam ((M.P0 sg).pt : Type u))
    (hkan : ∀ {I : Type v} {Kc : Type v} [Category.{v} I] [Category.{v} Kc] (d : I ⥤ C)
      (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ U) →
        k.HasLeftKanExtension (((d ⋙ U) ⋙ (M.domCell sg).toFunctor) ⋙
          (M.codCell sg).toFunctor.leftAdjoint) → k.HasLeftKanExtension d) :
    HasColimitsOfSizeLE lam C := by
  intro J _ hJ
  refine ⟨fun d => ?_⟩
  have : HasColimitsOfShape J ((M.P0 sg).pt : Type u) := hP0 J hJ
  have h1 := hasLeftKanExtension_star_of_hasColimit.{v} (d ⋙ U)
  have h2 := hasLeftKanExtension_star_of_hasColimit.{v}
    (((d ⋙ U) ⋙ (M.domCell sg).toFunctor) ⋙ (M.codCell sg).toFunctor.leftAdjoint)
  have : (Functor.star.{v} J).HasLeftKanExtension d := hkan d (Functor.star.{v} J) h1 h2
  exact hasColimit_of_hasLeftKanExtension_star.{v} d

/-- **Corollary 5.8** ([forsman2026syntactic]), for an equifier of the equations of `T`, with
bounds on the function symbols and on the equations. -/
theorem hasLeftKanExtension_of_equifier (κ lam : Cardinal.{v}) (hκ : Cardinal.aleph0 ≤ κ)
    {Sg : TwoSig.{t₁, t₂, t₃}} (sg : OneSig.{t₁, t₂, t₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (T : Theory.{t₁, t₂, t₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, u}]
    (M : Model Sg Cat.{v, u}) [HasChosenInserters Cat.{v, u}]
    (Q : Equifier (M.lhsCell sg T) (M.rhsCell sg T))
    (hfn : Cardinal.lift.{v} (Cardinal.mk sg.Fn) ≤ Cardinal.lift.{s₂} lam)
    (heqn : Cardinal.lift.{v} (Cardinal.mk T.Eqn) ≤ Cardinal.lift.{s₃} lam) (halg : T.IsAlgebraic)
    (hcol : ∀ c : Sg.Cat, HasColimitsOfSizeLE (max lam κ) (M.obj c : Type u))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M κ.ord.ToType B) :
    Nonempty (MonadicRightAdjoint (Q.e ≫ M.u sg).toFunctor) ∧
      HasColimitsOfSizeLE (max lam κ) (Q.pt : Type u) ∧
      ∀ {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
        (d : I ⥤ (Q.pt : Type u))
        (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ (Q.e ≫ M.u sg).toFunctor) →
          (∀ f : sg.Fn, k.HasLeftKanExtension
            ((d ⋙ (Q.e ≫ M.u sg).toFunctor) ⋙ (M.funArity sg f).toFunctor)) →
            k.HasLeftKanExtension d := by
  have hK' : Cardinal.aleph0 ≤ max lam κ := le_trans hκ (le_max_right _ _)
  have hcolK : ∀ c, HasKappaColimits (max lam κ) (M.obj c : Type u) :=
    fun c => hasKappaColimits_of_sizeLE (hcol c)
  have hP0 : HasKappaColimits (max lam κ) ((M.P0 sg).pt : Type u) :=
    fun J _ hJ => hasColimitsOfShape_P0 M sg J (fun c => hcolK c J hJ)
  have : ∀ s : sg.Srt, HasInitial (M.obj (sg.sty s) : Type u) :=
    fun s => (hcolK (sg.sty s)).hasInitial hK'
  have : HasCoproductsOfShape sg.Fn ((M.P0 sg).pt : Type u) :=
    hP0.hasCoproductsOfShape' (hfn.trans (Cardinal.lift_le.2 (le_max_left _ _)))
  have : HasCoproductsOfShape T.Eqn ((M.P0 sg).pt : Type u) :=
    hP0.hasCoproductsOfShape' (heqn.trans (Cardinal.lift_le.2 (le_max_left _ _)))
  have := isRightAdjoint_codCell M sg halg.1
  have : ∀ r : T.Eqn, (M.tm sg (T.cod r)).toFunctor.IsRightAdjoint :=
    fun r => isRightAdjoint_tm_of_isVar M sg _ (halg.2 r)
  have : ((M.Peq sg T).lift fun r => M.tm sg (T.cod r)).toFunctor.IsRightAdjoint :=
    Product.lift_isRightAdjoint _ _
  let E := Paper.Equifier.conj Q (M.sigCell_eq sg T T.dom) (M.sigCell_eq sg T T.cod).symm
  let adj₁ := Adjunction.ofIsRightAdjoint (M.codCell sg).toFunctor
  let r₁ := RelLeftAdjoint.ofAdjunction adj₁ (M.domCell sg).toFunctor
  let r₂ := RelLeftAdjoint.ofAdjunction (Adjunction.ofIsRightAdjoint
      ((M.Peq sg T).lift fun r => M.tm sg (T.cod r)).toFunctor)
    ((M.Peq sg T).lift fun r => M.tm sg (T.dom r)).toFunctor
  have hC : HasColimitsOfSizeLE κ ((M.P0 sg).pt : Type u) :=
    fun J _ hJ => hP0 J (hJ.trans (le_max_right _ _))
  let _ := Kappa.orderBotOfPos hκ
  have : IsFiltered κ.ord.ToType := (inferInstance : IsFiltered (Kappa.shape κ))
  have : IsSifted (κ.ord.ToType) := IsFiltered.isSifted
  have hF : PreservesColimitsOfShape κ.ord.ToType (M.domCell sg).toFunctor :=
    preservesColimitsOfShape_domCell M sg κ.ord.ToType hB
  have := preservesColimitsOfShape_lift_tm_dom sg T M κ.ord.ToType hB
  have hF' := jointEpi_of_preserves (J := κ.ord.ToType)
    ((M.Peq sg T).lift fun r => M.tm sg (T.dom r)).toFunctor
  obtain ⟨hmon, -, hkan⟩ :=
    ColimitsOfAlgebras.hasColimitsOfSizeLE_and_leftKan_of_relLeftAdjoint.{v, u, u₁, v₁, u₂, v₂} κ hκ
      (modelDatum M sg T) E _ _ r₁ r₂ hC hF hF'
  -- the same Kan extension clause, for the shapes `J → 1` of the colimits of size at most `κ`
  obtain ⟨-, -, hkanStar⟩ :=
    ColimitsOfAlgebras.hasColimitsOfSizeLE_and_leftKan_of_relLeftAdjoint.{v, u, v, v, v, v} κ hκ
      (modelDatum M sg T) E _ _ r₁ r₂ hC hF hF'
  refine ⟨hmon, ?_, ?_⟩
  · exact hasColimitsOfSizeLE_of_leftKan sg M _ _ hP0 hkanStar
  · intro I Kc _ _ d k h1 h2
    exact hkan d k h1 (hasLeftKanExtension_domCell_leftAdjoint sg M _ k h2)

/-- Corollary 5.8 without a bound on the possibly repeated equation indices. -/
theorem hasLeftKanExtension_of_thyForget (κ lam : Cardinal.{v}) (hκ : Cardinal.aleph0 ≤ κ)
    (hlam : Cardinal.aleph0 ≤ lam)
    {Sg : TwoSig.{t₁, t₂, t₃}} (sg : OneSig.{t₁, t₂, t₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (T : Theory.{t₁, t₂, t₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, u}]
    (M : Model Sg Cat.{v, u}) [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    (hsize : Cardinal.lift.{v} (Cardinal.mk Sg.Cat) ≤ Cardinal.lift.{t₁} lam ∧
      Cardinal.lift.{v} (Cardinal.mk Sg.Fun) ≤ Cardinal.lift.{t₂} lam ∧
      Cardinal.lift.{v} (Cardinal.mk Sg.Tr) ≤ Cardinal.lift.{t₃} lam ∧
      Cardinal.lift.{v} (Cardinal.mk sg.Srt) ≤ Cardinal.lift.{s₁} lam ∧
      Cardinal.lift.{v} (Cardinal.mk sg.Fn) ≤ Cardinal.lift.{s₂} lam)
    (halg : T.IsAlgebraic)
    (hcol : ∀ c : Sg.Cat, HasColimitsOfSizeLE (max lam κ) (M.obj c : Type u))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M κ.ord.ToType B) :
    Nonempty (MonadicRightAdjoint
        (M.thyForget sg T).toFunctor) ∧
      HasColimitsOfSizeLE (max lam κ) (M.thyObj sg T : Type u) ∧
      ∀ {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
        (d : I ⥤ (M.thyObj sg T : Type u))
        (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ (M.thyForget sg T).toFunctor) →
          (∀ f : sg.Fn, k.HasLeftKanExtension
            ((d ⋙ (M.thyForget sg T).toFunctor) ⋙
              (M.funArity sg f).toFunctor)) →
            k.HasLeftKanExtension d := by
  obtain ⟨hCat, hFun, hTr, hSrt, hFn⟩ := hsize
  have hFun' := Cardinal.lift_le.{max t₁ t₂ t₃ s₁ s₂ s₃}.2 hFun
  have hTr' := Cardinal.lift_le.{max t₁ t₂ t₃ s₁ s₂ s₃}.2 hTr
  have hSrt' := Cardinal.lift_le.{max t₁ t₂ t₃ s₁ s₂ s₃}.2 hSrt
  have hFn' := Cardinal.lift_le.{max t₁ t₂ t₃ s₁ s₂ s₃}.2 hFn
  rw [Cardinal.lift_lift, Cardinal.lift_lift] at hFun' hTr' hSrt' hFn'
  have hd := T.cardinalMk_deduplicate_le_of_bounds.{t₁, t₂, t₃, s₁, s₂, s₃, v}
    (Cardinal.lift.{max t₁ t₂ t₃ s₁ s₂ s₃} lam) (Cardinal.aleph0_le_lift.2 hlam)
    hFn' hTr' hFun' hSrt'
  have heqn : Cardinal.lift.{v} (Cardinal.mk T.deduplicate.Eqn) ≤ Cardinal.lift.{s₃} lam := by
    refine Cardinal.lift_le.{max t₁ t₂ t₃ s₁ s₂ s₃}.1 ?_
    rw [Cardinal.lift_lift, Cardinal.lift_lift]
    exact hd
  exact hasLeftKanExtension_of_equifier κ lam hκ sg T.deduplicate M
    (M.deduplicateEquifier sg T) hFn heqn (T.deduplicate_isAlgebraic_iff.mpr halg) hcol hB

end UlmerBialgebras.Paper.ModelDatumMonadicity
