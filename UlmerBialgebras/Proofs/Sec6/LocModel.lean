module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.RingTheory.Smooth.Flat
public import UlmerBialgebras.Proofs.Sec6.ExtScalarsMonoidal
public import UlmerBialgebras.Proofs.Sec6.SMonLax
public import UlmerBialgebras.Kan.CosiftedModel
public import UlmerBialgebras.Kan.SiftedModel
public import Foundations.CategoryTheory.Limits.PiLimits
public import UlmerBialgebras.Examples.MonModelUpdate

/-!
# Lemma 6.10: the model `Mod_R` and its localizations

## Main results

* `UlmerBialgebras.Paper.Loc.smon_colimitsComponentwise`: if every `X ⊗ -` preserves `I`-colimits,
  the functor symbols of the `Σ_SMon`-model of `C` preserve them componentwise.
* `UlmerBialgebras.Paper.Loc.smon_limitsComponentwise`: the same for `I`-limits.
* `UlmerBialgebras.Paper.Loc.locFunctor_preservesFiniteLimits`: the localization `L_p` at a prime
  `p` preserves finite limits (Lemma 6.10).
* `UlmerBialgebras.Paper.Loc.locFunctor_jointlyConservative`: the localizations at the maximal
  ideals of `R` are jointly conservative on `ModU R` (Lemma 6.10).
* `UlmerBialgebras.Paper.Loc.smonLaxMor_strong`: for a braided functor `F`, the induced lax morphism
  of `Σ_SMon`-models is strong.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 3
-/

@[expose] public section

universe u v

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory MonoidalCategory Limits TensorProduct

/-! ## Componentwise preservation for `Σ_SMon`-models -/


section Componentwise

variable {C : Type u} [Category.{u} C] [MonoidalCategory C] [SymmetricCategory C]

/-- If `X ⊗ -` preserves `I`-colimits for every `X`, the structural functors `⊗` and `I` of the
`Σ_SMon`-model of a symmetric monoidal category `C` preserve `I`-colimits componentwise. -/
theorem smon_colimitsComponentwise (I : Cat.{u, u})
    (h : ∀ X : C, PreservesColimitsOfShape (I : Type u) (tensorLeft X)) :
    ∀ B, PreservesColimitsComponentwise (smonModel C) I B := by
  intro B
  cases B with
  | tens =>
    intro i x
    refine ⟨?_⟩
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesColimitsOfShape (I : Type u) (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have := h (x 1)
        have : PreservesColimitsOfShape (I : Type u) (tensorRight (x 1)) :=
          preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · have := h (x 0)
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact key i x
  | unit => exact fun i _ => i.elim0

/-- If `X ⊗ -` preserves `I`-limits for every `X`, the structural functors `⊗` and `I` of the
`Σ_SMon`-model of a symmetric monoidal category `C` preserve `I`-limits componentwise. -/
theorem smon_limitsComponentwise (I : Cat.{u, u})
    (h : ∀ X : C, PreservesLimitsOfShape (I : Type u) (tensorLeft X)) :
    ∀ B, PreservesLimitsComponentwise (smonModel C) I B := by
  intro B
  cases B with
  | tens =>
    intro i x
    refine ⟨?_⟩
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesLimitsOfShape (I : Type u) (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have := h (x 1)
        have : PreservesLimitsOfShape (I : Type u) (tensorRight (x 1)) :=
          preservesLimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesLimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · have := h (x 0)
        exact preservesLimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact key i x
  | unit => exact fun i _ => i.elim0

end Componentwise

/-! ## The tensor product of `ModU R` -/

section ModU

variable (R : Type u) [CommRing R]

/-- `X ⊗ -` on `ModU R` is `X ⊗ -` on `ModuleCat R`, transported. -/
def tensorLeftIso (X : ModU R) :
    tensorLeft X ≅ (modEquiv R).inverse ⋙ tensorLeft ((modEquiv R).inverse.obj X) ⋙
      (modEquiv R).functor :=
  Iso.refl _

/-- On `Mod_R`, `X ⊗ -` is a left adjoint (transported from `ModuleCat R`, which is closed). -/
instance (X : ModU R) : (tensorLeft X).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (tensorLeftIso R X).symm

end ModU

/-! ## The localization functors -/

section Loc

variable (R : Type u) [CommRing R]

/-- The localization `L_p : Mod_R → Mod_{R_p}`, `M ↦ R_p ⊗_R M`, is braided strong monoidal. -/
noncomputable instance locFunctor_braided (p : Ideal R) [p.IsPrime] : (locFunctor R p).Braided :=
  inferInstanceAs ((modEquiv R).inverse ⋙
    ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p)) ⋙
      (modEquiv (Localization.AtPrime p)).functor).Braided

/-- The localization `L_p : Mod_R → Mod_{R_p}` is a left adjoint (to restriction of scalars). -/
instance locFunctor_isLeftAdjoint (p : Ideal R) [p.IsPrime] : (locFunctor R p).IsLeftAdjoint := by
  have : (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p)) ⋙
      (modEquiv (Localization.AtPrime p)).functor).IsLeftAdjoint :=
    Functor.isLeftAdjoint_comp _ _
  exact Functor.isLeftAdjoint_comp (modEquiv R).inverse
    (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p)) ⋙
      (modEquiv (Localization.AtPrime p)).functor)

/-- The localization `L_p : Mod_R → Mod_{R_p}` preserves finite limits, since `R_p` is flat over `R`
(Lemma 6.10 of [forsman2026syntactic]). -/
theorem locFunctor_preservesFiniteLimits (p : Ideal R) [p.IsPrime] :
    PreservesFiniteLimits (locFunctor R p) := by
  have hf : (algebraMap R (Localization.AtPrime p)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact inferInstanceAs (PreservesFiniteLimits ((modEquiv R).inverse ⋙
    ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p)) ⋙
      (modEquiv (Localization.AtPrime p)).functor))

/-- Local-global principle: a linear map is bijective if its base changes to all localizations
at maximal ideals are. -/
theorem bijective_of_baseChange {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (F : M →ₗ[R] N)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      Function.Bijective (F.baseChange (Localization.AtPrime P))) :
    Function.Bijective F := by
  refine bijective_of_isLocalized_maximal (fun P _ => Localization.AtPrime P ⊗[R] M)
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) M 1)
    (fun P _ => Localization.AtPrime P ⊗[R] N)
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) N 1) F (fun P _ => ?_)
  have : IsLocalizedModule.map P.primeCompl (TensorProduct.mk R (Localization.AtPrime P) M 1)
      (TensorProduct.mk R (Localization.AtPrime P) N 1) F =
        (F.baseChange (Localization.AtPrime P)).restrictScalars R := by
    refine IsLocalizedModule.linearMap_ext P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) M 1)
      (TensorProduct.mk R (Localization.AtPrime P) N 1) ?_
    rw [IsLocalizedModule.map_comp]
    ext m
    simp
  rw [this]
  exact h P

/-- Extension of scalars to the localizations at maximal ideals is jointly conservative. -/
theorem isIso_of_extendScalars {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      IsIso ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime P))).map g)) :
    IsIso g := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine bijective_of_baseChange R g.hom (fun P _ => ?_)
  have h1 := (ConcreteCategory.isIso_iff_bijective _).mp (h P)
  let e₀ : ((ModuleCat.restrictScalars (algebraMap R (Localization.AtPrime P))).obj
      (ModuleCat.of _ (Localization.AtPrime P))) ≃ₗ[R] Localization.AtPrime P :=
    { toFun := fun s => s
      invFun := fun s => s
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => (Algebra.smul_def r (show Localization.AtPrime P from s)).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eM := TensorProduct.congr e₀ (LinearEquiv.refl R M)
  let eN := TensorProduct.congr e₀ (LinearEquiv.refl R N)
  have hsq : ⇑(g.hom.baseChange (Localization.AtPrime P)) =
      eN ∘ ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime P))).map g) ∘
        eM.symm := by
    funext x
    induction x using TensorProduct.inductionOn with
    | add a b ha hb =>
      rw [map_add, ha, hb]
      let f := ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime P))).map g).hom
      change eN (f (eM.symm a)) + eN (f (eM.symm b)) = eN (f (eM.symm (a + b)))
      rw [map_add eM.symm]
      exact ((congrArg eN (f.map_add (eM.symm a) (eM.symm b))).trans (eN.map_add _ _)).symm
    | tmul s m => rfl
  rw [hsq]
  exact eN.bijective.comp (h1.comp eM.symm.bijective)

/-- The localizations `L_p` at the maximal ideals of `R` are jointly conservative on `ModU R`. -/
theorem locFunctor_jointlyConservative {X Y : ModU R} (g : X ⟶ Y)
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsIso ((locFunctor R P).map g)) : IsIso g := by
  have : IsIso ((modEquiv R).inverse.map g) := by
    refine isIso_of_extendScalars R _ (fun P _ => ?_)
    have : IsIso ((modEquiv (Localization.AtPrime P)).functor.map
        ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime P))).map
          ((modEquiv R).inverse.map g))) := h P
    exact isIso_of_reflects_iso _ (modEquiv (Localization.AtPrime P)).functor
  exact isIso_of_reflects_iso g (modEquiv R).inverse

end Loc


/-! ## Strong morphisms and functors into products -/

/-- For a braided strong monoidal functor `F`, the lax morphism of `Σ_SMon`-models induced by `F` is
strong: its structure 2-cells (`μ` for `⊗`, `ε` for `I`) are invertible. -/
theorem smonLaxMor_strong {C D : Type u} [Category.{u} C] [MonoidalCategory C]
    [SymmetricCategory C] [Category.{u} D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] : ∀ B, IsIso ((smonLaxMor F).str B) := by
  intro B
  cases B with
  | tens =>
    have : ∀ X : Fin 2 → C, IsIso (((smonLaxMor F).str SigEx.MonFun.tens).toNatTrans.app X) :=
      fun X => (inferInstance : IsIso (Functor.LaxMonoidal.μ F (X 0) (X 1)))
    have : IsIso (((smonLaxMor F).str SigEx.MonFun.tens).toNatTrans) :=
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    exact (Cat.Hom.isoMk (asIso (((smonLaxMor F).str SigEx.MonFun.tens).toNatTrans))).isIso_hom
  | unit =>
    have : ∀ X : Fin 0 → C, IsIso (((smonLaxMor F).str SigEx.MonFun.unit).toNatTrans.app X) :=
      fun X => (inferInstance : IsIso (Functor.LaxMonoidal.ε F))
    have : IsIso (((smonLaxMor F).str SigEx.MonFun.unit).toNatTrans) :=
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
    exact (Cat.Hom.isoMk (asIso (((smonLaxMor F).str SigEx.MonFun.unit).toNatTrans))).isIso_hom

/-- A functor into a product of categories preserves the limits preserved by all of its
components. -/
theorem pi'_preservesLimitsOfShape {ι : Type*} {C : ι → Type*} [∀ i, Category (C i)]
    {J : Type*} [Category J] {A : Type*} [Category A] (f : ∀ j, A ⥤ C j)
    [∀ j, PreservesLimitsOfShape J (f j)] : PreservesLimitsOfShape J (Functor.pi' f) where
  preservesLimit := ⟨fun hc => ⟨piIsLimitOfEval _ fun j => isLimitOfPreserves (f j) hc⟩⟩

end UlmerBialgebras.Paper.Loc
