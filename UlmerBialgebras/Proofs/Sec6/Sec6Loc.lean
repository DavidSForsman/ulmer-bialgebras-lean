module

public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc
public import UlmerBialgebras.Proofs.Sec6.LocModel
public import UlmerBialgebras.Proofs.Sec6.Support.LocTransport
public import UlmerBialgebras.Proofs.Sec5.Sec5_7
public import UlmerBialgebras.Proofs.Sec6.KernelPairs
public import Foundations.RingTheory.VonNeumannRegularFlat
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Solution: Lemma 6.10 (localizations)

`R` is a commutative ring in `Type u`. The statement is about `Mod_R = Loc.modCatModel R`, that is
`ModuleCat.{u} R` in `Cat.{u, u + 1}` (see `UlmerBialgebras/Paper/Sec3DefsLoc.lean`). `T` is any
theory over a
1-signature `sg` relative to `Σ_SMon`; its sorts are `sg.Srt`.

The proof below is for `Loc.modModel R`, `Mod_R` with hom-sets lifted to `Type (u + 1)`, in
`Cat.{u + 1, u + 1}` (`modModel_localizations`). That model is the change of universe of
`modCatModel R` (`Loc.modModel_eq`), and the statement transports along the change of universe
(`Loc.stmt610_modModel_iff`, built on `UlmerBialgebras/Models/UniverseChange.lean`).

The proof follows the paper. Each localization `L_p` is a braided monoidal functor, hence a
strong morphism of `Σ_SMon`-models (`Loc.smonLaxMor`), and induces `L_p^T` over `L_p^S`
(`LaxMor.exists_unique_thyMor_of_strong`). The `L_p` are jointly conservative, and so are the
`L_p^T`, since `U : Mod_R^T → ∏_S Mod_R` reflects isomorphisms. The tensor product of modules
preserves colimits in each variable, so `U` strictly creates sifted colimits (Corollary 4.17)
and `L_p^T` preserves them. Over a von Neumann regular ring every module is flat, so the tensor
product preserves finite limits in each variable, `U` strictly creates finite cosifted limits,
and `L_p^T` preserves them since `L_p` is exact.

## Main results

* `UlmerBialgebras.Paper.modModel_localizations`: Lemma 6.10 for `Loc.modModel R`.
* `UlmerBialgebras.Paper.lem_6_10`: Lemma 6.10: for the maximal ideals `p` of `R`, there are 1-cells
  `L_p^T : Mod_R^T → Mod_{R_p}^T` over the componentwise localizations; every such family is
  jointly conservative and each member preserves small sifted colimits; if `R` is von Neumann
  regular, each member also preserves finite cosifted limits and each `R_p` is a field.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27; Chapter 3, Exercise 10
-/

@[expose] public section

universe u

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Loc

section Shapes

/-! ## Shapes in `Type u`, viewed in `Cat.{u + 1, u + 1}` through `AsSmall` -/

variable {J : Type u} [SmallCategory J]

/-- `F` preserves the colimit of `K : J ⥤ X` (`J : Type u`, `X : Type (u + 1)`) if it preserves
    that of `AsSmall.down ⋙ K`. -/
theorem preservesColimit_of_asSmall' {X Y : Type (u + 1)} [Category.{u + 1} X]
    [Category.{u + 1} Y] (K : J ⥤ X) (F : X ⥤ Y)
    [PreservesColimit ((AsSmall.down : AsSmall.{u + 1} J ⥤ J) ⋙ K) F] : PreservesColimit K F := by
  constructor
  intro c hc
  have h1 : IsColimit (c.whisker (AsSmall.down : AsSmall.{u + 1} J ⥤ J)) :=
    hc.whiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm
  have h2 := isColimitOfPreserves F h1
  have h3 : IsColimit ((F.mapCocone c).whisker (AsSmall.down : AsSmall.{u + 1} J ⥤ J)) :=
    h2.ofIsoColimit (Functor.mapCoconeWhisker F)
  exact ⟨IsColimit.ofWhiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm h3⟩

variable {A D Cc : Cat.{u + 1, u + 1}}

/-- If `U` strictly creates left Kan extensions of `AsSmall.down ⋙ K ⋙ Fb` along `J ⟶ 1` and
    `Fb ⋙ U` preserves the colimit of `K`, then `Fb` preserves the colimit of `K`. -/
theorem preservesColimit_of_reflect' (K : J ⥤ (A : Type (u + 1))) (Fb : A ⟶ D) (U : D ⟶ Cc)
    (hcr : StrictlyCreatesLeftKan (toOne (Cat.of (AsSmall.{u + 1} J)))
      ((AsSmall.down ⋙ K ⋙ (Fb).toFunctor :
        AsSmall.{u + 1} J ⥤ (D : Type (u + 1)))).toCatHom U)
    [PreservesColimit K ((Fb).toFunctor ⋙
      (U).toFunctor)] :
    PreservesColimit K (Fb).toFunctor := by
  constructor
  intro c hc
  have h1 : IsColimit ((U).toFunctor.mapCocone
      ((Fb).toFunctor.mapCocone c)) :=
    isColimitOfPreserves ((Fb).toFunctor ⋙
      (U).toFunctor) hc
  have h2 := (h1.whiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm).ofIsoColimit
    (Functor.mapCoconeWhisker (U).toFunctor).symm
  obtain ⟨h3⟩ := isColimit_of_strictlyCreatesLeftKan _ U hcr _ h2
  exact ⟨IsColimit.ofWhiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm h3⟩

end Shapes

section ShapesFin

variable {J : Type} [SmallCategory J]

/-- `F` preserves the limit of `K : J ⥤ X` if it preserves that of `AsSmall.down ⋙ K`. -/
theorem preservesLimit_of_asSmall' {X Y : Type (u + 1)} [Category.{u + 1} X]
    [Category.{u + 1} Y] (K : J ⥤ X) (F : X ⥤ Y)
    [PreservesLimit ((AsSmall.down : AsSmall.{u + 1} J ⥤ J) ⋙ K) F] : PreservesLimit K F := by
  constructor
  intro c hc
  have h1 : IsLimit (c.whisker (AsSmall.down : AsSmall.{u + 1} J ⥤ J)) :=
    hc.whiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm
  have h2 := isLimitOfPreserves F h1
  have h3 : IsLimit ((F.mapCone c).whisker (AsSmall.down : AsSmall.{u + 1} J ⥤ J)) :=
    h2.ofIsoLimit (Functor.mapConeWhisker F)
  exact ⟨IsLimit.ofWhiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm h3⟩

variable {A D Cc : Cat.{u + 1, u + 1}}

/-- If `U` strictly creates right Kan extensions of `AsSmall.down ⋙ K ⋙ Fb` along `J ⟶ 1` and
    `Fb ⋙ U` preserves the limit of `K`, then `Fb` preserves the limit of `K`. -/
theorem preservesLimit_of_reflect' (K : J ⥤ (A : Type (u + 1))) (Fb : A ⟶ D) (U : D ⟶ Cc)
    (hcr : StrictlyCreatesRightKan (toOne (Cat.of (AsSmall.{u + 1} J)))
      ((AsSmall.down ⋙ K ⋙ (Fb).toFunctor :
        AsSmall.{u + 1} J ⥤ (D : Type (u + 1)))).toCatHom U)
    [PreservesLimit K ((Fb).toFunctor ⋙
      (U).toFunctor)] :
    PreservesLimit K (Fb).toFunctor := by
  constructor
  intro c hc
  have h1 : IsLimit ((U).toFunctor.mapCone
      ((Fb).toFunctor.mapCone c)) :=
    isLimitOfPreserves ((Fb).toFunctor ⋙
      (U).toFunctor) hc
  have h2 := (h1.whiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm).ofIsoLimit
    (Functor.mapConeWhisker (U).toFunctor).symm
  obtain ⟨h3⟩ := isLimit_of_strictlyCreatesRightKan _ U hcr _ h2
  exact ⟨IsLimit.ofWhiskerEquivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm h3⟩

end ShapesFin

section Aux

variable (R : Type u) [CommRing R] (sg : OneSig SigEx.smonSig) (T : Theory sg)

/-- The strong morphism of models given by the localization at `p`. -/
noncomputable abbrev locMor (p : Ideal R) [p.IsPrime] :
    LaxMor (modModel R) (modModel (Localization.AtPrime p)) :=
  smonLaxMor (locFunctor R p)

/-- The induced functor `L_p^T : Mod_R^T → Mod_{R_p}^T`. -/
noncomputable def locThy (p : Ideal R) [p.IsPrime] :
    (modModel R).thyObj sg T ⟶ (modModel (Localization.AtPrime p)).thyObj sg T :=
  ((locMor R p).exists_unique_thyMor_of_strong sg T (smonLaxMor_strong _)).exists.choose

/-- `L_p^T` lies over `L_p^S`: `U ∘ L_p^T = L_p^S ∘ U` for the forgetful functors
    `U : Mod_R^T → ∏_S Mod_R` and `U : Mod_{R_p}^T → ∏_S Mod_{R_p}`. -/
theorem locThy_forget (p : Ideal R) [p.IsPrime] :
    locThy R sg T p ≫ (modModel (Localization.AtPrime p)).thyForget sg T =
      (modModel R).thyForget sg T ≫ locSig R sg p := by
  have h := ((locMor R p).exists_unique_thyMor_of_strong sg T
    (smonLaxMor_strong _)).exists.choose_spec
  change locThy R sg T p ≫ ((modModel _).e sg T ≫ (modModel _).u sg) =
    ((modModel R).e sg T ≫ (modModel R).u sg) ≫ (locMor R p).prod0 sg
  rw [← Category.assoc, show locThy R sg T p ≫ (modModel _).e sg T = _ from h, Category.assoc]
  rw [LaxMor.sigMor_u]
  rw [← Category.assoc]

/-- The forgetful functor `U : Mod_S^T ⥤ ∏_{s ∈ S} Mod_S` reflects isomorphisms. -/
instance thyForget_reflectsIsomorphisms (S : Type u) [CommRing S] :
    ((modModel S).thyForget sg T).toFunctor.ReflectsIsomorphisms :=
  uB_reflectsIsomorphisms.{u + 1, u + 1} (modelDatum (modModel S) sg T)
    (Equifier.conj ((modModel S).thyEquif sg T) ((modModel S).sigCell_eq sg T T.dom)
      ((modModel S).sigCell_eq sg T T.cod).symm)

/-- Any family of lifts `L_p` of the localizations `L_p^S` over the forgetful functors is jointly
conservative. -/
theorem lift_jointlyConservative
    (L : ∀ (p : Ideal R) [p.IsMaximal],
      (modModel R).thyObj sg T ⟶ (modModel (Localization.AtPrime p)).thyObj sg T)
    (hL : ∀ (p : Ideal R) [p.IsMaximal],
      L p ≫ (modModel (Localization.AtPrime p)).thyForget sg T =
        (modModel R).thyForget sg T ≫ locSig R sg p)
    {X Y : ((modModel R).thyObj sg T : Type (u + 1))} (f : X ⟶ Y)
    (h : ∀ (p : Ideal R) [p.IsMaximal],
      IsIso ((L p).toFunctor.map f)) :
    IsIso f := by
  let U : ((modModel R).thyObj sg T : Type (u + 1)) ⥤ (((modModel R).P0 sg).pt : Type (u + 1)) :=
    ((modModel R).thyForget sg T).toFunctor
  suffices IsIso (U.map f) from isIso_of_reflects_iso f U
  refine (isIso_pi_iff (U.map f)).mpr fun s => ?_
  refine locFunctor_jointlyConservative R _ (fun P _ => ?_)
  have h1 : IsIso ((L P ≫ (modModel (Localization.AtPrime P)).thyForget sg T).toFunctor.map f)
      := by
    have := h P
    exact (inferInstance : IsIso (((modModel (Localization.AtPrime P)).thyForget sg T).toFunctor.map
        ((L P).toFunctor.map f)))
  rw [hL P] at h1
  exact (isIso_pi_iff _).mp h1 s

/-- `ModU S` has colimits of every small shape `J : Type u` (via `ModuleCat S ≌ ModU S`). -/
instance modU_hasColimitsOfShape (S : Type u) [CommRing S] (J : Type u) [SmallCategory J] :
    HasColimitsOfShape J (ModU S) :=
  Adjunction.hasColimitsOfShape_of_equivalence (modEquiv S).inverse

/-- `ModU S` has colimits of shape `AsSmall J` for every small `J : Type u`. -/
instance modU_hasColimitsOfShape_asSmall (S : Type u) [CommRing S] (J : Type u) [SmallCategory J] :
    HasColimitsOfShape (AsSmall.{u + 1} J) (ModU S) :=
  hasColimitsOfShape_of_equivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J)

/-- Any lift `L` of the localization `L_p^S` over the forgetful functors preserves small sifted
colimits. -/
theorem lift_preservesSifted (p : Ideal R) [p.IsPrime]
    (L : (modModel R).thyObj sg T ⟶ (modModel (Localization.AtPrime p)).thyObj sg T)
    (hL : L ≫ (modModel (Localization.AtPrime p)).thyForget sg T =
      (modModel R).thyForget sg T ≫ locSig R sg p)
    (J : Type u) [SmallCategory J] [IsSifted J] :
    PreservesColimitsOfShape J (L).toFunctor := by
  -- The forgetful functor of the localized models creates sifted colimits, so it suffices that
  -- `L ⋙ forget = forget ⋙ locSig` preserves them: `forget` does (it creates them) and the
  -- localization `locSig` does sortwise.
  classical
  have : IsSifted (AsSmall.{u + 1} J) :=
    IsSifted.isSifted_of_equiv (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm
  have : IsSifted ((Cat.of (AsSmall.{u + 1} J) : Cat.{u + 1, u + 1}) : Type (u + 1)) :=
    inferInstanceAs (IsSifted (AsSmall.{u + 1} J))
  have hB : ∀ (S : Type u) [CommRing S],
      ∀ B, PreservesColimitsComponentwise (modModel S) (Cat.of (AsSmall.{u + 1} J)) B :=
    fun S _ => smon_colimitsComponentwise _ (fun X => inferInstance)
  let UM : ((modModel R).thyObj sg T : Type (u + 1)) ⥤ (((modModel R).P0 sg).pt : Type (u + 1)) :=
    ((modModel R).thyForget sg T).toFunctor
  -- the localization preserves the colimits sortwise
  have : PreservesColimitsOfShape J
      (locSig R sg p).toFunctor := by
    have : ∀ s : sg.Srt, PreservesColimitsOfShape J
        (Pi.eval (fun _ : sg.Srt => ModU R) s ⋙ locFunctor R p) := fun s => by
      have := piEvalPreservesColimitsOfShape (C := fun _ : sg.Srt => ModU R) (J := J) s
      exact comp_preservesColimitsOfShape _ _
    exact pi'PreservesColimitsOfShape (C := fun _ : sg.Srt => ModU (Localization.AtPrime p))
      (fun s => Pi.eval (fun _ : sg.Srt => ModU R) s ⋙ locFunctor R p)
  -- the composite preserves the colimit of `K`, and the forgetful functor reflects it
  constructor
  intro K
  have : PreservesColimit K
      ((L).toFunctor ⋙
        ((modModel (Localization.AtPrime p)).thyForget sg T).toFunctor) := by
    rw [show ((L).toFunctor ⋙
        ((modModel (Localization.AtPrime p)).thyForget sg T).toFunctor) =
      UM ⋙ (locSig R sg p).toFunctor from
        congr(($hL).toFunctor)]
    have : HasColimitsOfShape (AsSmall.{u + 1} J) (((modModel R).P0 sg).pt : Type (u + 1)) :=
      pi_hasColimitsOfShape (C := fun _ : sg.Srt => ModU R)
    let d : Cat.of (AsSmall.{u + 1} J) ⟶ (modModel R).thyObj sg T :=
      (AsSmall.down ⋙ K : AsSmall.{u + 1} J ⥤ _).toCatHom
    have : HasColimit (d ≫ (modModel R).thyForget sg T).toFunctor :=
      (inferInstance : HasColimitsOfShape (AsSmall.{u + 1} J)
        (((modModel R).P0 sg).pt : Type (u + 1))).has_colimit _
    have : PreservesColimit (AsSmall.down ⋙ K) UM :=
      preservesColimit_of_strictlyCreatesLeftKan d ((modModel R).thyForget sg T)
        (thy_strictlyCreates_colimits.{u + 1, u + 1} (modModel R) sg T _ (hB R) d)
    have : PreservesColimit K UM := preservesColimit_of_asSmall' K UM
    infer_instance
  exact preservesColimit_of_reflect' K (L)
    ((modModel (Localization.AtPrime p)).thyForget sg T)
    (thy_strictlyCreates_colimits.{u + 1, u + 1} (modModel (Localization.AtPrime p)) sg
        T _ (hB _) _)

/-- `ModU S` has finite limits (via `ModuleCat S ≌ ModU S`). -/
instance modU_hasFiniteLimits (S : Type u) [CommRing S] : HasFiniteLimits (ModU S) :=
  ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence (modEquiv S).inverse⟩

/-- Over a von Neumann regular ring, `X ⊗ -` preserves finite limits. -/
theorem tensorLeft_preservesFiniteLimits (S : Type u) [CommRing S]
    (hS : IsVonNeumannRegularRing S) (X : ModU S) : PreservesFiniteLimits
        (MonoidalCategory.tensorLeft X) := by
  have : Module.Flat S ((modEquiv S).inverse.obj X) :=
    IsVonNeumannRegular.flat hS _
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft ((modEquiv S).inverse.obj X)) :=
    inferInstance
  have : PreservesFiniteLimits ((modEquiv S).inverse ⋙
      MonoidalCategory.tensorLeft ((modEquiv S).inverse.obj X) ⋙ (modEquiv S).functor) :=
    inferInstance
  exact preservesFiniteLimits_of_natIso (tensorLeftIso S X).symm

/-- Over a von Neumann regular ring, any lift `L` of the localization `L_p^S` over the forgetful
functors preserves finite cosifted limits. -/
theorem lift_preservesCosifted (hR : IsVonNeumannRegularRing R) (p : Ideal R) [p.IsMaximal]
    (L : (modModel R).thyObj sg T ⟶ (modModel (Localization.AtPrime p)).thyObj sg T)
    (hL : L ≫ (modModel (Localization.AtPrime p)).thyForget sg T =
      (modModel R).thyForget sg T ≫ locSig R sg p)
    (J : Type) [SmallCategory J] [FinCategory J] [IsCosifted J] :
    PreservesLimitsOfShape J (L).toFunctor := by
  -- As for sifted colimits: over a von Neumann regular ring tensoring is exact, so the forgetful
  -- functors create finite cosifted limits, and `L ⋙ forget = forget ⋙ locSig` preserves them.
  classical
  have hRp : IsVonNeumannRegularRing (Localization.AtPrime p) :=
    IsVonNeumannRegularRing.of_isField (IsVonNeumannRegular.isField_localizationAtPrime hR p)
  have : IsSifted (AsSmall.{u + 1} J)ᵒᵖ :=
    IsSifted.isSifted_of_equiv (AsSmall.equiv : J ≌ AsSmall.{u + 1} J).symm.op
  have : IsCosifted ((Cat.of (AsSmall.{u + 1} J) : Cat.{u + 1, u + 1}) : Type (u + 1)) :=
    inferInstanceAs (IsSifted (AsSmall.{u + 1} J)ᵒᵖ)
  have hB : ∀ (S : Type u) [CommRing S], IsVonNeumannRegularRing S →
      ∀ B, PreservesLimitsComponentwise (modModel S) (Cat.of (AsSmall.{u + 1} J)) B := by
    intro S _ hS
    refine smon_limitsComponentwise _ (fun X => ?_)
    have := tensorLeft_preservesFiniteLimits S hS X
    exact preservesLimitsOfShape_of_equiv (AsSmall.equiv : J ≌ AsSmall.{u + 1} J) _
  have : ∀ (S : Type u) [CommRing S], HasLimitsOfShape (AsSmall.{u + 1} J) (ModU S) :=
    fun S _ => hasLimitsOfShape_of_equivalence (AsSmall.equiv : J ≌ AsSmall.{u + 1} J)
  let UM : ((modModel R).thyObj sg T : Type (u + 1)) ⥤ (((modModel R).P0 sg).pt : Type (u + 1)) :=
    ((modModel R).thyForget sg T).toFunctor
  -- the localization preserves the limits sortwise
  have := locFunctor_preservesFiniteLimits R p
  have : PreservesLimitsOfShape J
      (locSig R sg p).toFunctor := by
    have : ∀ s : sg.Srt, PreservesLimitsOfShape J
        (Pi.eval (fun _ : sg.Srt => ModU R) s ⋙ locFunctor R p) := fun s => by
      have := piEvalPreservesLimitsOfShape (C := fun _ : sg.Srt => ModU R) (J := J) s
      exact comp_preservesLimitsOfShape _ _
    exact pi'_preservesLimitsOfShape (C := fun _ : sg.Srt => ModU (Localization.AtPrime p))
      (fun s => Pi.eval (fun _ : sg.Srt => ModU R) s ⋙ locFunctor R p)
  -- the composite preserves the limit of `K`, and the forgetful functor reflects it
  constructor
  intro K
  have : PreservesLimit K
      ((L).toFunctor ⋙
        ((modModel (Localization.AtPrime p)).thyForget sg T).toFunctor) := by
    rw [show ((L).toFunctor ⋙
        ((modModel (Localization.AtPrime p)).thyForget sg T).toFunctor) =
      UM ⋙ (locSig R sg p).toFunctor from
        congr(($hL).toFunctor)]
    have : HasLimitsOfShape (AsSmall.{u + 1} J) (((modModel R).P0 sg).pt : Type (u + 1)) :=
      pi_hasLimitsOfShape (C := fun _ : sg.Srt => ModU R)
    let d : Cat.of (AsSmall.{u + 1} J) ⟶ (modModel R).thyObj sg T :=
      (AsSmall.down ⋙ K : AsSmall.{u + 1} J ⥤ _).toCatHom
    have : HasLimit (d ≫ (modModel R).thyForget sg T).toFunctor :=
      (inferInstance : HasLimitsOfShape (AsSmall.{u + 1} J)
        (((modModel R).P0 sg).pt : Type (u + 1))).has_limit _
    have : PreservesLimit (AsSmall.down ⋙ K) UM :=
      preservesLimit_of_strictlyCreatesRightKan d ((modModel R).thyForget sg T)
        (thy_strictlyCreates_limits (modModel R) sg T _ (hB R hR) d)
    have : PreservesLimit K UM := preservesLimit_of_asSmall' K UM
    infer_instance
  exact preservesLimit_of_reflect' K (L)
    ((modModel (Localization.AtPrime p)).thyForget sg T)
    (thy_strictlyCreates_limits (modModel (Localization.AtPrime p)) sg T _ (hB _ hRp) _)

end Aux

/-- Lemma 6.10 for `Mod_R` with lifted hom-sets (`Loc.modModel R`, in `Cat.{u + 1, u + 1}`). -/
theorem modModel_localizations (R : Type u) [CommRing R] (sg : OneSig SigEx.smonSig)
    (T : Theory sg) :
    (∃ L : ∀ (p : Ideal R) [p.IsMaximal],
        (modModel R).thyObj sg T ⟶ (modModel (Localization.AtPrime p)).thyObj sg T,
      ∀ (p : Ideal R) [p.IsMaximal],
        L p ≫ (modModel (Localization.AtPrime p)).thyForget sg T =
          (modModel R).thyForget sg T ≫ locSig R sg p) ∧
    ∀ L : ∀ (p : Ideal R) [p.IsMaximal],
        (modModel R).thyObj sg T ⟶ (modModel (Localization.AtPrime p)).thyObj sg T,
      (∀ (p : Ideal R) [p.IsMaximal],
        L p ≫ (modModel (Localization.AtPrime p)).thyForget sg T =
          (modModel R).thyForget sg T ≫ locSig R sg p) →
      (∀ ⦃X Y : ((modModel R).thyObj sg T : Type (u + 1))⦄ (f : X ⟶ Y),
        (∀ (p : Ideal R) [p.IsMaximal],
          IsIso ((L p).toFunctor.map f)) → IsIso f) ∧
      (∀ (p : Ideal R) [p.IsMaximal] (J : Type u) [SmallCategory J] [IsSifted J],
        PreservesColimitsOfShape J (L p).toFunctor) ∧
      (IsVonNeumannRegularRing R → ∀ (p : Ideal R) [p.IsMaximal],
        (∀ (J : Type) [SmallCategory J] [FinCategory J] [IsCosifted J],
          PreservesLimitsOfShape J (L p).toFunctor) ∧
        IsField (Localization.AtPrime p)) := by
  refine ⟨⟨fun p _ => locThy R sg T p, fun p _ => locThy_forget R sg T p⟩, fun L hL =>
    ⟨fun X Y f h => lift_jointlyConservative R sg T L hL f h,
      fun p _ J _ _ => lift_preservesSifted R sg T p (L p) (hL p) J, fun hR p _ =>
        ⟨fun J _ _ _ => lift_preservesCosifted R sg T hR p (L p) (hL p) J,
          IsVonNeumannRegular.isField_localizationAtPrime hR p⟩⟩⟩

/-- **Lemma 6.10** ([forsman2026syntactic]): localizing at the maximal ideals `p` of `R` gives
functors `L_p^T : Mod_R^T → Mod_{R_p}^T` over the componentwise localizations
`L_p^S : ∏_S Mod_R → ∏_S Mod_{R_p}` (for instance the functors induced by the strong monoidal
localizations, Corollary 3.23 (3)). Every such family of lifts is jointly conservative, and each
member preserves small sifted colimits. If `R` is von Neumann regular, each member also preserves
finite cosifted limits, and each `R_p` is a field. -/
theorem lem_6_10 (R : Type u) [CommRing R] (sg : OneSig SigEx.smonSig) (T : Theory sg) :
    (∃ L : ∀ (p : Ideal R) [p.IsMaximal],
        (modCatModel R).thyObj sg T ⟶ (modCatModel (Localization.AtPrime p)).thyObj sg T,
      ∀ (p : Ideal R) [p.IsMaximal],
        L p ≫ (modCatModel (Localization.AtPrime p)).thyForget sg T =
          (modCatModel R).thyForget sg T ≫ locSigCat R sg p) ∧
    ∀ L : ∀ (p : Ideal R) [p.IsMaximal],
        (modCatModel R).thyObj sg T ⟶ (modCatModel (Localization.AtPrime p)).thyObj sg T,
      (∀ (p : Ideal R) [p.IsMaximal],
        L p ≫ (modCatModel (Localization.AtPrime p)).thyForget sg T =
          (modCatModel R).thyForget sg T ≫ locSigCat R sg p) →
      (∀ ⦃X Y : ((modCatModel R).thyObj sg T : Type (u + 1))⦄ (f : X ⟶ Y),
        (∀ (p : Ideal R) [p.IsMaximal],
          IsIso ((L p).toFunctor.map f)) → IsIso f) ∧
      (∀ (p : Ideal R) [p.IsMaximal] (J : Type u) [SmallCategory J] [IsSifted J],
        PreservesColimitsOfShape J (L p).toFunctor) ∧
      (IsVonNeumannRegularRing R → ∀ (p : Ideal R) [p.IsMaximal],
        (∀ (J : Type) [SmallCategory J] [FinCategory J] [IsCosifted J],
          PreservesLimitsOfShape J (L p).toFunctor) ∧
        IsField (Localization.AtPrime p)) :=
  (Loc.stmt610_modModel_iff R sg T).1 (modModel_localizations R sg T)

end UlmerBialgebras.Paper
