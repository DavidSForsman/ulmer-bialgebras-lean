module

public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushoutPi
public import UlmerBialgebras.Models.CatProductPi
public import Foundations.CategoryTheory.Limits.OpTranslate

/-!
# Theorem 4.19: lifting wide pushouts to categorical models

The two conclusions of Corollary 4.18 propagate through interpretation of
terms. Apply the model's Kan-extension creation theorem to the function and
equation arities of the resulting wide-pushout diagram.

## Main results

* `UlmerBialgebras.RegEpiWide.thy_strictlyCreates_widePushouts`: Theorem 4.19, the forgetful functor
  of `M^T` strictly creates wide pushouts of arrows it sends to regular epimorphisms.
* `UlmerBialgebras.RegEpiWide.tm_maps_regularEpis`: if the function symbols preserve regular
  epimorphisms, every term sends componentwise regular epimorphisms to regular epimorphisms.
* `UlmerBialgebras.RegEpiWide.tm_preservesWidePushout`: if moreover the function symbols preserve
  wide pushouts of regular epimorphisms, every term preserves wide pushouts whose legs are
  componentwise regular epimorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.18
  and Theorem 4.19
-/

@[expose] public section

universe v u w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.RegEpiWide

open CategoryTheory Limits
open UlmerBialgebras.Paper

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u}) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]

omit [HasChosenProductsOfSize.{s₂} Cat.{v, u}] in
/-- Regular-epi preservation by the atomic functors propagates to every term.
The input only needs to be componentwise regular epic, even for infinitely many sorts. -/
theorem tm_maps_regularEpis
    (hfn : ∀ (B : Sg.Fun) ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄
      (f : x ⟶ y), IsRegularEpi f →
        IsRegularEpi ((M.fn B).toFunctor.map f))
    {cc : Sg.Cat} (t : sg.CTrm cc)
    {x y : ((M.P0 sg).pt : Type u)} (f : x ⟶ y)
    (hf : ∀ s, IsRegularEpi (((M.P0 sg).π s).toFunctor.map f)) :
    IsRegularEpi ((M.tm sg t).toFunctor.map f) := by
  classical
  induction t with
  | var s => exact hf s
  | app B args ih =>
      change IsRegularEpi ((M.fn B).toFunctor.map
        (fun i => (M.tm sg (args i)).toFunctor.map f))
      exact hfn B _ (isRegularEpi_of_piRegEpi _ ih)

omit [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}] in
/-- A functor into a product preserves the colimit of a single diagram if
each component does. No existence of the colimit is required. -/
theorem pi'_preservesColimit {J : Type*} [Category J] {A : Type*} [Category A]
    {ι : Type*} {C : ι → Type*} [∀ i, Category (C i)]
    (D : J ⥤ A) (F : ∀ i, A ⥤ C i) [∀ i, PreservesColimit D (F i)] :
    PreservesColimit D (Functor.pi' F) := by
  refine ⟨fun hc => ⟨piIsColimitOfEval fun i => isColimitOfPreserves (F i) hc⟩⟩

omit [HasChosenProductsOfSize.{s₂} Cat.{v, u}] in
/-- Preservation of wide pushouts whose input legs are componentwise regular
epis propagates through interpretation of terms. -/
theorem tm_preservesWidePushout (K : Type w)
    (hfn : ∀ (B : Sg.Fun) ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄
      (f : x ⟶ y), IsRegularEpi f →
        IsRegularEpi ((M.fn B).toFunctor.map f))
    (hwide : ∀ B : Sg.Fun,
      PreservesWidePushoutsOfRegEpis K (M.fn B).toFunctor)
    (D : WidePushoutShape K ⥤ ((M.P0 sg).pt : Type u))
    (hD : ∀ k s, IsRegularEpi (((M.P0 sg).π s).toFunctor.map (D.map (WidePushoutShape.Hom.init k))))
    {cc : Sg.Cat} (t : sg.CTrm cc) :
    PreservesColimit D (M.tm sg t).toFunctor := by
  classical
  induction t with
  | var s => exact Product.π_preservesColimit (M.P0 sg) D s
  | app B args ih =>
      let G : ((M.P0 sg).pt : Type u) ⥤ (M.P B).pt :=
        Functor.pi' fun i => (M.tm sg (args i)).toFunctor
      have : ∀ i, PreservesColimit D (M.tm sg (args i)).toFunctor := ih
      have : PreservesColimit D G := pi'_preservesColimit D _
      have : PreservesColimit (D ⋙ G) (M.fn B).toFunctor :=
        hwide B (D ⋙ G) (fun k => by
          have hreg : IsRegularEpi ((D ⋙ G).map (WidePushoutShape.Hom.init k)) :=
            isRegularEpi_of_piRegEpi _ (fun i =>
              tm_maps_regularEpis M sg hfn (args i)
                (D.map (WidePushoutShape.Hom.init k)) (hD k))
          exact hreg.regularEpi)
      change PreservesColimit D (G ⋙ (M.fn B).toFunctor)
      infer_instance

omit [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}] in
/-- Preservation of the colimit of `e.functor ⋙ D` along an equivalence `e` of shapes gives the
preservation of the colimit of `D`. -/
theorem preservesColimit_of_whiskerEquivalence {J J' : Type*} [Category J] [Category J']
    (e : J ≌ J') {A B : Type*} [Category A] [Category B] (D : J' ⥤ A) (F : A ⥤ B)
    [PreservesColimit (e.functor ⋙ D) F] : PreservesColimit D F :=
  ⟨fun hc => ⟨IsColimit.ofWhiskerEquivalence e
    (isColimitOfPreserves F (hc.whiskerEquivalence e))⟩⟩

omit [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}] in
/-- Single-diagram colimit preservation implies preservation of the
corresponding left Kan extensions along the unique functor to `1`. -/
theorem preservesLeftKan_of_preservesColimit_single {I C D : Cat.{v, u}}
    (F : C ⟶ D) (d : I ⟶ C)
    [PreservesColimit (d).toFunctor (F).toFunctor] :
    PreservesLeftKan (toOne I) d F := by
  intro L hL
  refine ⟨isInitialLeftExtOfIsColimit ?_⟩
  refine IsColimit.ofIsoColimit ?_ (coconeOfLeftExtPushIso F L).symm
  exact isColimitOfPreserves (F).toFunctor (isColimitCoconeOfLeftExt hL.some)

variable [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]

/-- **Theorem 4.19** ([forsman2026syntactic]): strict creation of wide pushouts of arrows which
the forgetful functor sends to regular epis. -/
theorem thy_strictlyCreates_widePushouts (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] (K : Type w) [Nontrivial K]
    (hreg : ∀ c : Sg.Cat, RegEpisAreReflexiveCoequalizers (M.obj c : Type u))
    (hB : ∀ (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
      PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙
        (M.fn B).toFunctor))
    (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u))
    (d : J ⟶ M.thyObj sg T)
    (hd : ∀ j, Nonempty (RegularEpi ((d ≫ M.thyForget sg T).toFunctor.map
        (e.functor.map (WidePushoutShape.Hom.init j))))) :
    StrictlyCreatesLeftKan (toOne J) d (M.thyForget sg T) := by
  classical
  have hB' : ∀ B : Sg.Fun,
      PreservesWidePushoutsOfRegEpis K (M.fn B).toFunctor ∧
        ∀ ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄ (f : x ⟶ y),
          Nonempty (RegularEpi f) → Nonempty (RegularEpi ((M.fn B).toFunctor.map f)) :=
    fun B => preservesWidePushouts_and_regularEpis_pi (M.fn B).toFunctor
      (fun i => hreg (Sg.art B i)) (hB B)
  have hfn : ∀ (B : Sg.Fun) ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄
      (f : x ⟶ y), IsRegularEpi f → IsRegularEpi ((M.fn B).toFunctor.map f) :=
    fun B _ _ f hf => ⟨(hB' B).2 f hf.regularEpi⟩
  let D : WidePushoutShape K ⥤ ((M.P0 sg).pt : Type u) :=
    e.functor ⋙ (d ≫ M.thyForget sg T).toFunctor
  have hD : ∀ k s, IsRegularEpi
      (((M.P0 sg).π s).toFunctor.map (D.map (WidePushoutShape.Hom.init k))) := by
    intro k s
    have : IsRegularEpi (D.map (WidePushoutShape.Hom.init k)) := ⟨hd k⟩
    have : PreservesColimitsOfShape WalkingParallelPair ((M.P0 sg).π s).toFunctor :=
      ⟨fun {_} => inferInstance⟩
    exact OpTranslate.isRegularEpi_map _ _
  have htm : ∀ {cc : Sg.Cat} (t : sg.CTrm cc),
      PreservesLeftKan (toOne J) (d ≫ M.thyForget sg T) (M.tm sg t) := by
    intro cc t
    have := tm_preservesWidePushout M sg K hfn (fun B => (hB' B).1) D hD t
    have := preservesColimit_of_whiskerEquivalence e (d ≫ M.thyForget sg T).toFunctor
      (M.tm sg t).toFunctor
    exact preservesLeftKan_of_preservesColimit_single (M.tm sg t) _
  refine M.thy_strictlyCreates_leftKan sg T _ d (fun f => htm (sg.fndom f)) ?_
  intro r L hL
  exact quotientInitial_of_isInitial ((htm (T.dom r) L hL).some)

end UlmerBialgebras.RegEpiWide
