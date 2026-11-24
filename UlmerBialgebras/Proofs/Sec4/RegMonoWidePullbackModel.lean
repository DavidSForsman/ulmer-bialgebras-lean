module

public import UlmerBialgebras.Proofs.Sec4.Support.RegMonoCoreflexive
public import UlmerBialgebras.Proofs.Sec4.Support.RegMonoWidePullbackPi
public import UlmerBialgebras.Kan.KanModel
public import UlmerBialgebras.Kan.LimKan
public import Foundations.CategoryTheory.Limits.OpTranslate

/-!
# The dual of Theorem 4.19: lifting wide pullbacks to categorical models

Let `M` be a `Σ`-model in `CAT` such that every regular monomorphism of each `M_c` is the
equalizer of a coreflexive pair, and every functor symbol preserves `K`-wide pullbacks of
regular monomorphisms in each variable (`K` nontrivial). Then the forgetful 1-cell
`U : M^T → M₀` strictly creates the `K`-wide pullbacks of families of morphisms of `M^T`
that `U` sends to regular monomorphisms
(`UlmerBialgebras.RegMonoWide.thy_strictlyCreates_widePullbacks`).

The proof is the dual of `UlmerBialgebras/Proofs/Sec4/RegEpiWidePushoutModel.lean`: the dual of
Corollary 4.18
(`RegMonoWidePullbackPi.lean`), derived from the primal result through opposites, shows that
each `M(B)` preserves these wide pullbacks and regular monomorphisms, which propagates to all
term functors, and the creation theorem for right Kan extensions of the model then applies.

## Main results

* `UlmerBialgebras.RegMonoWide.thy_strictlyCreates_widePullbacks`: the dual of Theorem 4.19, the
  forgetful 1-cell of `M^T` strictly creates wide pullbacks of families it sends to regular
  monomorphisms.
* `UlmerBialgebras.RegMonoWide.Internal.tm_preservesWidePullback`: if the function symbols preserve
  regular monomorphisms and wide pullbacks of regular monomorphisms, every term preserves wide
  pullbacks whose legs are componentwise regular monomorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.18,
  Theorem 4.19 and Example 4.20 (2)
-/

@[expose] public section

universe w w' v u u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.RegMonoWide

open CategoryTheory Limits

namespace Internal

section Pi

variable {ι : Type w'} {C : ι → Type u} [∀ i, Category.{v} (C i)]

/-- Componentwise regular monomorphisms assemble by primal regular-epi assembly in opposites. -/
lemma isRegularMono_of_piRegMono {x y : ∀ j, C j} (m : x ⟶ y) (hm : piRegMono m) :
    IsRegularMono m := OpTranslate.isRegularMono_of_components C m hm

end Pi

/-- A functor into a product preserves the limit of a single diagram if each component
does. No existence of the limit is required. -/
theorem pi'_preservesLimit {J : Type*} [Category J] {A : Type*} [Category A]
    {ι : Type*} {C : ι → Type*} [∀ i, Category (C i)]
    (D : J ⥤ A) (F : ∀ i, A ⥤ C i) [∀ i, PreservesLimit D (F i)] :
    PreservesLimit D (Functor.pi' F) :=
  OpTranslate.pi'_preservesLimit_of_op C D F

/-- Single-diagram limit preservation implies preservation of the corresponding right Kan
extensions along the unique functor to `1`. -/
theorem preservesRightKan_of_preservesLimit_single {I C D : Cat.{v, u}}
    (F : C ⟶ D) (d : I ⟶ C)
    [PreservesLimit (d).toFunctor (F).toFunctor] :
    PreservesRightKan (toOne I) d F := by
  intro R hR
  refine ⟨isTerminalRightExtOfIsLimit ?_⟩
  refine IsLimit.ofIsoLimit ?_ (coneOfRightExtPushIso F R).symm
  exact isLimitOfPreserves (F).toFunctor (isLimitConeOfRightExt hR.some)

/-- Preservation of the limit of `e.functor ⋙ D` along an equivalence `e` of shapes gives the
preservation of the limit of `D`. -/
theorem preservesLimit_of_whiskerEquivalence {J J' : Type*} [Category J] [Category J']
    (e : J ≌ J') {A B : Type*} [Category A] [Category B] (D : J' ⥤ A) (F : A ⥤ B)
    [PreservesLimit (e.functor ⋙ D) F] : PreservesLimit D F :=
  ⟨fun hc => ⟨IsLimit.ofWhiskerEquivalence e
    (isLimitOfPreserves F (hc.whiskerEquivalence e))⟩⟩

section Model

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
  (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]

/-- Regular-mono preservation by the functor symbols propagates to every term. -/
theorem tm_maps_regularMonos
    (hfn : ∀ (B : Sg.Fun) ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄
      (f : x ⟶ y), IsRegularMono f → IsRegularMono ((M.fn B).toFunctor.map f))
    {cc : Sg.Cat} (t : sg.CTrm cc)
    {x y : ((M.P0 sg).pt : Type u)} (f : x ⟶ y)
    (hf : ∀ s, IsRegularMono (((M.P0 sg).π s).toFunctor.map f)) :
    IsRegularMono ((M.tm sg t).toFunctor.map f) := by
  classical
  induction t with
  | var s => exact hf s
  | app B args ih =>
      exact hfn B (fun i => (M.tm sg (args i)).toFunctor.map f) (isRegularMono_of_piRegMono _ ih)

/-- Preservation of wide pullbacks whose legs are componentwise regular monomorphisms
propagates to every term. -/
theorem tm_preservesWidePullback (K : Type w)
    (hfn : ∀ (B : Sg.Fun) ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄
      (f : x ⟶ y), IsRegularMono f → IsRegularMono ((M.fn B).toFunctor.map f))
    (hwide : ∀ B : Sg.Fun,
      PreservesWidePullbacksIn K (regMono _) (M.fn B).toFunctor)
    (D : WidePullbackShape K ⥤ ((M.P0 sg).pt : Type u))
    (hD : ∀ k s, IsRegularMono
      (((M.P0 sg).π s).toFunctor.map (D.map (WidePullbackShape.Hom.term k))))
    {cc : Sg.Cat} (t : sg.CTrm cc) :
    PreservesLimit D (M.tm sg t).toFunctor := by
  classical
  induction t with
  | var s => exact Product.π_preservesLimit (M.P0 sg) D s
  | app B args ih =>
      let G : ((M.P0 sg).pt : Type u) ⥤ (M.P B).pt :=
        Functor.pi' fun i => (M.tm sg (args i)).toFunctor
      have : ∀ i, PreservesLimit D (M.tm sg (args i)).toFunctor := ih
      have : PreservesLimit D G := pi'_preservesLimit D _
      have : PreservesLimit (D ⋙ G) (M.fn B).toFunctor :=
        hwide B (D ⋙ G) (fun k =>
          isRegularMono_of_piRegMono _ (fun i =>
            tm_maps_regularMonos M sg hfn (args i)
              (D.map (WidePullbackShape.Hom.term k)) (hD k)))
      exact (inferInstance : PreservesLimit D (G ⋙ (M.fn B).toFunctor))

end Model

end Internal

open Internal

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
  (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
  [HasChosenProductsOfSize.{s₂} Cat.{v, u}] [HasChosenInserters Cat.{v, u}]
  [HasChosenEquifiers Cat.{v, u}]

/-- **The dual of Theorem 4.19** ([forsman2026syntactic]): strict creation of the wide
pullbacks of families of morphisms which the forgetful 1-cell sends to regular monomorphisms. -/
theorem thy_strictlyCreates_widePullbacks (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] (K : Type w) [Nontrivial K]
    (hreg : ∀ c : Sg.Cat, RegularMonosAreCoreflexiveEqualizers (M.obj c : Type u))
    (hB : ∀ (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
      PreservesWidePullbacksIn K (regMono _) (updateFunctor x i ⋙
        (M.fn B).toFunctor))
    (J : Cat.{v, u}) (e : WidePullbackShape K ≌ (J : Type u))
    (d : J ⟶ M.thyObj sg T)
    (hd : ∀ j, Nonempty (RegularMono ((d ≫ M.thyForget sg T).toFunctor.map
        (e.functor.map (WidePullbackShape.Hom.term j))))) :
    StrictlyCreatesRightKan (toOne J) d (M.thyForget sg T) := by
  classical
  have hB' : ∀ B : Sg.Fun,
      PreservesWidePullbacksIn K (regMono _) (M.fn B).toFunctor ∧
        ∀ ⦃x y : ∀ j, (M.obj (Sg.art B j) : Type u)⦄ (f : x ⟶ y),
          IsRegularMono f → IsRegularMono ((M.fn B).toFunctor.map f) :=
    fun B => preservesWidePullbacks_and_regularMonos_pi (M.fn B).toFunctor
      (fun i => hreg (Sg.art B i)) (hB B)
  let D : WidePullbackShape K ⥤ ((M.P0 sg).pt : Type u) :=
    e.functor ⋙ (d ≫ M.thyForget sg T).toFunctor
  have hD : ∀ k s, IsRegularMono
      (((M.P0 sg).π s).toFunctor.map (D.map (WidePullbackShape.Hom.term k))) := by
    intro k s
    have : IsRegularMono (D.map (WidePullbackShape.Hom.term k)) := ⟨hd k⟩
    have : PreservesLimitsOfShape WalkingParallelPair ((M.P0 sg).π s).toFunctor :=
      ⟨fun {_} => inferInstance⟩
    exact OpTranslate.isRegularMono_map _ _
  have htm : ∀ {cc : Sg.Cat} (t : sg.CTrm cc),
      PreservesRightKan (toOne J) (d ≫ M.thyForget sg T) (M.tm sg t) := by
    intro cc t
    have := tm_preservesWidePullback M sg K (fun B => (hB' B).2) (fun B => (hB' B).1) D hD t
    have := preservesLimit_of_whiskerEquivalence e (d ≫ M.thyForget sg T).toFunctor
      (M.tm sg t).toFunctor
    exact preservesRightKan_of_preservesLimit_single (M.tm sg t) _
  refine M.thy_strictlyCreates_rightKan sg T _ d (fun f => htm (sg.fncod f)) ?_
  intro r R hR
  exact subterminal_of_isTerminal ((htm (T.cod r) R hR).some)

end UlmerBialgebras.RegMonoWide
