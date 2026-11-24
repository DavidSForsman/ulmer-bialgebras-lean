module

public import Mathlib.CategoryTheory.Monad.Monadicity
public import UlmerBialgebras.Monadicity.SubTheoryColimits
public import UlmerBialgebras.Monadicity.SplitCreate
public import UlmerBialgebras.Monadicity.FreeIns
public import UlmerBialgebras.Monadicity.FreeEquif
public import Foundations.CategoryTheory.Limits.PiAdjoint
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Coequalizer

/-!
# Free bialgebras and monadicity of the forgetful functor

For a categorical `Σ`-model `M` and an **algebraic** `σ`-theory `T`, the forgetful functor
`U : M^T → M₀` has a left adjoint and is monadic. This file contains the lemmas on the term
1-cells used for that (listed below); the construction and the monadicity proof are elsewhere.

The construction proceeds in the two steps by which `M^T` is built out of `M₀`:

* the inserter step `u : M^σ → M₀`, whose left adjoint is produced by the free-algebra
  chain of `FreeIns.lean`; the required left adjoint of the coarity 1-cell `M(t₂)` exists
  because `T` is algebraic, so that `M(t₂)` is a product of projections (`PiAdjoint.lean`);
* the equifier step `e : M^T → M^σ`, whose left adjoint is produced by the chain of
  coequalizers of `FreeEquif.lean`.

Monadicity is then obtained from the reflexive (crude) monadicity theorem, using that both
forgetful functors are conservative and create reflexive coequalizers (Corollary 4.17).

Everything is stated with explicit hypotheses of the shape "`M₀` has colimits of shape `J`"
and "`M(B)` preserves colimits of shape `J` componentwise"; the packaging of these
hypotheses in terms of an infinite cardinal `κ` uses the shapes of `KappaShapes.lean`.

## Main results

* `UlmerBialgebras.preservesColimitsOfShape_of_preservesLeftKan`: a 1-cell of `CAT` preserving all
  left Kan extensions along `I ⟶ 1` preserves `I`-colimits.
* `UlmerBialgebras.preservesColimitsOfShape_tm`, `UlmerBialgebras.preservesColimitsOfShape_domCell`:
  for sifted `I`, the term 1-cells and the arity 1-cell preserve the `I`-colimits which the functor
  symbols preserve componentwise.
* `UlmerBialgebras.isRightAdjoint_tm_of_isVar`: a term which is a sort is interpreted by a right
  adjoint when all the factors have initial objects.
* `UlmerBialgebras.isRightAdjoint_codCell`: if every function coarity term is a sort, the coarity
  1-cell `M(t₂) : M₀ → ∏_f M_{c_f}` is a right adjoint.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5, Theorem 5.7 and Corollary 5.8
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe v u w w' u₁ u₂ u₃ s₁ s₂

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## Colimits from left Kan extensions -/

/-- The converse of `UlmerBialgebras.preservesLeftKan_of_preservesColimitsOfShape`: a 1-cell of
`CAT` preserving all left Kan extensions along `I ⟶ 1` preserves `I`-colimits. -/
theorem preservesColimitsOfShape_of_preservesLeftKan {I C D : Cat.{v, u}} (F : C ⟶ D)
    (h : ∀ d : I ⟶ C, PreservesLeftKan (toOne I) d F) :
    PreservesColimitsOfShape (I : Type u) (F).toFunctor := by
  constructor
  intro d
  constructor
  intro c hc
  have h2 := h d.toCatHom (leftExtOfCocone c) ⟨isInitialLeftExtOfIsColimit hc⟩
  exact ⟨IsColimit.ofIsoColimit (isColimitCoconeOfLeftExt h2.some)
    (coconeOfLeftExtPushIso F (leftExtOfCocone c))⟩

/-! ## Reflexive coequalizers -/

/-! ## Term supports preserve sifted colimits -/

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})

/-- The interpretation `M.interp ρ t` of a term preserves the sifted colimits which the functor
symbols preserve componentwise, as soon as every component of the environment `ρ` preserves them
(Lemma 4.16 for each functor symbol, by induction on `t`). -/
theorem preservesColimitsOfShape_interp (J : Type w') [Category.{w} J] [IsSifted J]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M J B)
    {V : Type*} {vty : V → Sg.Cat} {X : Cat.{v, u}} (ρ : ∀ x, X ⟶ M.obj (vty x))
    (hρ : ∀ x, PreservesColimitsOfShape J (ρ x).toFunctor) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    PreservesColimitsOfShape J (M.interp ρ t).toFunctor := by
  induction t with
  | var x => exact hρ x
  | app B args ih =>
    have := preservesColimitsOfShape_pi_of_componentwise (J := J) (M.fn B).toFunctor
      (fun i x => (hB B i x).some)
    have : PreservesColimitsOfShape J (Functor.pi' fun i =>
        (M.interp ρ (args i)).toFunctor) :=
      pi'PreservesColimitsOfShape _
    exact comp_preservesColimitsOfShape (Functor.pi' fun i =>
        (M.interp ρ (args i)).toFunctor) (M.fn B).toFunctor

/-- A lift into a strict product in `CAT` is a right adjoint when its components are, as soon as
its source has coproducts of the shape of the product. -/
theorem Product.lift_isRightAdjoint {ι : Type w'} {c : ι → Cat.{v, u}} (P : Product c)
    {X : Cat.{v, u}} (g : ∀ i, X ⟶ c i) [∀ i, (g i).toFunctor.IsRightAdjoint]
    [HasCoproductsOfShape ι (X : Type u)] : (P.lift g).toFunctor.IsRightAdjoint := by
  have := pi'_isRightAdjoint (fun i => (g i).toFunctor)
  let e := (Product.toPi P).asEquivalence
  have h : (P.lift g).toFunctor ≅ Functor.pi' (fun i => (g i).toFunctor) ⋙ e.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (Product.lift_comp_toPi P g)) _
  exact Functor.isRightAdjoint_of_iso h.symm

variable (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]

/-- Term supports preserve the sifted colimits which the functor symbols preserve
componentwise. -/
theorem preservesColimitsOfShape_tm (J : Type w') [Category.{w} J] [IsSifted J]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M J B) {c : Sg.Cat} (t : sg.CTrm c) :
    PreservesColimitsOfShape J (M.tm sg t).toFunctor :=
  preservesColimitsOfShape_interp M J hB (M.P0 sg).π
    (fun s => ⟨fun {K} => Product.π_preservesColimit (M.P0 sg) K s⟩) t

/-- The arity 1-cell preserves the sifted colimits which the functor symbols preserve
componentwise. -/
theorem preservesColimitsOfShape_domCell [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (J : Type w')
    [Category.{w} J] [IsSifted J] (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M J B) :
    PreservesColimitsOfShape J (M.domCell sg).toFunctor := by
  constructor
  intro K
  have : ∀ f : sg.Fn, PreservesColimit K (M.tm sg (sg.fndom f)).toFunctor :=
    fun f => (preservesColimitsOfShape_tm M sg J hB (sg.fndom f)).preservesColimit
  exact Product.lift_preservesColimit (M.Pfn sg) _ K

/-! ## Left adjoints -/

/-- A term which is a sort is interpreted by a projection, which has a left adjoint as soon
as all the factors have initial objects. -/
theorem isRightAdjoint_tm_of_isVar [∀ s : sg.Srt, HasInitial (M.obj (sg.sty s) : Type u)]
    {c : Sg.Cat} (t : sg.CTrm c) (ht : t.IsVar) :
    (M.tm sg t).toFunctor.IsRightAdjoint := by
  classical
  cases t with
  | var s =>
    have := UlmerBialgebras.Pi.eval_isRightAdjoint
      (fun s : sg.Srt => (M.obj (sg.sty s) : Type u)) s
    change ((M.P0 sg).π s).toFunctor.IsRightAdjoint
    rw [← Product.toPi_comp_eval]
    infer_instance
  | app B args => exact ht.elim

/-- For an algebraic theory the coarity 1-cell `M(t₂) : M₀ → ∏_f M_{c_f}` has a left
adjoint. -/
theorem isRightAdjoint_codCell [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (hfn : ∀ f : sg.Fn, (sg.fncod f).IsVar)
    [∀ s : sg.Srt, HasInitial (M.obj (sg.sty s) : Type u)]
    [HasCoproductsOfShape sg.Fn ((M.P0 sg).pt : Type u)] :
    (M.codCell sg).toFunctor.IsRightAdjoint := by
  have : ∀ f : sg.Fn,
      (M.tm sg (sg.fncod f)).toFunctor.IsRightAdjoint :=
    fun f => isRightAdjoint_tm_of_isVar M sg _ (hfn f)
  exact Product.lift_isRightAdjoint (M.Pfn sg) _

end UlmerBialgebras
