module

public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import UlmerBialgebras.Kan.SiftedModel

/-!
# The forgetful functor `Hopf_k ⥤ Vect_k`, and the hypotheses of the closing remark of Example 4.20

For a field `k`, the Hopf monoids in `Vect_k` are the bialgebras of the Hopf model of
`ModuleCat.{u} k`. This file defines their forgetful functor to `ModuleCat k`, used in the `Vect_k`
case of Example 4.20 (`UlmerBialgebras/Paper/Sec4Ex420.lean`).

The closing remark of Example 4.20 asks of a `Σ`-model `M` in `CAT` that its categories `M_c`
have, and its functors `M(B)` preserve componentwise, sifted colimits and finite cosifted limits,
and that the categories `M_c` have kernel pairs and cokernel pairs. These are the four conditions
`Model.SiftedColimitsComponentwise`, `Model.FinCosiftedLimitsComponentwise`,
`Model.HasKernelPairs` and `Model.HasCokernelPairs`.

## Main definitions

* `UlmerBialgebras.Paper.hopfVectForget`
* `UlmerBialgebras.Model.SiftedColimitsComponentwise`
* `UlmerBialgebras.Model.FinCosiftedLimitsComponentwise`
* `UlmerBialgebras.Model.HasKernelPairs`
* `UlmerBialgebras.Model.HasCokernelPairs`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20
-/

@[expose] public section


universe v u u₁ u₂ u₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- The forgetful functor `Hopf_k ⥤ Vect_k` from Hopf monoids in `Vect_k` (the bialgebras of the
Hopf model of `ModuleCat k`) to `k`-modules: `U : M^{T_Hopf} → M₀` followed by the projection at
the single sort. -/
def hopfVectForget (k : Type u) [Field k] :
    HopfModel.thyCat (ModuleCat.{u} k) ⥤ ModuleCat.{u} k :=
  (HopfModel.forget (ModuleCat.{u} k) ≫
    ((HopfModel.hopfModel (ModuleCat.{u} k)).P0 HopfEx.oneSig).π ()).toFunctor

end UlmerBialgebras.Paper

namespace UlmerBialgebras.Model

open CategoryTheory Limits

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})

/-- The categories `M_c` have, and the functors `M(B)` preserve componentwise, the colimits of
every small sifted shape `J`: small relative to `CAT = Cat.{v, u}`, that is, with objects and
morphisms in the hom universe `Type v`. -/
def SiftedColimitsComponentwise : Prop :=
  ∀ (J : Type v) [SmallCategory J] [IsSifted J],
    (∀ c, HasColimitsOfShape J (M.obj c : Type u)) ∧ ∀ B, PreservesColimitsComponentwise M J B

/-- The categories `M_c` have, and the functors `M(B)` preserve in each variable, the limits of
every finite cosifted shape `J : Type`. -/
def FinCosiftedLimitsComponentwise : Prop :=
  ∀ (J : Type) [SmallCategory J] [FinCategory J] [IsCosifted J],
    (∀ c, HasLimitsOfShape J (M.obj c : Type u)) ∧
      ∀ (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
        Nonempty (PreservesLimitsOfShape J (updateFunctor x i ⋙ (M.fn B).toFunctor))

/-- Every morphism of every category `M_c` has a kernel pair. -/
def HasKernelPairs : Prop := ∀ c {X Y : (M.obj c : Type u)} (f : X ⟶ Y), HasPullback f f

/-- Every morphism of every category `M_c` has a cokernel pair. -/
def HasCokernelPairs : Prop := ∀ c {X Y : (M.obj c : Type u)} (f : X ⟶ Y), HasPushout f f

end UlmerBialgebras.Model
