module

public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import UlmerBialgebras.Paper.Sec3DefsLaxLimit
public import UlmerBialgebras.Proofs.Sec3.HopfModelEquiv
public import UlmerBialgebras.Proofs.Sec3.LaxLimitEquivSMon

/-!
# Solution: Examples 3.20 (2) and (4)

* Hopf algebras: for the Hopf model of a braided monoidal category `C`
  (`UlmerBialgebras/Paper/Sec3DefsHopfModel.lean`), the category `M^{T_Hopf}` is Mathlib's category
  `Hopf C` of
  Hopf monoids. The paper states this for symmetric monoidal `C`.
* Lax-limit theories: the theory `T_Lax` of a 2-signature is algebraic, and for the
  signatures of a monad, a monoidal category and a symmetric monoidal category it is the
  theory of monad algebras, monoids and commutative monoids
  (`UlmerBialgebras/Paper/Sec3DefsLaxLimit.lean`).

## Main results

* `UlmerBialgebras.Paper.ex_3_20_2`: Examples 3.20 (2), `M^{T_Hopf}` is isomorphic over `C` to
  `Hopf C`.
* `UlmerBialgebras.Paper.ex_3_20_4_algebraic`: Examples 3.20 (4), `T_Lax` is algebraic.
* `UlmerBialgebras.Paper.ex_3_20_4_mnd`: Examples 3.20 (4), `M^{T_Lax}` is isomorphic over `C` to
  `T.Algebra`.
* `UlmerBialgebras.Paper.ex_3_20_4_mon`: Examples 3.20 (4), `M^{T_Lax}` is isomorphic over `C` to
  `Mon C`.
* `UlmerBialgebras.Paper.ex_3_20_4_smon`: Examples 3.20 (4), `M^{T_Lax}` is isomorphic over `C` to
  `CommMon C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.20
  (2) and (4)
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
* [A. Joyal, R. Street, *Braided Tensor Categories*][joyalBraidedTensorCategories1993]
* [R. Street, *Quantum Groups: A Path to Current Algebra*][streetQuantumGroupsPath2007]
* [R. Street, *Limits indexed by category-valued 2-functors*][streetLimitsIndexedCategoryvalued1976]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v uu₁ uu₂ uu₃

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory

/-- **Examples 3.20 (2)**: for the Hopf model `M` of a braided monoidal category `C`, the
category `M^{T_Hopf}` is the category of Hopf monoids in `C`. There are mutually inverse functors
`F : M^{T_Hopf} ⥤ Hopf C` and `G : Hopf C ⥤ M^{T_Hopf}` (an isomorphism of categories), and `F`
lies over `C`. Here `M^{T_Hopf}` lies over `C` through the forgetful 1-cell
`U : M^{T_Hopf} → M₀` followed by the projection `M₀ = ∏_{s} C → C` at the unique sort `s`, and
`Hopf C` lies over `C` through the forgetful functor `HopfModel.hopfForget C`.

References: [forsman2026syntactic]. -/
theorem ex_3_20_2 (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    ∃ (F : HopfModel.ThyObj C ⥤ Hopf C) (G : Hopf C ⥤ HopfModel.ThyObj C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ HopfModel.hopfForget C =
          (HopfModel.forget C).toFunctor ⋙
            (((HopfModel.hopfModel C).P0 HopfEx.oneSig).π ()).toFunctor :=
  ⟨HopfModel.Internal.comparison C, HopfModel.Internal.inverseFunctor C,
    HopfModel.Internal.comparison_comp_inverseFunctor C,
    HopfModel.Internal.inverseFunctor_comp_comparison C,
    HopfModel.Internal.comparison_comp_hopfForget C⟩

/-- **Examples 3.20 (4)** ([forsman2026syntactic]): the lax-limit theory `T_Lax` of a 2-signature is
algebraic. -/
theorem ex_3_20_4_algebraic (Sg : TwoSig.{uu₁, uu₂, uu₃}) : (LaxEx.theory Sg).IsAlgebraic :=
  LaxEx.theory_isAlgebraic Sg

/-- **Examples 3.20 (4)**, monads: for a monad `T` on `C`, viewed as a `Σ_Mnd`-model,
`M^{T_Lax}` is the Eilenberg–Moore category of `T`. There are mutually inverse functors
`F : M^{T_Lax} ⥤ T.Algebra` and `G : T.Algebra ⥤ M^{T_Lax}` (an isomorphism of categories), and
`F` lies over `C`. Here `M^{T_Lax}` lies over `C` through the forgetful 1-cell
`U : M^{T_Lax} → M₀` followed by the projection `M₀ = ∏_{s} C → C` at the unique sort `s`, and
`T.Algebra` lies over `C` through `T.forget`.

References: [forsman2026syntactic]. -/
theorem ex_3_20_4_mnd {C : Type (max u v)} [Category.{v} C] (T : Monad C) :
    ∃ (F : LaxLimit.ThyObj (MndEx.model T) ⥤ T.Algebra)
      (G : T.Algebra ⥤ LaxLimit.ThyObj (MndEx.model T)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ T.forget = ((MndEx.model T).thyForget (LaxEx.oneSig SigEx.mndSig)
            (LaxEx.theory SigEx.mndSig)).toFunctor ⋙
          (((MndEx.model T).P0 (LaxEx.oneSig SigEx.mndSig)).π ()).toFunctor :=
  ⟨LaxLimit.Internal.MndCase.comparison T, LaxLimit.Internal.MndCase.inverseFunctor T,
    LaxLimit.Internal.MndCase.comparison_comp_inverseFunctor T,
    LaxLimit.Internal.MndCase.inverseFunctor_comp_comparison T,
    LaxLimit.Internal.MndCase.comparison_comp_forget T⟩

/-- **Examples 3.20 (4)**, monoidal categories: for a monoidal category `C`, viewed as a
`Σ_Mon`-model, `M^{T_Lax}` is the category of monoids in `C`. There are mutually inverse functors
`F : M^{T_Lax} ⥤ Mon C` and `G : Mon C ⥤ M^{T_Lax}` (an isomorphism of categories), and `F` lies
over `C`. Here `M^{T_Lax}` lies over `C` through the forgetful 1-cell `U : M^{T_Lax} → M₀`
followed by the projection `M₀ = ∏_{s} C → C` at the unique sort `s`, and `Mon C` lies over `C`
through `Mon.forget C`.

References: [forsman2026syntactic]. -/
theorem ex_3_20_4_mon (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] :
    ∃ (F : LaxLimit.ThyObj (LaxLimit.monModel C) ⥤ Mon C)
      (G : Mon C ⥤ LaxLimit.ThyObj (LaxLimit.monModel C)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Mon.forget C = ((LaxLimit.monModel C).thyForget (LaxEx.oneSig SigEx.monSig)
            (LaxEx.theory SigEx.monSig)).toFunctor ⋙
          (((LaxLimit.monModel C).P0 (LaxEx.oneSig SigEx.monSig)).π ()).toFunctor :=
  ⟨LaxLimit.Internal.MonCase.comparison C, LaxLimit.Internal.MonCase.inverseFunctor C,
    LaxLimit.Internal.MonCase.comparison_comp_inverseFunctor C,
    LaxLimit.Internal.MonCase.inverseFunctor_comp_comparison C,
    LaxLimit.Internal.MonCase.comparison_comp_forget C⟩

/-- **Examples 3.20 (4)**, symmetric monoidal categories: for a symmetric monoidal category
`C`, viewed as a `Σ_SMon`-model, `M^{T_Lax}` is the category of commutative monoids in `C`. There
are mutually inverse functors `F : M^{T_Lax} ⥤ CommMon C` and `G : CommMon C ⥤ M^{T_Lax}` (an
isomorphism of categories), and `F` lies over `C`. Here `M^{T_Lax}` lies over `C` through the
forgetful 1-cell `U : M^{T_Lax} → M₀` followed by the projection `M₀ = ∏_{s} C → C` at the unique
sort `s`, and `CommMon C` lies over `C` through `CommMon.forget C`.

References: [forsman2026syntactic]. -/
theorem ex_3_20_4_smon (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] :
    ∃ (F : LaxLimit.ThyObj (Loc.smonModel C) ⥤ CommMon C)
      (G : CommMon C ⥤ LaxLimit.ThyObj (Loc.smonModel C)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ CommMon.forget C = ((Loc.smonModel C).thyForget (LaxEx.oneSig SigEx.smonSig)
            (LaxEx.theory SigEx.smonSig)).toFunctor ⋙
          (((Loc.smonModel C).P0 (LaxEx.oneSig SigEx.smonSig)).π ()).toFunctor :=
  ⟨LaxLimit.Internal.SMonCase.comparison C, LaxLimit.Internal.SMonCase.inverseFunctor C,
    LaxLimit.Internal.SMonCase.comparison_comp_inverseFunctor C,
    LaxLimit.Internal.SMonCase.inverseFunctor_comp_comparison C,
    LaxLimit.Internal.SMonCase.comparison_comp_forget C⟩

end UlmerBialgebras.Paper
