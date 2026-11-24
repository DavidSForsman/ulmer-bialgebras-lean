module

public import UlmerBialgebras.Examples.FieldEx
public import UlmerBialgebras.Examples.SetFunctors
public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Kan.LimKan

/-!
# The set-theoretic model of the field signature, towards Corollary 4.21

This file provides the categorical `Σ`-model

`M = (Set, ×, 1, (−) + 1)`

of Examples 3.20 (3), where `M(η)` is the unit of the maybe monad, together with the
preservation properties of its interpretations which yield, via Corollary 4.12, **Corollary
4.21** for the object of `T_Field`-bialgebras over it: the forgetful functor
`U : M^T → M₀` strictly creates

* all **connected** limits — the product `× : Set² → Set` is a right adjoint, the constant `1`
  preserves connected limits and `(−) + 1` preserves connected limits;
* all **sifted** colimits — the product is a left adjoint in each variable separately, hence
  preserves sifted colimits by Lemma 4.16, the constant preserves connected colimits, and
  `(−) + 1` preserves connected colimits.

In particular `M^T` has connected limits and sifted colimits as soon as `Set` does.  The model lives
in `Cat.{u, u + 1}`, with `Set = Type u` itself.

The identification `M^T ≃ Field` of the paper is carried out in `FieldCalc.lean`,
`FieldRing.lean` and `FieldEquiv.lean`.  The resulting statements about connected limits and
sifted colimits, for `M^T` and for the category of fields itself, are in `FieldLimits.lean`.

## Main results

* `UlmerBialgebras.FieldEx.SetCat`: the category `Type u` of `u`-small sets.
* `UlmerBialgebras.FieldEx.prodFunctorU`, `UlmerBialgebras.FieldEx.unitFunctorU`,
  `UlmerBialgebras.FieldEx.succFunctorU`: the interpretations `×`, `1` and `(−) + 1`.
* `UlmerBialgebras.FieldEx.model`: the categorical `Σ`-model `M = (Set, ×, 1, (−) + 1)` of
  Examples 3.20 (3).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3) and Corollary 4.21
-/

@[expose] public section

universe u

namespace UlmerBialgebras

namespace FieldEx

open CategoryTheory Limits

/-! ## The category of sets -/

/-- The category of `u`-small sets, `Type u`, an object of the 2-category `Cat.{u, u + 1}`. -/
abbrev SetCat := Type u

/-- The product of sets, on the two-fold power of `SetCat`. -/
noncomputable def prodFunctorU : (∀ _ : Fin 2, SetCat.{u}) ⥤ SetCat.{u} := prodFunctor

/-- The singleton set, on the empty power of `SetCat`. -/
noncomputable def unitFunctorU : (∀ _ : Fin 0, SetCat.{u}) ⥤ SetCat.{u} := unitFunctor

/-- The maybe functor `(−) + 1`, on the one-fold power of `SetCat`. -/
noncomputable def succFunctorU : (∀ _ : Fin 1, SetCat.{u}) ⥤ SetCat.{u} := succFunctor

/-! ## The model -/

/-- The interpretation of the category and functor symbols of `Σ` in sets. -/
noncomputable def preModel : PreModel twoSig Cat.{u, u + 1} where
  obj := fun _ => Cat.of SetCat.{u}
  fn := fun B => match B with
    | .tens => prodFunctorU.toCatHom
    | .unit => unitFunctorU.toCatHom
    | .succ => succFunctorU.toCatHom

/-- The diagonal `x → x × x`, as the interpretation of `δ`. -/
noncomputable def diagCell :
    preModel.interp (preModel.Pctx TrSym.diag).π (twoSig.trsrc TrSym.diag) ⟶
      preModel.interp (preModel.Pctx TrSym.diag).π (twoSig.trtgt TrSym.diag) where
  toNatTrans := {
    app _ := TypeCat.ofHom (fun x => (x, x))
    naturality _ _ _ := rfl }

/-- The first projection `x × y → x`, as the interpretation of `p₁`. -/
noncomputable def proj₁Cell :
    preModel.interp (preModel.Pctx TrSym.proj₁).π (twoSig.trsrc TrSym.proj₁) ⟶
      preModel.interp (preModel.Pctx TrSym.proj₁).π (twoSig.trtgt TrSym.proj₁) where
  toNatTrans := {
    app _ := TypeCat.ofHom Prod.fst
    naturality _ _ _ := rfl }

/-- The second projection `x × y → y`, as the interpretation of `p₂`. -/
noncomputable def proj₂Cell :
    preModel.interp (preModel.Pctx TrSym.proj₂).π (twoSig.trsrc TrSym.proj₂) ⟶
      preModel.interp (preModel.Pctx TrSym.proj₂).π (twoSig.trtgt TrSym.proj₂) where
  toNatTrans := {
    app _ := TypeCat.ofHom Prod.snd
    naturality _ _ _ := rfl }

/-- The unique map `x → 1`, as the interpretation of `!`. -/
noncomputable def termCell :
    preModel.interp (preModel.Pctx TrSym.term).π (twoSig.trsrc TrSym.term) ⟶
      preModel.interp (preModel.Pctx TrSym.term).π (twoSig.trtgt TrSym.term) where
  toNatTrans := {
    app _ := TypeCat.ofHom (fun _ => PUnit.unit)
    naturality _ _ _ := rfl }

/-- The unit `x → x + 1` of the maybe monad, as the interpretation of `η`. -/
noncomputable def etaCell :
    preModel.interp (preModel.Pctx TrSym.eta).π (twoSig.trsrc TrSym.eta) ⟶
      preModel.interp (preModel.Pctx TrSym.eta).π (twoSig.trtgt TrSym.eta) where
  toNatTrans := {
    app _ := TypeCat.ofHom some
    naturality _ _ _ := rfl }

/-- **The categorical `Σ`-model `M = (Set, ×, 1, (−) + 1)`** of Examples 3.20 (3). -/
noncomputable def model : Model twoSig Cat.{u, u + 1} where
  toPreModel := preModel
  tr := fun a => match a with
    | .diag => diagCell
    | .proj₁ => proj₁Cell
    | .proj₂ => proj₂Cell
    | .term => termCell
    | .eta => etaCell

/-! ## Preservation properties of the interpretations -/

section Preservation

/-- Fixing the second argument of the product. -/
noncomputable def updateProdUZero (x : ∀ _ : Fin 2, SetCat.{u}) :
    updateFunctor x 0 ⋙ prodFunctorU.{u} ≅ prodRight (x 1) := Iso.refl _

/-- Fixing the first argument of the product. -/
noncomputable def updateProdUOne (x : ∀ _ : Fin 2, SetCat.{u}) :
    updateFunctor x 1 ⋙ prodFunctorU.{u} ≅ prodLeft (x 0) := Iso.refl _

/-- The maybe functor has one argument only. -/
noncomputable def updateSuccUZero (x : ∀ _ : Fin 1, SetCat.{u}) :
    updateFunctor x 0 ⋙ succFunctorU.{u} ≅ optionFunctor := Iso.refl _

end Preservation

/-! ## Corollary 4.21 (see `FieldLimits.lean`) -/

open UlmerBialgebras.Model

end FieldEx

end UlmerBialgebras
