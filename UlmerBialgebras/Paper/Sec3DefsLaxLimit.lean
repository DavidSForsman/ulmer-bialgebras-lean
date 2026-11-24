module

public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc
public import UlmerBialgebras.Examples.LaxTheoryEx
public import UlmerBialgebras.Examples.MonadEx

/-!
# Lax-limit theories and the monoidal model

The lax-limit theory `T_Lax` of a 2-signature `Σ` (`UlmerBialgebras.LaxEx.theory`) has one sort
`s_c` for each category symbol `c` of `Σ`, one function symbol `f_B : B(s_{c₁}, …, s_{cₙ}) → s_d`
for each functor symbol `B`, and one equation `f_{t₁(s̄)} = f_{t₂(s̄)} ∘ α_{s̄}` for each
transformation symbol `α : t₁ → t₂`.

The symmetric monoidal model is `UlmerBialgebras.Paper.Loc.smonModel` and the model of a monad is
`UlmerBialgebras.MndEx.model`.

## Main definitions

* `UlmerBialgebras.Paper.LaxLimit.ThyObj M`: the category `M^{T_Lax}` for a `Σ`-model `M` in `CAT`.
* `UlmerBialgebras.Paper.LaxLimit.monModel C`: a monoidal category `C` as a model of the 2-signature
  `Σ_Mon` (`UlmerBialgebras.SigEx.monSig`) in `CAT`. The six transformation symbols go to the
  associator, the two unitors and their inverses.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (4)
* [R. Street, *Limits indexed by category-valued 2-functors*][streetLimitsIndexedCategoryvalued1976]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe v u u₁ u₂ u₃

namespace UlmerBialgebras.Paper.LaxLimit

open CategoryTheory MonoidalCategory

/-- The category `M^{T_Lax}` (Examples 3.20 (4) of [forsman2026syntactic]) of bialgebras of the
lax-limit theory of `Σ` in a `Σ`-model `M`
in `CAT`. -/
abbrev ThyObj {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
    [HasChosenProductsOfSize.{u₁} Cat.{v, u}] [HasChosenProductsOfSize.{u₂} Cat.{v, u}]
    [HasChosenProductsOfSize.{u₃} Cat.{v, u}] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] : Type u :=
  (M.thyObj (LaxEx.oneSig Sg) (LaxEx.theory Sg) : Type u)

section Mon

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The interpretation of the category and functor symbols of `Σ_Mon`: the tensor product
and the unit. -/
def monPreModel : PreModel SigEx.monSig Cat.{v, u} where
  obj := fun _ => Cat.of C
  fn := fun B => match B with
    | .tens => (MonEx.tensFunctor C).toCatHom
    | .unit => (MonEx.unitFunctor C).toCatHom

/-- The interpretation of a transformation symbol of `Σ_Mon`. -/
def monCell : ∀ a : SigEx.MonTr,
    (monPreModel C).interp ((monPreModel C).Pctx a).π (SigEx.monSig.trsrc a) ⟶
      (monPreModel C).interp ((monPreModel C).Pctx a).π (SigEx.monSig.trtgt a)
  | .assoc =>
    { toNatTrans :=
      { app := fun p => (α_ (MonEx.ev C p 0) (MonEx.ev C p 1) (MonEx.ev C p 2)).hom
        naturality := fun _ _ f =>
          associator_naturality (MonEx.evMap C f 0) (MonEx.evMap C f 1) (MonEx.evMap C f 2) } }
  | .assocInv =>
    { toNatTrans :=
      { app := fun p => (α_ (MonEx.ev C p 0) (MonEx.ev C p 1) (MonEx.ev C p 2)).inv
        naturality := fun _ _ f =>
          associator_inv_naturality (MonEx.evMap C f 0) (MonEx.evMap C f 1) (MonEx.evMap C f 2) } }
  | .lunit =>
    { toNatTrans :=
      { app := fun p => (λ_ (MonEx.ev C p 0)).hom
        naturality := fun _ _ f => MonEx.lunit_naturality f 0 } }
  | .lunitInv =>
    { toNatTrans :=
      { app := fun p => (λ_ (MonEx.ev C p 0)).inv
        naturality := fun _ _ f => MonEx.lunit_inv_naturality f 0 } }
  | .runit =>
    { toNatTrans :=
      { app := fun p => (ρ_ (MonEx.ev C p 0)).hom
        naturality := fun _ _ f => MonEx.runit_naturality f 0 } }
  | .runitInv =>
    { toNatTrans :=
      { app := fun p => (ρ_ (MonEx.ev C p 0)).inv
        naturality := fun _ _ f => MonEx.runit_inv_naturality f 0 } }

/-- **A monoidal category is a `Σ_Mon`-model in `CAT`.** -/
def monModel : Model SigEx.monSig Cat.{v, u} where
  toPreModel := monPreModel C
  tr := monCell C

end Mon

end UlmerBialgebras.Paper.LaxLimit
