module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Examples.SignatureEx
public import UlmerBialgebras.Examples.MonModel
public import AffineGroupSchemes.VonNeumannRegular
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Challenge definitions for Lemma 6.10

* `UlmerBialgebras.Paper.Loc.smonModel C`: a symmetric monoidal category `C` as a model of the
  2-signature `Σ_SMon` (`UlmerBialgebras.SigEx.smonSig`) in `CAT`. The seven transformation symbols
  go to the associator, the two unitors, their inverses, and the symmetry.
* `UlmerBialgebras.Paper.Loc.ModU R`: the category of `R`-modules with its hom-sets lifted to
  `Type (u + 1)`, so that it is an object of `Cat.{u + 1, u + 1}`. The symmetric monoidal
  structure is transported from `ModuleCat.{u} R`.
* `UlmerBialgebras.Paper.Loc.modModel R`: `Mod_R` as a `Σ_SMon`-model.
* `UlmerBialgebras.Paper.Loc.locFunctor R p`: the localization `M ↦ R_p ⊗_R M`.
* `UlmerBialgebras.Paper.Loc.locSig R sg p`: localization on `M₀ = ∏_{s ∈ S} Mod_R`, componentwise.
* `UlmerBialgebras.Paper.Loc.modCatModel R`, `UlmerBialgebras.Paper.Loc.locSigCat R sg p`: the same
  for `ModuleCat.{u} R` itself, in `Cat.{u, u + 1}` (Lemma 6.10 is stated for these; `modModel`
  is its change of universe, used by the old form).

## Main results

* `UlmerBialgebras.Paper.Loc.smonModel`: a symmetric monoidal category as a `Σ_SMon`-model in `CAT`.
* `UlmerBialgebras.Paper.Loc.ModU`, `UlmerBialgebras.Paper.Loc.modModel`: `R`-modules with lifted
  hom-sets, and `Mod_R` as a `Σ_SMon`-model.
* `UlmerBialgebras.Paper.Loc.locFunctor`: the localization `M ↦ R_p ⊗_R M` (Lemma 6.10).
* `UlmerBialgebras.Paper.Loc.locSig`: the localization on `∏_{s ∈ S} Mod_R`, componentwise.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 (`Σ_SMon`), Lemma 6.10
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*]
  [atiyah_introduction_1969], Chapter 3
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory MonoidalCategory

/-! ## A symmetric monoidal category as a `Σ_SMon`-model -/

section SMon

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The interpretation of the category and functor symbols of `Σ_SMon`: the tensor product
and the unit. -/
def smonPreModel : PreModel SigEx.smonSig Cat.{v, u} where
  obj := fun _ => Cat.of C
  fn := fun B => match B with
    | .tens => (MonEx.tensFunctor C).toCatHom
    | .unit => (MonEx.unitFunctor C).toCatHom

/-- The interpretation of a transformation symbol of `Σ_SMon`. -/
def smonCell : ∀ a : SigEx.SMonTr,
    (smonPreModel C).interp ((smonPreModel C).Pctx a).π (SigEx.smonSig.trsrc a) ⟶
      (smonPreModel C).interp ((smonPreModel C).Pctx a).π (SigEx.smonSig.trtgt a)
  | .assoc =>
    NatTrans.toCatHom₂ {
      app := fun p => (α_ (MonEx.ev C p 0) (MonEx.ev C p 1) (MonEx.ev C p 2)).hom
      naturality := fun _ _ f =>
        associator_naturality (MonEx.evMap C f 0) (MonEx.evMap C f 1) (MonEx.evMap C f 2) }
  | .assocInv =>
    NatTrans.toCatHom₂ {
      app := fun p => (α_ (MonEx.ev C p 0) (MonEx.ev C p 1) (MonEx.ev C p 2)).inv
      naturality := fun _ _ f =>
        associator_inv_naturality (MonEx.evMap C f 0) (MonEx.evMap C f 1) (MonEx.evMap C f 2) }
  | .lunit =>
    NatTrans.toCatHom₂ {
      app := fun p => (λ_ (MonEx.ev C p 0)).hom
      naturality := fun _ _ f => MonEx.lunit_naturality f 0 }
  | .lunitInv =>
    NatTrans.toCatHom₂ {
      app := fun p => (λ_ (MonEx.ev C p 0)).inv
      naturality := fun _ _ f => MonEx.lunit_inv_naturality f 0 }
  | .runit =>
    NatTrans.toCatHom₂ {
      app := fun p => (ρ_ (MonEx.ev C p 0)).hom
      naturality := fun _ _ f => MonEx.runit_naturality f 0 }
  | .runitInv =>
    NatTrans.toCatHom₂ {
      app := fun p => (ρ_ (MonEx.ev C p 0)).inv
      naturality := fun _ _ f => MonEx.runit_inv_naturality f 0 }
  | .sym =>
    NatTrans.toCatHom₂ {
      app := fun p => (β_ (MonEx.ev C p 0) (MonEx.ev C p 1)).hom
      naturality := fun _ _ f =>
        BraidedCategory.braiding_naturality (MonEx.evMap C f 0) (MonEx.evMap C f 1) }

/-- **A symmetric monoidal category is a `Σ_SMon`-model in `CAT`.** -/
def smonModel : Model SigEx.smonSig Cat.{v, u} where
  toPreModel := smonPreModel C
  tr := smonCell C

end SMon

end UlmerBialgebras.Paper.Loc
