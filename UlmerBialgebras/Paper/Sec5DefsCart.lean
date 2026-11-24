module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Examples.SignatureEx
public import UlmerBialgebras.Examples.MonModel
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.Tactic.DeriveCountable
public import Foundations.CategoryTheory.Monoidal.Cartesian.Diagonal

/-!
# The cartesian 2-signature and cartesian categorical models

Examples 3.19 (the 2-signature `Σ_Cart`) and Corollary 5.9 of
*A Syntactic Approach to Ulmer's Bialgebras* [forsman2026syntactic]:
* `UlmerBialgebras.Paper.Cart.sigCart`: the 2-signature
  `Σ_Cart = (c, □ : cc → c, I : () → c, δ, p₁, p₂, !)`
* `UlmerBialgebras.Paper.Cart.cartPreModel C`: interpretation of the functor symbols in a cartesian
  category `C`
* `UlmerBialgebras.Paper.Cart.cartModel C`: `C` as a `Σ_Cart`-model in `CAT`.

## Main results

* `UlmerBialgebras.Paper.Cart.sigCart`: the 2-signature `Σ_Cart` (Examples 3.19).
* `UlmerBialgebras.Paper.Cart.cartPreModel`: the interpretation of the category and functor symbols
  of `Σ_Cart` in a cartesian category `C`.
* `UlmerBialgebras.Paper.Cart.cartModel`: a cartesian category `C` as a `Σ_Cart`-model in `CAT`
  (used in Corollary 5.9).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19, Corollary 5.9
-/

@[expose] public section

universe v u uᵥ

namespace UlmerBialgebras.Paper.Cart

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

/-- The functor symbols of `Σ_Cart`: binary product `□` and terminal object `I`. -/
inductive CartFun | tens | unit
  deriving DecidableEq, Countable

/-- The transformation symbols of `Σ_Cart`: diagonal, projections, and terminal map. -/
inductive CartTr | diag | proj₁ | proj₂ | term
  deriving DecidableEq, Countable

/-- The category and functor symbols of `Σ_Cart`. -/
@[reducible] def cartFunSig : FunSig where
  Cat := Unit
  Fun := CartFun
  arn := fun | .tens => 2 | .unit => 0
  art := fun _ _ => ()
  fcod := fun _ => ()

/-- `a □ b` in `Σ_Cart`. -/
@[reducible] def cartTens {V : Type uᵥ} {vty : V → Unit} (a b : Trm cartFunSig vty ()) :
    Trm cartFunSig vty () := Trm.app (S := cartFunSig) CartFun.tens ![a, b]

/-- The term `I` of `Σ_Cart`. -/
@[reducible] def cartUnit {V : Type uᵥ} {vty : V → Unit} : Trm cartFunSig vty () :=
  .app CartFun.unit (fun i => i.elim0)

/-- **The 2-signature `Σ_Cart`** (Examples 3.19 of [forsman2026syntactic]). -/
@[reducible] def sigCart : TwoSig where
  toFunSig := cartFunSig
  Tr := CartTr
  trn := fun | .diag => 1 | .proj₁ => 2 | .proj₂ => 2 | .term => 1
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun
    | .diag => .var 0
    | .proj₁ => cartTens (.var 0) (.var 1)
    | .proj₂ => cartTens (.var 0) (.var 1)
    | .term => .var 0
  trtgt := fun
    | .diag => cartTens (.var 0) (.var 0)
    | .proj₁ => .var 0
    | .proj₂ => .var 1
    | .term => cartUnit

section Model

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

/-- The interpretation of the category and functor symbols of `Σ_Cart` in a cartesian category. -/
def cartPreModel : PreModel sigCart Cat.{v, u} where
  obj := fun _ => Cat.of C
  fn := fun B => match B with
    | .tens => (MonEx.tensFunctor C).toCatHom
    | .unit => (MonEx.unitFunctor C).toCatHom

/-- The interpretation of the transformation symbols of `Σ_Cart` in a cartesian category. -/
def cartCell : ∀ a : CartTr,
    (cartPreModel C).interp ((cartPreModel C).Pctx a).π (sigCart.trsrc a) ⟶
      (cartPreModel C).interp ((cartPreModel C).Pctx a).π (sigCart.trtgt a)
  | .diag => { toNatTrans := {
      app := fun p => lift (C := C) (𝟙 (MonEx.ev C p 0)) (𝟙 (MonEx.ev C p 0))
      naturality := fun _ _ f => lift_id_id_naturality (MonEx.evMap C f 0)
    } }
  | .proj₁ => { toNatTrans := {
      app := fun p => fst (C := C) (MonEx.ev C p 0) (MonEx.ev C p 1)
      naturality := fun _ _ f => tensorHom_fst (MonEx.evMap C f 0) (MonEx.evMap C f 1)
    } }
  | .proj₂ => { toNatTrans := {
      app := fun p => snd (C := C) (MonEx.ev C p 0) (MonEx.ev C p 1)
      naturality := fun _ _ f => tensorHom_snd (MonEx.evMap C f 0) (MonEx.evMap C f 1)
    } }
  | .term => { toNatTrans := {
      app := fun p => toUnit (C := C) (MonEx.ev C p 0)
      naturality := fun _ _ f =>
        (comp_toUnit (MonEx.evMap C f 0)).trans (Category.comp_id _).symm
    } }

/-- **A cartesian category is a `Σ_Cart`-model in `CAT`.** -/
def cartModel : Model sigCart Cat.{v, u} where
  toPreModel := cartPreModel C
  tr := cartCell C

end Model

end UlmerBialgebras.Paper.Cart
