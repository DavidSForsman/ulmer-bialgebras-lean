module

public import UlmerBialgebras.Examples.SignatureEx
public import UlmerBialgebras.Examples.MonCalc
public import UlmerBialgebras.Kan.KanModel
public import UlmerBialgebras.Kan.ColimKan
public import UlmerBialgebras.Kan.LimKan
public import Foundations.CategoryTheory.Limits.PiColimits
public import Foundations.CategoryTheory.Limits.OpTranslate

/-!
# The theory of monad algebras, and Corollary 4.13

The Eilenberg–Moore category of a monad `T` on a category `C` is the object of bialgebras of
the signature pair

* `Σ = Σ_Mnd = (c, T : c → c, µˣ : T(T x) → T x, ηˣ : x → T x)` (Examples 3.19),
* `σ_Mnd = (s : c, a : T(s) → s)`,
* `T_Mnd` : the two parallel pairs `a ∘ µ_s = a ∘ T(a) : T(T s) → s` and `a ∘ η_s = 1_s`.

The theory is algebraic.  For a monad `T` on `C`, viewed as a `Σ_Mnd`-model in `CAT`
(`UlmerBialgebras.MndEx.model`), the object of `T_Mnd`-bialgebras is the Eilenberg–Moore category,
and Corollary 4.11 specialises to **Corollary 4.13**: the forgetful functor `C^T → C` strictly
creates all limits, and those colimits which `T` preserves and whose quotient initiality `T²`
preserves.  This file only constructs the model; the identification with the Eilenberg–Moore
category and the specialisation of Corollary 4.11 are not formalized in it.

## Main results

* `UlmerBialgebras.MndEx.model`: a monad on `C` is a `Σ_Mnd`-model in `CAT`, for the 2-signature
  `Σ_Mnd` of Examples 3.19.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.19,
  Corollary 4.11, Corollary 4.13
-/

@[expose] public section


universe v u

namespace UlmerBialgebras

open CategoryTheory Limits SigEx

namespace MndEx

/-! ## A monad as a `Σ_Mnd`-model -/

variable {C : Type u} [Category.{v} C] (T : Monad C)

/-- The endofunctor of the monad, as a functor on the one-fold product. -/
@[reducible] def tFunctor : (∀ _ : Fin 1, C) ⥤ C := Pi.eval (fun _ : Fin 1 => C) 0 ⋙ (T : C ⥤ C)

/-- The interpretation of the category and functor symbols of `Σ_Mnd`. -/
def preModel : PreModel mndSig Cat.{v, u} where
  obj := fun _ => Cat.of C
  fn := fun B => match B with | .T => (tFunctor T).toCatHom

/-- Reading off the unique component of an environment. -/
@[reducible] def ev (p : ∀ _ : Fin 1, (Cat.of C : Type u)) : C := p 0

/-- The multiplication of the monad, as the interpretation of `µ`. -/
def muCell :
    (preModel T).interp ((preModel T).Pctx MndTr.mu).π (mndSig.trsrc MndTr.mu) ⟶
      (preModel T).interp ((preModel T).Pctx MndTr.mu).π (mndSig.trtgt MndTr.mu) where
  toNatTrans := {
    app p := T.μ.app (ev (C := C) p)
    naturality _ _ f := T.μ.naturality (f 0) }

/-- The unit of the monad, as the interpretation of `η`. -/
def etaCell :
    (preModel T).interp ((preModel T).Pctx MndTr.eta).π (mndSig.trsrc MndTr.eta) ⟶
      (preModel T).interp ((preModel T).Pctx MndTr.eta).π (mndSig.trtgt MndTr.eta) where
  toNatTrans := {
    app p := T.η.app (ev (C := C) p)
    naturality _ _ f := T.η.naturality (f 0) }

/-- **A monad is a `Σ_Mnd`-model in `CAT`.** -/
def model : Model mndSig Cat.{v, u} where
  toPreModel := preModel T
  tr := fun a => match a with
    | .mu => muCell T
    | .eta => etaCell T

/-- Evaluating the functor symbol `T` of `MndEx.model` on an object family applies `T` to index `0`.
-/
lemma model_fn_T_obj
    (X : ∀ i : Fin (mndSig.arn MndFun.T), ((model T).obj (mndSig.art MndFun.T i) : Type u)) :
    ((model T).fn MndFun.T).toFunctor.obj X = (T : C ⥤ C).obj (X 0 : C) := rfl

/-- Evaluating the functor symbol `T` of `MndEx.model` on a morphism family applies `T.map` to
index `0`. -/
lemma model_fn_T_map
    {X Y : ∀ i : Fin (mndSig.arn MndFun.T), ((model T).obj (mndSig.art MndFun.T i) : Type u)}
    (f : X ⟶ Y) :
    ((model T).fn MndFun.T).toFunctor.map f = (T : C ⥤ C).map (f 0 : (X 0 : C) ⟶ (Y 0 : C)) := rfl

/-- Evaluating the `mu` transformation cell of `MndEx.model` at an environment `p` gives `T.μ`. -/
lemma model_tr_mu_app (p : ((model T).Pctx MndTr.mu).pt) :
    ((model T).tr MndTr.mu).toNatTrans.app p = T.μ.app (p 0 : C) := rfl

/-- Evaluating the `eta` transformation cell of `MndEx.model` at an environment `p` gives `T.η`. -/
lemma model_tr_eta_app (p : ((model T).Pctx MndTr.eta).pt) :
    ((model T).tr MndTr.eta).toNatTrans.app p = T.η.app (p 0 : C) := rfl

/-! ## `M^σ` is the category of `T`-algebra data -/

variable {T}

/-! ## The defining condition of `M^T` -/

/-! ## `M^T` is the Eilenberg–Moore category -/

/-! ## Corollary 4.11 -/

variable (T)

end MndEx

end UlmerBialgebras
