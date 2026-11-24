module

public import Mathlib.Tactic.FinCases
public import UlmerBialgebras.Models.Bialgebra

/-!
# The signature pair and theory of monoids

This file formalises the syntactic half of Examples 3.20 (1) of *A Syntactic Approach to
Ulmer's Bialgebras*: the 2-signature

`Σ = (c, □ : cc → c, I : () → c, (x□y)□z → x□(y□z), x□I → x, I□x → x)`,

the relative 1-signature `σ = (s : c, µ : s□s → s, u : I → s)` and the σ-theory `T` of
monoids, given by the three parallel paths of the term graph

* `(s□s)□s → s□s → s` versus `(s□s)□s → s□(s□s) → s□s → s` (associativity),
* `s□I → s□s → s` versus `s□I → s` (right unit),
* `I□s → s□s → s` versus `I□s → s` (left unit).

The theory is *algebraic* (its coarity terms are sorts), so Corollary 3.23 (1) applies to
it; this verification is not formalized in this file.

The three instances of transformation symbols occurring in the theory are substitution
instances of the associator and the unitors at the sort `s`; since substitution does not
commute definitionally with the `Fin`-indexed argument vectors used to build terms, these
arrows are obtained by transporting along the (propositional) equalities
`substTrsrc_assoc`, … below.

## Main results

* `UlmerBialgebras.MonEx.twoSig`: the 2-signature `Σ_Mon`.
* `UlmerBialgebras.MonEx.oneSig`: the relative 1-signature
  `σ_Mon = (s : c, µ : s□s → s, u : I → s)`.
* `UlmerBialgebras.MonEx.monTheory`: the theory `T_Mon` of monoids (Examples 3.20 (1)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (1)
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂

namespace UlmerBialgebras

open CategoryTheory in
/-- The evaluation of a transported arrow. -/
lemma Model.arrCell_transport {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    [HasChosenFinProducts Obj] {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Obj)
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Obj]
    [HasChosenProductsOfSize.{s₂} Obj] [HasChosenInserters Obj]
    {c : Sg.Cat} {t₁ t₂ t₁' t₂' : sg.CTrm c} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂')
    (g : sg.Arr t₁ t₂) :
    M.arrCell sg (g.transport h₁ h₂) =
      eqToHom (by rw [h₁]) ≫ M.arrCell sg g ≫ eqToHom (by rw [h₂]) := by
  subst h₁; subst h₂; simp [OneSig.Arr.transport]

namespace MonEx

/-- The functor symbols: the tensor `□` and the unit `I`. -/
inductive FunSym | tens | unit
  deriving DecidableEq

/-- The transformation symbols: the associator and the two unitors. -/
inductive TrSym | assoc | lunit | runit
  deriving DecidableEq

/-- The function symbols of `σ`: the multiplication and the unit of the monoid. -/
inductive FnSym | mul | one
  deriving DecidableEq

/-- The three equations of the theory of monoids. -/
inductive EqnSym | assoc | mulOne | oneMul
  deriving DecidableEq

/-- The category and functor symbols of `Σ_Mon`: one category symbol, a binary functor
symbol `□` and a nullary functor symbol `I`. -/
@[reducible] def funSig : FunSig where
  Cat := Unit
  Fun := FunSym
  arn := fun B => match B with | .tens => 2 | .unit => 0
  art := fun _ _ => ()
  fcod := fun _ => ()

/-- Terms of the monoidal signature (there is only one category symbol). -/
abbrev Tm {V : Type} (vty : V → Unit) := Trm funSig vty ()

/-- The term `a □ b`. -/
@[reducible] def tens {V : Type} {vty : V → Unit} (a b : Tm vty) : Tm vty :=
  Trm.app (S := funSig) FunSym.tens ![a, b]

/-- The term `I`. -/
@[reducible] def unitT {V : Type} {vty : V → Unit} : Tm vty := .app FunSym.unit (fun i => i.elim0)
/-- Substitution into a variable `v` returns `sub v`. -/
@[simp] lemma subst_var {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) (v : V) :
    (Trm.var v : Trm funSig vty (vty v)).subst sub = sub v := rfl


/-- Substitution commutes with the term `a □ b`. -/
@[simp] lemma subst_tens {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) (a b : Tm vty) :
    (tens a b).subst sub = tens (a.subst sub) (b.subst sub) := by
  rw [Trm.subst]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Substitution fixes the term `I`. -/
@[simp] lemma subst_unitT {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) :
    (unitT (vty := vty)).subst sub = unitT := by
  rw [Trm.subst]
  congr 1
  funext i
  exact i.elim0

/-- The 2-signature `Σ_Mon`. -/
@[reducible] def twoSig : TwoSig where
  toFunSig := funSig
  Tr := TrSym
  trn := fun a => match a with | .assoc => 3 | .lunit => 1 | .runit => 1
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .assoc => tens (tens (.var 0) (.var 1)) (.var 2)
    | .lunit => tens unitT (.var 0)
    | .runit => tens (.var 0) unitT
  trtgt := fun a => match a with
    | .assoc => tens (.var 0) (tens (.var 1) (.var 2))
    | .lunit => .var 0
    | .runit => .var 0

/-- The term consisting of the unique sort `s`. -/
@[reducible] def sTm : Trm funSig (fun _ : Unit => ()) () := .var ()

/-- The relative 1-signature `σ_Mon = (s : c, µ : s□s → s, u : I → s)`. -/
@[reducible] def oneSig : OneSig twoSig where
  Srt := Unit
  sty := fun _ => ()
  Fn := FnSym
  fnty := fun _ => ()
  fndom := fun f => match f with | .mul => tens sTm sTm | .one => unitT
  fncod := fun _ => sTm

/-! ## The arrows of the term graph used by the theory of monoids -/

/-- The substitution of the sort `s` for all the variables of a transformation symbol. -/
abbrev subS (a : TrSym) : ∀ i : Fin (twoSig.trn a), oneSig.CTrm (twoSig.trt a i) :=
  fun _ => sTm

/-- The source of the associator symbol, with `s` for every variable, is `(s□s)□s`. -/
lemma substTrsrc_assoc :
    (twoSig.trsrc TrSym.assoc).subst (subS TrSym.assoc) = tens (tens sTm sTm) sTm := by
  simp [twoSig]

/-- The target of the associator symbol, with `s` for every variable, is `s□(s□s)`. -/
lemma substTrtgt_assoc :
    (twoSig.trtgt TrSym.assoc).subst (subS TrSym.assoc) = tens sTm (tens sTm sTm) := by
  simp [twoSig]

/-- The source of the right unitor symbol, with `s` for its variable, is `s□I`. -/
lemma substTrsrc_runit :
    (twoSig.trsrc TrSym.runit).subst (subS TrSym.runit) = tens sTm unitT := by
  simp [twoSig]

/-- The target of the right unitor symbol, with `s` for its variable, is `s`. -/
lemma substTrtgt_runit : (twoSig.trtgt TrSym.runit).subst (subS TrSym.runit) = sTm := rfl

/-- The source of the left unitor symbol, with `s` for its variable, is `I□s`. -/
lemma substTrsrc_lunit :
    (twoSig.trsrc TrSym.lunit).subst (subS TrSym.lunit) = tens unitT sTm := by
  simp [twoSig]

/-- The target of the left unitor symbol, with `s` for its variable, is `s`. -/
lemma substTrtgt_lunit : (twoSig.trtgt TrSym.lunit).subst (subS TrSym.lunit) = sTm := rfl

/-- The instance `α_{s,s,s}` of the associator. -/
def assocArr : oneSig.Arr (tens (tens sTm sTm) sTm) (tens sTm (tens sTm sTm)) :=
  OneSig.Arr.transport substTrsrc_assoc substTrtgt_assoc
    (OneSig.Arr.tr (sg := oneSig) TrSym.assoc (subS TrSym.assoc))

/-- The instance `ρ_s` of the right unitor. -/
def runitArr : oneSig.Arr (tens sTm unitT) sTm :=
  OneSig.Arr.transport substTrsrc_runit substTrtgt_runit
    (OneSig.Arr.tr (sg := oneSig) TrSym.runit (subS TrSym.runit))

/-- The instance `λ_s` of the left unitor. -/
def lunitArr : oneSig.Arr (tens unitT sTm) sTm :=
  OneSig.Arr.transport substTrsrc_lunit substTrtgt_lunit
    (OneSig.Arr.tr (sg := oneSig) TrSym.lunit (subS TrSym.lunit))

/-- The arrow `µ□s : (s□s)□s → s□s`. -/
def mulTensS : oneSig.Arr (tens (tens sTm sTm) sTm) (tens sTm sTm) :=
  OneSig.Arr.app (sg := oneSig) FunSym.tens 0 ![tens sTm sTm, sTm] ![sTm, sTm]
    (fun j hj => by fin_cases j <;> simp_all) (OneSig.Arr.fn (sg := oneSig) FnSym.mul)

/-- The arrow `s□µ : s□(s□s) → s□s`. -/
def sTensMul : oneSig.Arr (tens sTm (tens sTm sTm)) (tens sTm sTm) :=
  OneSig.Arr.app (sg := oneSig) FunSym.tens 1 ![sTm, tens sTm sTm] ![sTm, sTm]
    (fun j hj => by fin_cases j <;> simp_all) (OneSig.Arr.fn (sg := oneSig) FnSym.mul)

/-- The arrow `s□u : s□I → s□s`. -/
def sTensOne : oneSig.Arr (tens sTm unitT) (tens sTm sTm) :=
  OneSig.Arr.app (sg := oneSig) FunSym.tens 1 ![sTm, unitT] ![sTm, sTm]
    (fun j hj => by fin_cases j <;> simp_all) (OneSig.Arr.fn (sg := oneSig) FnSym.one)

/-- The arrow `u□s : I□s → s□s`. -/
def oneTensS : oneSig.Arr (tens unitT sTm) (tens sTm sTm) :=
  OneSig.Arr.app (sg := oneSig) FunSym.tens 0 ![unitT, sTm] ![sTm, sTm]
    (fun j hj => by fin_cases j <;> simp_all) (OneSig.Arr.fn (sg := oneSig) FnSym.one)

/-! ## The theory of monoids -/

/-- The theory `T_Mon` of monoids: associativity and the two unit laws. -/
def monTheory : Theory oneSig where
  Eqn := EqnSym
  eqty := fun _ => ()
  dom := fun r => match r with
    | .assoc => tens (tens sTm sTm) sTm
    | .mulOne => tens sTm unitT
    | .oneMul => tens unitT sTm
  cod := fun _ => sTm
  lhs := fun r => match r with
    | .assoc => .cons mulTensS (.cons (OneSig.Arr.fn (sg := oneSig) FnSym.mul) (.nil _))
    | .mulOne => .cons sTensOne (.cons (OneSig.Arr.fn (sg := oneSig) FnSym.mul) (.nil _))
    | .oneMul => .cons oneTensS (.cons (OneSig.Arr.fn (sg := oneSig) FnSym.mul) (.nil _))
  rhs := fun r => match r with
    | .assoc => .cons assocArr
        (.cons sTensMul (.cons (OneSig.Arr.fn (sg := oneSig) FnSym.mul) (.nil _)))
    | .mulOne => .cons runitArr (.nil _)
    | .oneMul => .cons lunitArr (.nil _)

end MonEx

end UlmerBialgebras
