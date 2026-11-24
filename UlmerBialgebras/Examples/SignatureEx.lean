module

public import Mathlib.Data.Fin.VecNotation
public import UlmerBialgebras.Syntax.Syntax

/-!
# Examples 3.19: the standard 2-signatures

This file formalises **Examples 3.19** of *A Syntactic Approach to Ulmer's Bialgebras*: the
2-signatures

* `Σ_Cart = (c, □ : cc → c, I : () → c, δ, p₁, p₂, !)` (formalized in
`UlmerBialgebras/Paper/Sec5DefsCart.lean`),
* `Σ_Mon  = (c, □ : cc → c, I : () → c, (x□y)□z ⇄ x□(y□z), x□I ⇄ x ⇆ I□x)`,
* `Σ_SMon = Σ_Mon` together with a symmetry `x□y → y□x`,
* `Σ_Adj  = (c, d, L : c → d, R : d → c, ηˣ : x → R(L x), εʸ : L(R y) → y)`,
* `Σ_Mnd  = (c, T : c → c, µˣ : T(T x) → T x, ηˣ : x → T x)`,
* `Σ_Distr = (c, T, S : c → c, µ_T, η_T, µ_S, η_S, γˣ : S(T x) → T(S x))`.

Each one is an `UlmerBialgebras.TwoSig`; the transformation symbols of a signature are recorded as
an inductive type, and the parallel pair of terms of a transformation symbol is given in the
context `Fin n` of its displayed variables.

A bidirectional arrow `⇄` of the paper is recorded as two transformation symbols, one in each
direction (nothing in Definition 3.3 forces them to be mutually inverse; invertibility is a
property of a particular model).

## Main results

* `UlmerBialgebras.SigEx.monSig`: the 2-signature `Σ_Mon` of Examples 3.19.
* `UlmerBialgebras.SigEx.smonSig`: the 2-signature `Σ_SMon` of Examples 3.19.
* `UlmerBialgebras.SigEx.adjSig`: the 2-signature `Σ_Adj` of Examples 3.19.
* `UlmerBialgebras.SigEx.mndSig`: the 2-signature `Σ_Mnd` of Examples 3.19.
* `UlmerBialgebras.SigEx.distrSig`: the 2-signature `Σ_Distr` of Examples 3.19.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 3.3,
  Examples 3.19
-/

@[expose] public section

namespace UlmerBialgebras

namespace SigEx

/-! ## `Σ_Mon` and `Σ_SMon`: the (symmetric) monoidal signatures -/

/-- The functor symbols of `Σ_Mon`: the tensor and the unit. -/
inductive MonFun | tens | unit
  deriving DecidableEq

/-- The transformation symbols of `Σ_Mon`: the associator and the two unitors, each in both
directions. -/
inductive MonTr | assoc | assocInv | lunit | lunitInv | runit | runitInv
  deriving DecidableEq

/-- The transformation symbols of `Σ_SMon`: those of `Σ_Mon` together with the symmetry. -/
inductive SMonTr | assoc | assocInv | lunit | lunitInv | runit | runitInv | sym
  deriving DecidableEq

/-- The category and functor symbols of `Σ_Mon` (and of `Σ_SMon`). -/
@[reducible] def monFunSig : FunSig where
  Cat := Unit
  Fun := MonFun
  arn := fun B => match B with | .tens => 2 | .unit => 0
  art := fun _ _ => ()
  fcod := fun _ => ()

/-- `a □ b` in `Σ_Mon`. -/
@[reducible] def monTens {V : Type} {vty : V → Unit} (a b : Trm monFunSig vty ()) :
    Trm monFunSig vty () := Trm.app (S := monFunSig) MonFun.tens ![a, b]

/-- The term `I` of `Σ_Mon`. -/
@[reducible] def monUnit {V : Type} {vty : V → Unit} : Trm monFunSig vty () :=
  .app MonFun.unit (fun i => i.elim0)

/-- **The 2-signature `Σ_Mon`.** -/
@[reducible] def monSig : TwoSig where
  toFunSig := monFunSig
  Tr := MonTr
  trn := fun a => match a with
    | .assoc => 3 | .assocInv => 3
    | .lunit => 1 | .lunitInv => 1 | .runit => 1 | .runitInv => 1
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .assoc => monTens (monTens (.var 0) (.var 1)) (.var 2)
    | .assocInv => monTens (.var 0) (monTens (.var 1) (.var 2))
    | .lunit => monTens monUnit (.var 0)
    | .lunitInv => .var 0
    | .runit => monTens (.var 0) monUnit
    | .runitInv => .var 0
  trtgt := fun a => match a with
    | .assoc => monTens (.var 0) (monTens (.var 1) (.var 2))
    | .assocInv => monTens (monTens (.var 0) (.var 1)) (.var 2)
    | .lunit => .var 0
    | .lunitInv => monTens monUnit (.var 0)
    | .runit => .var 0
    | .runitInv => monTens (.var 0) monUnit

/-- **The 2-signature `Σ_SMon`**: `Σ_Mon` with a symmetry `x□y → y□x`. -/
@[reducible] def smonSig : TwoSig where
  toFunSig := monFunSig
  Tr := SMonTr
  trn := fun a => match a with
    | .assoc => 3 | .assocInv => 3
    | .lunit => 1 | .lunitInv => 1 | .runit => 1 | .runitInv => 1
    | .sym => 2
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .assoc => monTens (monTens (.var 0) (.var 1)) (.var 2)
    | .assocInv => monTens (.var 0) (monTens (.var 1) (.var 2))
    | .lunit => monTens monUnit (.var 0)
    | .lunitInv => .var 0
    | .runit => monTens (.var 0) monUnit
    | .runitInv => .var 0
    | .sym => monTens (.var 0) (.var 1)
  trtgt := fun a => match a with
    | .assoc => monTens (.var 0) (monTens (.var 1) (.var 2))
    | .assocInv => monTens (monTens (.var 0) (.var 1)) (.var 2)
    | .lunit => .var 0
    | .lunitInv => monTens monUnit (.var 0)
    | .runit => .var 0
    | .runitInv => monTens (.var 0) monUnit
    | .sym => monTens (.var 1) (.var 0)

/-! ## `Σ_Mnd`: the signature of a monad -/

/-- The functor symbol of `Σ_Mnd`. -/
inductive MndFun | T
  deriving DecidableEq

/-- The transformation symbols of `Σ_Mnd`: the multiplication and the unit. -/
inductive MndTr | mu | eta
  deriving DecidableEq

/-- The category and functor symbols of `Σ_Mnd`. -/
@[reducible] def mndFunSig : FunSig where
  Cat := Unit
  Fun := MndFun
  arn := fun _ => 1
  art := fun _ _ => ()
  fcod := fun _ => ()

/-- The term `T t`. -/
@[reducible] def mndT {V : Type} {vty : V → Unit} (t : Trm mndFunSig vty ()) :
    Trm mndFunSig vty () := .app MndFun.T ![t]

/-- **The 2-signature `Σ_Mnd`.** -/
@[reducible] def mndSig : TwoSig where
  toFunSig := mndFunSig
  Tr := MndTr
  trn := fun _ => 1
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .mu => mndT (mndT (.var 0))
    | .eta => .var 0
  trtgt := fun a => match a with
    | .mu => mndT (.var 0)
    | .eta => mndT (.var 0)

/-! ## `Σ_Adj`: the signature of an adjunction

Only the data: the triangle identities are equations, so they belong to a theory, not to the
signature. -/

/-- The category symbols of `Σ_Adj`. -/
inductive AdjCat | c | d
  deriving DecidableEq

/-- The functor symbols of `Σ_Adj`. -/
inductive AdjFun | L | R
  deriving DecidableEq

/-- The transformation symbols of `Σ_Adj`: the unit and the counit. -/
inductive AdjTr | eta | eps
  deriving DecidableEq

/-- The category and functor symbols of `Σ_Adj`: `L : c → d` and `R : d → c`. -/
@[reducible] def adjFunSig : FunSig where
  Cat := AdjCat
  Fun := AdjFun
  arn := fun _ => 1
  art := fun B _ => match B with
    | .L => .c
    | .R => .d
  fcod := fun B => match B with
    | .L => .d
    | .R => .c

/-- The term `L t` of `Σ_Adj`. -/
@[reducible] def adjL {V : Type} {vty : V → AdjCat} (t : Trm adjFunSig vty .c) :
    Trm adjFunSig vty .d := Trm.app (S := adjFunSig) (vty := vty) AdjFun.L ![t]

/-- The term `R t` of `Σ_Adj`. -/
@[reducible] def adjR {V : Type} {vty : V → AdjCat} (t : Trm adjFunSig vty .d) :
    Trm adjFunSig vty .c := Trm.app (S := adjFunSig) (vty := vty) AdjFun.R ![t]

/-- **The 2-signature `Σ_Adj`**: `ηˣ : x → R(L x)` for `x : c` and `εʸ : L(R y) → y` for
`y : d`. -/
@[reducible] def adjSig : TwoSig where
  toFunSig := adjFunSig
  Tr := AdjTr
  trn := fun _ => 1
  trt := fun a _ => match a with
    | .eta => .c
    | .eps => .d
  trty := fun a => match a with
    | .eta => .c
    | .eps => .d
  trsrc := fun a => match a with
    | .eta => .var 0
    | .eps => adjL (adjR (.var 0))
  trtgt := fun a => match a with
    | .eta => adjR (adjL (.var 0))
    | .eps => .var 0

/-! ## `Σ_Distr`: the signature of a distributive law

Only the data: the monad laws and the laws of a distributive law are equations of a theory. -/

/-- The functor symbols of `Σ_Distr`. -/
inductive DistrFun | T | S
  deriving DecidableEq

/-- The transformation symbols of `Σ_Distr`: the multiplications and units of `T` and `S`, and
`γ`. -/
inductive DistrTr | muT | etaT | muS | etaS | gamma
  deriving DecidableEq

/-- The category and functor symbols of `Σ_Distr`: `T, S : c → c`. -/
@[reducible] def distrFunSig : FunSig where
  Cat := Unit
  Fun := DistrFun
  arn := fun _ => 1
  art := fun _ _ => ()
  fcod := fun _ => ()

/-- The term `T t` of `Σ_Distr`. -/
@[reducible] def distrT {V : Type} {vty : V → Unit} (t : Trm distrFunSig vty ()) :
    Trm distrFunSig vty () := .app DistrFun.T ![t]

/-- The term `S t` of `Σ_Distr`. -/
@[reducible] def distrS {V : Type} {vty : V → Unit} (t : Trm distrFunSig vty ()) :
    Trm distrFunSig vty () := .app DistrFun.S ![t]

/-- **The 2-signature `Σ_Distr`**: `µ_T`, `η_T`, `µ_S`, `η_S` and `γˣ : S(T x) → T(S x)`. -/
@[reducible] def distrSig : TwoSig where
  toFunSig := distrFunSig
  Tr := DistrTr
  trn := fun _ => 1
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .muT => distrT (distrT (.var 0))
    | .etaT => .var 0
    | .muS => distrS (distrS (.var 0))
    | .etaS => .var 0
    | .gamma => distrS (distrT (.var 0))
  trtgt := fun a => match a with
    | .muT => distrT (.var 0)
    | .etaT => distrT (.var 0)
    | .muS => distrS (.var 0)
    | .etaS => distrS (.var 0)
    | .gamma => distrT (distrS (.var 0))

end SigEx

end UlmerBialgebras
