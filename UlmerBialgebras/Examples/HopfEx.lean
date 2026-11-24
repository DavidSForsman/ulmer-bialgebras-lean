module

public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import UlmerBialgebras.Syntax.PathOps

/-!
# Examples 3.20 (2): the signature pair and theory of Hopf algebras

This file formalises the syntactic half of **Examples 3.20 (2)** of *A Syntactic Approach to
Ulmer's Bialgebras*: the skew-monoidal 2-signature with an interchange law

`Σ = (c, □ : cc → c, I : () → c, αˣʸᶻ : (x□y)□z → x□(y□z), λˣ : I□x → x, ρˣ : x → x□I,
      χˣʸᶻᵛ : (x□y)□(z□v) → (x□z)□(y□v))`,

the relative 1-signature

`σ_Hopf = (s : c, µ : s□s → s, u : I → s, δ : s → s□s, ε : s → I, S : s → s)`,

and the theory `T_Hopf`, whose twelve equations are the parallel pairs of paths of the term
graph displayed as commutative diagrams in the paper: associativity and the two unit laws
for `µ`, coassociativity and the two counit laws for `δ`, the four bialgebra compatibilities
between `(µ, u)` and `(δ, ε)`, and the two antipode axioms.

The theory is neither algebraic nor coalgebraic (this is not formalized here), which is
exactly the situation in which Corollary 3.23 (3) — the strong case of Theorem 3.22 — is needed.

## Main results

* `UlmerBialgebras.HopfEx.twoSig`: the skew-monoidal 2-signature with an interchange law.
* `UlmerBialgebras.HopfEx.oneSig`: the relative 1-signature `σ_Hopf`.
* `UlmerBialgebras.HopfEx.theory`: the theory `T_Hopf` of internal Hopf algebras (Examples 3.20
  (2)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (2), Theorem 3.22 and Corollary 3.23
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
* [A. Joyal, R. Street, *Braided tensor categories*][joyalBraidedTensorCategories1993]
* [R. Street, *Quantum Groups: A Path to Current Algebra*][streetQuantumGroupsPath2007]
-/

@[expose] public section

namespace UlmerBialgebras

namespace HopfEx

/-- The functor symbols: the tensor `□` and the unit `I`. -/
inductive FunSym | tens | unit
  deriving DecidableEq

/-- The transformation symbols: the associator, the two unitors and the interchange law. -/
inductive TrSym | assoc | lunit | runit | chi
  deriving DecidableEq

/-- The function symbols of `σ_Hopf`. -/
inductive FnSym | mul | one | comul | counit | antipode
  deriving DecidableEq

/-- The equations of `T_Hopf`. -/
inductive EqnSym
  | assoc | lunit | runit
  | coassoc | lcounit | rcounit
  | bialg | counitMul | unitComul | counitUnit
  | antipodeLeft | antipodeRight
  deriving DecidableEq

/-- The category and functor symbols of `Σ`. -/
@[reducible] def funSig : FunSig where
  Cat := Unit
  Fun := FunSym
  arn := fun B => match B with | .tens => 2 | .unit => 0
  art := fun _ _ => ()
  fcod := fun _ => ()

/-- Terms of the signature. -/
abbrev Tm {V : Type} (vty : V → Unit) := Trm funSig vty ()

/-- The term `a □ b`. -/
@[reducible] def tn {V : Type} {vty : V → Unit} (a b : Tm vty) : Tm vty :=
  Trm.app (S := funSig) FunSym.tens ![a, b]

/-- The term `I`. -/
@[reducible] def un {V : Type} {vty : V → Unit} : Tm vty :=
  .app FunSym.unit (fun i => i.elim0)
/-- Substitution into a variable `v` returns `sub v`. -/
@[simp] lemma subst_var {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) (v : V) :
    (Trm.var v : Trm funSig vty (vty v)).subst sub = sub v := rfl


/-- Substitution commutes with the term `a □ b`. -/
@[simp] lemma subst_tn {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) (a b : Tm vty) :
    (tn a b).subst sub = tn (a.subst sub) (b.subst sub) := by
  rw [Trm.subst]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Substitution fixes the term `I`. -/
@[simp] lemma subst_un {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) : (un (vty := vty)).subst sub = un := by
  rw [Trm.subst]
  congr 1
  funext i
  exact i.elim0

/-- **The skew-monoidal 2-signature with an interchange law.** -/
@[reducible] def twoSig : TwoSig where
  toFunSig := funSig
  Tr := TrSym
  trn := fun a => match a with | .assoc => 3 | .lunit => 1 | .runit => 1 | .chi => 4
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .assoc => tn (tn (.var 0) (.var 1)) (.var 2)
    | .lunit => tn un (.var 0)
    | .runit => .var 0
    | .chi => tn (tn (.var 0) (.var 1)) (tn (.var 2) (.var 3))
  trtgt := fun a => match a with
    | .assoc => tn (.var 0) (tn (.var 1) (.var 2))
    | .lunit => .var 0
    | .runit => tn (.var 0) un
    | .chi => tn (tn (.var 0) (.var 2)) (tn (.var 1) (.var 3))

/-- The sort `s`. -/
@[reducible] def sTm : Trm funSig (fun _ : Unit => ()) () := .var ()

/-- **The relative 1-signature `σ_Hopf`.** -/
@[reducible] def oneSig : OneSig twoSig where
  Srt := Unit
  sty := fun _ => ()
  Fn := FnSym
  fnty := fun _ => ()
  fndom := fun f => match f with
    | .mul => tn sTm sTm
    | .one => un
    | .comul => sTm
    | .counit => sTm
    | .antipode => sTm
  fncod := fun f => match f with
    | .mul => sTm
    | .one => sTm
    | .comul => tn sTm sTm
    | .counit => un
    | .antipode => sTm

/-! ## Arrows and paths of the term graph -/

/-- Closed terms over the sort of `σ_Hopf`. -/
abbrev CTm : Type := oneSig.CTrm ()

/-- The image `g □ b` of an arrow in the left slot of `□`. -/
def leftArr {a a' : CTm} (b : CTm) (g : oneSig.Arr a a') : oneSig.Arr (tn a b) (tn a' b) :=
  OneSig.Arr.app (sg := oneSig) FunSym.tens 0 ![a, b] ![a', b]
    (fun j hj => by fin_cases j <;> simp_all) g

/-- The image `a □ g` of an arrow in the right slot of `□`. -/
def rightArr (a : CTm) {b b' : CTm} (g : oneSig.Arr b b') : oneSig.Arr (tn a b) (tn a b') :=
  OneSig.Arr.app (sg := oneSig) FunSym.tens 1 ![a, b] ![a, b']
    (fun j hj => by fin_cases j <;> simp_all) g

/-- A single arrow, as a path. -/
def arrPath {t t' : CTm} (g : oneSig.Arr t t') : oneSig.Path t t' := .cons g (.nil _)

/-- The image `p □ b` of a path in the left slot of `□`. -/
def leftPath (b : CTm) :
    ∀ {a t : CTm}, oneSig.Path a t → oneSig.Path (tn a b) (tn t b)
  | _, _, .nil _ => .nil _
  | _, _, .cons g p => .cons (leftArr b g) (leftPath b p)

/-- The image `a □ p` of a path in the right slot of `□`. -/
def rightPath (a : CTm) : ∀ {b t : CTm}, oneSig.Path b t → oneSig.Path (tn a b) (tn a t)
  | _, _, .nil _ => .nil _
  | _, _, .cons g p => .cons (rightArr a g) (rightPath a p)

/-- The image `p □ q` of a pair of paths: it changes the left slot first
(`leftPath b p ≫ rightPath a' q`). The footnote of Examples 3.20 (2) of the paper changes the right
slot first; both give the same 2-cell in every model. -/
def tensPath {a a' b b' : CTm} (p : oneSig.Path a a') (q : oneSig.Path b b') :
    oneSig.Path (tn a b) (tn a' b') :=
  OneSig.Path.comp (leftPath b p) (rightPath a' q)

/-- The arrow attached to a function symbol. -/
def fnArr (f : FnSym) : oneSig.Arr (oneSig.fndom f) (oneSig.fncod f) :=
  OneSig.Arr.fn (sg := oneSig) f

/-! ### Instances of the transformation symbols -/

/-- The source of the associator symbol, instantiated at `t₁, t₂, t₃`, is `(t₁ □ t₂) □ t₃`. -/
lemma subst_assoc_src (t₁ t₂ t₃ : CTm) :
    (twoSig.trsrc TrSym.assoc).subst ![t₁, t₂, t₃] = tn (tn t₁ t₂) t₃ := by
  simp [twoSig]

/-- The target of the associator symbol, instantiated at `t₁, t₂, t₃`, is `t₁ □ (t₂ □ t₃)`. -/
lemma subst_assoc_tgt (t₁ t₂ t₃ : CTm) :
    (twoSig.trtgt TrSym.assoc).subst ![t₁, t₂, t₃] = tn t₁ (tn t₂ t₃) := by
  simp [twoSig]

/-- The source of the left unitor symbol, instantiated at `t`, is `I □ t`. -/
lemma subst_lunit_src (t : CTm) :
    (twoSig.trsrc TrSym.lunit).subst ![t] = tn un t := by
  simp [twoSig]

/-- The target of the left unitor symbol, instantiated at `t`, is `t`. -/
lemma subst_lunit_tgt (t : CTm) : (twoSig.trtgt TrSym.lunit).subst ![t] = t := rfl

/-- The source of the right unitor symbol, instantiated at `t`, is `t`. -/
lemma subst_runit_src (t : CTm) : (twoSig.trsrc TrSym.runit).subst ![t] = t := rfl

/-- The target of the right unitor symbol, instantiated at `t`, is `t □ I`. -/
lemma subst_runit_tgt (t : CTm) :
    (twoSig.trtgt TrSym.runit).subst ![t] = tn t un := by
  simp [twoSig]

/-- The source of the interchange symbol, instantiated at `t₁, t₂, t₃, t₄`, is
`(t₁ □ t₂) □ (t₃ □ t₄)`. -/
lemma subst_chi_src (t₁ t₂ t₃ t₄ : CTm) :
    (twoSig.trsrc TrSym.chi).subst ![t₁, t₂, t₃, t₄] = tn (tn t₁ t₂) (tn t₃ t₄) := by
  simp [twoSig]

/-- The target of the interchange symbol, instantiated at `t₁, t₂, t₃, t₄`, is
`(t₁ □ t₃) □ (t₂ □ t₄)`. -/
lemma subst_chi_tgt (t₁ t₂ t₃ t₄ : CTm) :
    (twoSig.trtgt TrSym.chi).subst ![t₁, t₂, t₃, t₄] = tn (tn t₁ t₃) (tn t₂ t₄) := by
  simp [twoSig]

/-- The instance `α_{t₁,t₂,t₃}` of the associator. -/
def assocArr (t₁ t₂ t₃ : CTm) : oneSig.Arr (tn (tn t₁ t₂) t₃) (tn t₁ (tn t₂ t₃)) :=
  OneSig.Arr.transport (subst_assoc_src t₁ t₂ t₃) (subst_assoc_tgt t₁ t₂ t₃)
    (OneSig.Arr.tr (sg := oneSig) TrSym.assoc ![t₁, t₂, t₃])

/-- The instance `λ_t` of the left unitor. -/
def lunitArr (t : CTm) : oneSig.Arr (tn un t) t :=
  OneSig.Arr.transport (subst_lunit_src t) (subst_lunit_tgt t)
    (OneSig.Arr.tr (sg := oneSig) TrSym.lunit ![t])

/-- The instance `ρ_t` of the right unitor. -/
def runitArr (t : CTm) : oneSig.Arr t (tn t un) :=
  OneSig.Arr.transport (subst_runit_src t) (subst_runit_tgt t)
    (OneSig.Arr.tr (sg := oneSig) TrSym.runit ![t])

/-- The instance `χ_{t₁,t₂,t₃,t₄}` of the interchange law. -/
def chiArr (t₁ t₂ t₃ t₄ : CTm) :
    oneSig.Arr (tn (tn t₁ t₂) (tn t₃ t₄)) (tn (tn t₁ t₃) (tn t₂ t₄)) :=
  OneSig.Arr.transport (subst_chi_src t₁ t₂ t₃ t₄) (subst_chi_tgt t₁ t₂ t₃ t₄)
    (OneSig.Arr.tr (sg := oneSig) TrSym.chi ![t₁, t₂, t₃, t₄])

/-! ## The theory of Hopf algebras -/

/-- `µ`, as a path. -/
def mulP : oneSig.Path (tn sTm sTm) sTm := arrPath (fnArr FnSym.mul)

/-- `u`, as a path. -/
def oneP : oneSig.Path un sTm := arrPath (fnArr FnSym.one)

/-- `δ`, as a path. -/
def comulP : oneSig.Path sTm (tn sTm sTm) := arrPath (fnArr FnSym.comul)

/-- `ε`, as a path. -/
def counitP : oneSig.Path sTm un := arrPath (fnArr FnSym.counit)

/-- `S`, as a path. -/
def antipodeP : oneSig.Path sTm sTm := arrPath (fnArr FnSym.antipode)

open OneSig.Path in
/-- **The theory `T_Hopf` of internal Hopf algebras.** -/
def theory : Theory oneSig where
  Eqn := EqnSym
  eqty := fun _ => ()
  dom := fun r => match r with
    | .assoc => tn (tn sTm sTm) sTm
    | .lunit => tn un sTm
    | .runit => sTm
    | .coassoc => sTm
    | .lcounit => sTm
    | .rcounit => sTm
    | .bialg => tn sTm sTm
    | .counitMul => tn sTm sTm
    | .unitComul => un
    | .counitUnit => un
    | .antipodeLeft => sTm
    | .antipodeRight => sTm
  cod := fun r => match r with
    | .assoc => sTm
    | .lunit => sTm
    | .runit => sTm
    | .coassoc => tn sTm (tn sTm sTm)
    | .lcounit => sTm
    | .rcounit => tn sTm un
    | .bialg => tn sTm sTm
    | .counitMul => un
    | .unitComul => tn sTm sTm
    | .counitUnit => un
    | .antipodeLeft => sTm
    | .antipodeRight => sTm
  lhs := fun r => match r with
    | .assoc => comp (leftPath sTm mulP) mulP
    | .lunit => comp (leftPath sTm oneP) mulP
    | .runit => comp (arrPath (runitArr sTm)) (comp (rightPath sTm oneP) mulP)
    | .coassoc =>
        comp comulP (comp (leftPath sTm comulP) (arrPath (assocArr sTm sTm sTm)))
    | .lcounit => comp comulP (comp (leftPath sTm counitP) (arrPath (lunitArr sTm)))
    | .rcounit => comp comulP (rightPath sTm counitP)
    | .bialg =>
        comp (tensPath comulP comulP)
          (comp (arrPath (chiArr sTm sTm sTm sTm)) (tensPath mulP mulP))
    | .counitMul => comp (tensPath counitP counitP) (arrPath (lunitArr un))
    | .unitComul => comp (arrPath (runitArr un)) (tensPath oneP oneP)
    | .counitUnit => comp oneP counitP
    | .antipodeLeft => comp comulP (comp (rightPath sTm antipodeP) mulP)
    | .antipodeRight => comp comulP (comp (leftPath sTm antipodeP) mulP)
  rhs := fun r => match r with
    | .assoc => comp (arrPath (assocArr sTm sTm sTm)) (comp (rightPath sTm mulP) mulP)
    | .lunit => arrPath (lunitArr sTm)
    | .runit => .nil _
    | .coassoc => comp comulP (rightPath sTm comulP)
    | .lcounit => .nil _
    | .rcounit => arrPath (runitArr sTm)
    | .bialg => comp mulP comulP
    | .counitMul => comp mulP counitP
    | .unitComul => comp oneP comulP
    | .counitUnit => .nil _
    | .antipodeLeft => comp counitP oneP
    | .antipodeRight => comp counitP oneP

end HopfEx

end UlmerBialgebras
