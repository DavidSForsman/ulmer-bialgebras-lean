module

public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import UlmerBialgebras.Syntax.PathOps

/-!
# Examples 3.20 (3): the signature pair and theory of fields

This file formalises the syntactic half of **Examples 3.20 (3)** of *A Syntactic Approach to
Ulmer's Bialgebras*: the cartesian 2-signature

`Σ = (c, □ : cc → c, I : () → c, S : c → c,
      δˣ : x → x□x, p₁ˣʸ : x□y → x, p₂ˣʸ : x□y → y, !ˣ : x → I, ηˣ : x → Sx)`,

the relative 1-signature

`σ_Field = (s : c, m : s□s → s, i : s → s, u : I → s,
            m₁, m₂ : Ss□Ss → Ss, ν : Ss → Ss, ι : I → Ss)`,

and the theory `T_Field`, consisting of

* the equations of a commutative group for `(s, m, i, u)`;
* the equations of a commutative ring for `(Ss, m₁, ν, ι, m₂, ηs ∘ u)`, the quadruple
  `(Ss, m₁, ν, ι)` carrying the additive and `(Ss, m₂, ηs ∘ u)` the multiplicative structure;
* the equation `m₂ ∘ (ηs □ ηs) = ηs ∘ m : s□s → Ss` saying that `ηs` is a morphism of magmas
  from `(s, m)` to `(Ss, m₂)`.

Since the 2-signature only provides the diagonal, the projections and the map to the terminal
object, the structural isomorphisms used in writing down the equations (the associator
`(a□b)□c → a□(b□c)` and the symmetry `a□b → b□a`) are *derived* paths of the term graph,
built out of `δ`, `p₁`, `p₂` by the pairing combinator `UlmerBialgebras.FieldEx.pairP`.

## Main results

* `UlmerBialgebras.FieldEx.twoSig`: the cartesian 2-signature `Σ` of Examples 3.20 (3).
* `UlmerBialgebras.FieldEx.oneSig`: the relative 1-signature `σ_Field`.
* `UlmerBialgebras.FieldEx.theory`: the theory `T_Field` of fields.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3)
-/

@[expose] public section

namespace UlmerBialgebras

namespace FieldEx

/-- The functor symbols of `Σ`: the binary `□`, the nullary `I` and the unary `S`. -/
inductive FunSym | tens | unit | succ
  deriving DecidableEq

/-- The transformation symbols of `Σ`: the diagonal, the two projections, the map to the
terminal object and the unit `η` of `S`. -/
inductive TrSym | diag | proj₁ | proj₂ | term | eta
  deriving DecidableEq

/-- The function symbols of `σ_Field`. -/
inductive FnSym | mul | inv | one | add | rmul | neg | zero
  deriving DecidableEq

/-- The equations of `T_Field`. -/
inductive EqnSym
  | mulAssoc | mulComm | mulUnit | mulInv
  | addAssoc | addComm | addUnit | addInv
  | rmulAssoc | rmulComm | rmulUnit
  | distrib
  | etaMul
  deriving DecidableEq

/-- The category and functor symbols of `Σ`. -/
@[reducible] def funSig : FunSig where
  Cat := Unit
  Fun := FunSym
  arn := fun B => match B with | .tens => 2 | .unit => 0 | .succ => 1
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

/-- The term `S a`. -/
@[reducible] def sc {V : Type} {vty : V → Unit} (a : Tm vty) : Tm vty :=
  Trm.app (S := funSig) FunSym.succ ![a]
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
  fin_cases i
  · rfl
  · rfl

/-- Substitution commutes with the term `S a`. -/
@[simp] lemma subst_sc {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) (a : Tm vty) :
    (sc a).subst sub = sc (a.subst sub) := by
  rw [Trm.subst]
  congr 1
  funext i
  fin_cases i
  rfl

/-- Substitution fixes the term `I`. -/
@[simp] lemma subst_un {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm funSig wty (vty v)) : (un (vty := vty)).subst sub = un := by
  rw [Trm.subst]
  congr 1
  funext i
  exact i.elim0

/-- **The cartesian 2-signature `Σ` of Examples 3.20 (3).** -/
@[reducible] def twoSig : TwoSig where
  toFunSig := funSig
  Tr := TrSym
  trn := fun a => match a with
    | .diag => 1 | .proj₁ => 2 | .proj₂ => 2 | .term => 1 | .eta => 1
  trt := fun _ _ => ()
  trty := fun _ => ()
  trsrc := fun a => match a with
    | .diag => .var 0
    | .proj₁ => tn (.var 0) (.var 1)
    | .proj₂ => tn (.var 0) (.var 1)
    | .term => .var 0
    | .eta => .var 0
  trtgt := fun a => match a with
    | .diag => tn (.var 0) (.var 0)
    | .proj₁ => .var 0
    | .proj₂ => .var 1
    | .term => un
    | .eta => sc (.var 0)

/-- The sort `s`. -/
@[reducible] def sTm : Trm funSig (fun _ : Unit => ()) () := .var ()

/-- **The relative 1-signature `σ_Field`.** -/
@[reducible] def oneSig : OneSig twoSig where
  Srt := Unit
  sty := fun _ => ()
  Fn := FnSym
  fnty := fun _ => ()
  fndom := fun f => match f with
    | .mul => tn sTm sTm
    | .inv => sTm
    | .one => un
    | .add => tn (sc sTm) (sc sTm)
    | .rmul => tn (sc sTm) (sc sTm)
    | .neg => sc sTm
    | .zero => un
  fncod := fun f => match f with
    | .mul => sTm
    | .inv => sTm
    | .one => sTm
    | .add => sc sTm
    | .rmul => sc sTm
    | .neg => sc sTm
    | .zero => sc sTm

/-! ## Arrows and paths of the term graph -/

/-- Closed terms over the sort of `σ_Field`. -/
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

/-- The image `p □ q` of a pair of paths: first apply `p` in the left slot, then `q` in the
right slot. -/
def tensPath {a a' b b' : CTm} (p : oneSig.Path a a') (q : oneSig.Path b b') :
    oneSig.Path (tn a b) (tn a' b') :=
  OneSig.Path.comp (leftPath b p) (rightPath a' q)

/-- The arrow attached to a function symbol. -/
def fnArr (f : FnSym) : oneSig.Arr (oneSig.fndom f) (oneSig.fncod f) :=
  OneSig.Arr.fn (sg := oneSig) f

/-! ### Instances of the transformation symbols -/

/-- The source of the diagonal symbol, instantiated at `t`, is `t`. -/
lemma subst_diag_src (t : CTm) : (twoSig.trsrc TrSym.diag).subst ![t] = t := rfl

/-- The target of the diagonal symbol, instantiated at `t`, is `t □ t`. -/
lemma subst_diag_tgt (t : CTm) :
    (twoSig.trtgt TrSym.diag).subst ![t] = tn t t := by
  simp [twoSig]

/-- The source of the first projection symbol, instantiated at `a, b`, is `a □ b`. -/
lemma subst_proj₁_src (a b : CTm) :
    (twoSig.trsrc TrSym.proj₁).subst ![a, b] = tn a b := by
  simp [twoSig]

/-- The target of the first projection symbol, instantiated at `a, b`, is `a`. -/
lemma subst_proj₁_tgt (a b : CTm) : (twoSig.trtgt TrSym.proj₁).subst ![a, b] = a := rfl

/-- The source of the second projection symbol, instantiated at `a, b`, is `a □ b`. -/
lemma subst_proj₂_src (a b : CTm) :
    (twoSig.trsrc TrSym.proj₂).subst ![a, b] = tn a b := by
  simp [twoSig]

/-- The target of the second projection symbol, instantiated at `a, b`, is `b`. -/
lemma subst_proj₂_tgt (a b : CTm) : (twoSig.trtgt TrSym.proj₂).subst ![a, b] = b := rfl

/-- The source of the terminal symbol, instantiated at `t`, is `t`. -/
lemma subst_term_src (t : CTm) : (twoSig.trsrc TrSym.term).subst ![t] = t := rfl

/-- The target of the terminal symbol, instantiated at `t`, is `I`. -/
lemma subst_term_tgt (t : CTm) : (twoSig.trtgt TrSym.term).subst ![t] = un := by
  simp [twoSig]

/-- The source of the unit symbol `η`, instantiated at `t`, is `t`. -/
lemma subst_eta_src (t : CTm) : (twoSig.trsrc TrSym.eta).subst ![t] = t := rfl

/-- The target of the unit symbol `η`, instantiated at `t`, is `S t`. -/
lemma subst_eta_tgt (t : CTm) : (twoSig.trtgt TrSym.eta).subst ![t] = sc t := by
  simp [twoSig]

/-- The instance `δ_t : t → t□t` of the diagonal. -/
def diagArr (t : CTm) : oneSig.Arr t (tn t t) :=
  OneSig.Arr.transport (subst_diag_src t) (subst_diag_tgt t)
    (OneSig.Arr.tr (sg := oneSig) TrSym.diag ![t])

/-- The instance `p₁ : a□b → a` of the first projection. -/
def proj₁Arr (a b : CTm) : oneSig.Arr (tn a b) a :=
  OneSig.Arr.transport (subst_proj₁_src a b) (subst_proj₁_tgt a b)
    (OneSig.Arr.tr (sg := oneSig) TrSym.proj₁ ![a, b])

/-- The instance `p₂ : a□b → b` of the second projection. -/
def proj₂Arr (a b : CTm) : oneSig.Arr (tn a b) b :=
  OneSig.Arr.transport (subst_proj₂_src a b) (subst_proj₂_tgt a b)
    (OneSig.Arr.tr (sg := oneSig) TrSym.proj₂ ![a, b])

/-- The instance `!_t : t → I`. -/
def termArr (t : CTm) : oneSig.Arr t un :=
  OneSig.Arr.transport (subst_term_src t) (subst_term_tgt t)
    (OneSig.Arr.tr (sg := oneSig) TrSym.term ![t])

/-- The instance `η_t : t → S t` of the unit. -/
def etaArr (t : CTm) : oneSig.Arr t (sc t) :=
  OneSig.Arr.transport (subst_eta_src t) (subst_eta_tgt t)
    (OneSig.Arr.tr (sg := oneSig) TrSym.eta ![t])

/-! ### Derived cartesian combinators -/

/-- The diagonal, as a path. -/
def diagP (t : CTm) : oneSig.Path t (tn t t) := arrPath (diagArr t)

/-- The first projection, as a path. -/
def fstP (a b : CTm) : oneSig.Path (tn a b) a := arrPath (proj₁Arr a b)

/-- The second projection, as a path. -/
def sndP (a b : CTm) : oneSig.Path (tn a b) b := arrPath (proj₂Arr a b)

/-- The unique map to `I`, as a path. -/
def bangP (t : CTm) : oneSig.Path t un := arrPath (termArr t)

/-- The unit `η_t`, as a path. -/
def etaP (t : CTm) : oneSig.Path t (sc t) := arrPath (etaArr t)

/-- The pairing `⟨p, q⟩ : t → a□b` of two paths out of `t`, built from the diagonal. -/
def pairP {t a b : CTm} (p : oneSig.Path t a) (q : oneSig.Path t b) :
    oneSig.Path t (tn a b) :=
  OneSig.Path.comp (diagP t) (tensPath p q)

/-- The derived associator `(a□b)□c → a□(b□c)`. -/
def assocP (a b c : CTm) : oneSig.Path (tn (tn a b) c) (tn a (tn b c)) :=
  pairP (OneSig.Path.comp (fstP (tn a b) c) (fstP a b))
    (pairP (OneSig.Path.comp (fstP (tn a b) c) (sndP a b)) (sndP (tn a b) c))

/-- The derived symmetry `a□b → b□a`. -/
def swapP (a b : CTm) : oneSig.Path (tn a b) (tn b a) :=
  pairP (sndP a b) (fstP a b)

/-! ## The equations of a commutative group

The four axioms below are stated for an arbitrary term `t` equipped with paths playing the
role of a multiplication, an inverse and a unit; they are used twice, for `(s, m, i, u)` and
for the additive structure `(Ss, m₁, ν, ι)`.
-/

section GroupAxioms

variable (t : CTm) (mul : oneSig.Path (tn t t) t) (inv : oneSig.Path t t)
  (e : oneSig.Path un t)

/-- Left-hand side of associativity: `(mul □ t) ; mul`. -/
def assocLHS : oneSig.Path (tn (tn t t) t) t :=
  OneSig.Path.comp (leftPath t mul) mul

/-- Right-hand side of associativity: `assoc ; (t □ mul) ; mul`. -/
def assocRHS : oneSig.Path (tn (tn t t) t) t :=
  OneSig.Path.comp (assocP t t t) (OneSig.Path.comp (rightPath t mul) mul)

/-- Right-hand side of commutativity: `swap ; mul`. -/
def commRHS : oneSig.Path (tn t t) t :=
  OneSig.Path.comp (swapP t t) mul

/-- Left-hand side of the unit law: `⟨! ; e, id⟩ ; mul`. -/
def unitLHS : oneSig.Path t t :=
  OneSig.Path.comp (pairP (OneSig.Path.comp (bangP t) e) (.nil t)) mul

/-- Left-hand side of the inverse law: `⟨inv, id⟩ ; mul`. -/
def invLHS : oneSig.Path t t :=
  OneSig.Path.comp (pairP inv (.nil t)) mul

/-- Right-hand side of the inverse law: `! ; e`. -/
def invRHS : oneSig.Path t t :=
  OneSig.Path.comp (bangP t) e

end GroupAxioms

/-! ## The theory of fields -/

/-- The term `Ss`. -/
@[reducible] def ssTm : CTm := sc sTm

/-- `m`, as a path. -/
def mulP : oneSig.Path (tn sTm sTm) sTm := arrPath (fnArr FnSym.mul)

/-- `i`, as a path. -/
def invP : oneSig.Path sTm sTm := arrPath (fnArr FnSym.inv)

/-- `u`, as a path. -/
def oneP : oneSig.Path un sTm := arrPath (fnArr FnSym.one)

/-- `m₁`, as a path. -/
def addP : oneSig.Path (tn ssTm ssTm) ssTm := arrPath (fnArr FnSym.add)

/-- `m₂`, as a path. -/
def rmulP : oneSig.Path (tn ssTm ssTm) ssTm := arrPath (fnArr FnSym.rmul)

/-- `ν`, as a path. -/
def negP : oneSig.Path ssTm ssTm := arrPath (fnArr FnSym.neg)

/-- `ι`, as a path. -/
def zeroP : oneSig.Path un ssTm := arrPath (fnArr FnSym.zero)

/-- `ηs : s → Ss`, as a path. -/
def etaSP : oneSig.Path sTm ssTm := etaP sTm

/-- The multiplicative unit `ηs ∘ u : I → Ss` of the ring. -/
def rmulUnitP : oneSig.Path un ssTm := OneSig.Path.comp oneP etaSP

/-- Left-hand side of distributivity: `(Ss □ m₁) ; m₂`. -/
def distribLHS : oneSig.Path (tn ssTm (tn ssTm ssTm)) ssTm :=
  OneSig.Path.comp (rightPath ssTm addP) rmulP

/-- Right-hand side of distributivity: `⟨⟨p₁, p₂p₁⟩ ; m₂, ⟨p₁, p₂p₂⟩ ; m₂⟩ ; m₁`. -/
def distribRHS : oneSig.Path (tn ssTm (tn ssTm ssTm)) ssTm :=
  OneSig.Path.comp
    (pairP
      (OneSig.Path.comp
        (pairP (fstP ssTm (tn ssTm ssTm))
          (OneSig.Path.comp (sndP ssTm (tn ssTm ssTm)) (fstP ssTm ssTm))) rmulP)
      (OneSig.Path.comp
        (pairP (fstP ssTm (tn ssTm ssTm))
          (OneSig.Path.comp (sndP ssTm (tn ssTm ssTm)) (sndP ssTm ssTm))) rmulP))
    addP

open OneSig.Path in
/-- **The theory `T_Field` of fields.** -/
def theory : Theory oneSig where
  Eqn := EqnSym
  eqty := fun _ => ()
  dom := fun r => match r with
    | .mulAssoc => tn (tn sTm sTm) sTm
    | .mulComm => tn sTm sTm
    | .mulUnit => sTm
    | .mulInv => sTm
    | .addAssoc => tn (tn ssTm ssTm) ssTm
    | .addComm => tn ssTm ssTm
    | .addUnit => ssTm
    | .addInv => ssTm
    | .rmulAssoc => tn (tn ssTm ssTm) ssTm
    | .rmulComm => tn ssTm ssTm
    | .rmulUnit => ssTm
    | .distrib => tn ssTm (tn ssTm ssTm)
    | .etaMul => tn sTm sTm
  cod := fun r => match r with
    | .mulAssoc | .mulComm | .mulUnit | .mulInv => sTm
    | .addAssoc | .addComm | .addUnit | .addInv | .rmulAssoc | .rmulComm | .rmulUnit | .distrib
    | .etaMul => ssTm
  lhs := fun r => match r with
    | .mulAssoc => assocLHS sTm mulP
    | .mulComm => mulP
    | .mulUnit => unitLHS sTm mulP oneP
    | .mulInv => invLHS sTm mulP invP
    | .addAssoc => assocLHS ssTm addP
    | .addComm => addP
    | .addUnit => unitLHS ssTm addP zeroP
    | .addInv => invLHS ssTm addP negP
    | .rmulAssoc => assocLHS ssTm rmulP
    | .rmulComm => rmulP
    | .rmulUnit => unitLHS ssTm rmulP rmulUnitP
    | .distrib => distribLHS
    | .etaMul => comp (tensPath etaSP etaSP) rmulP
  rhs := fun r => match r with
    | .mulAssoc => assocRHS sTm mulP
    | .mulComm => commRHS sTm mulP
    | .mulUnit => .nil _
    | .mulInv => invRHS sTm oneP
    | .addAssoc => assocRHS ssTm addP
    | .addComm => commRHS ssTm addP
    | .addUnit => .nil _
    | .addInv => invRHS ssTm zeroP
    | .rmulAssoc => assocRHS ssTm rmulP
    | .rmulComm => commRHS ssTm rmulP
    | .rmulUnit => .nil _
    | .distrib => distribRHS
    | .etaMul => comp mulP etaSP

end FieldEx

end UlmerBialgebras
