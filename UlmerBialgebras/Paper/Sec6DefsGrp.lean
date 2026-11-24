module

public import UlmerBialgebras.Paper.Sec5DefsCart
public import UlmerBialgebras.Syntax.PathOps
public import Foundations.Data.Fin.VecTwo

/-!
# The theory of groups over the cartesian 2-signature (for Corollary 6.11)

* **Cartesian combinators** on the term graph of any 1-signature relative to `Σ_Cart`: the
  diagonal `δ`, the projections `p₁, p₂`, the terminal map `!`, their functorial images in the
  two slots of `□`, pairing `⟨p, q⟩ = δ ; (p □ q)`, and the derived associator
  `⟨p₁p₁, ⟨p₁p₂, p₂⟩⟩` (`Σ_Cart` has no associator symbol).
* **`grpSig S`**: the multi-sorted 1-signature with sorts `S`, all of type `c`, and for each
  sort `s` a multiplication `s□s → s`, a unit `I → s` and an inverse `s → s`.
* **`grpTheory S`**: for each sort the five group axioms, written as in Mathlib's `GrpObj`:
  associativity `(m □ s) ; m = assoc ; (s □ m) ; m`, the unit laws `⟨id, !;e⟩ ; m = id` and
  `⟨!;e, id⟩ ; m = id`, and the inverse laws `⟨i, id⟩ ; m = ! ; e` and `⟨id, i⟩ ; m = ! ; e`.
* **`grpExtSig`, `grpExtTheory`**: a multi-sorted theory *extending the theory of groups in each
  sort*. Its function symbols are those of `grpSig S` together with extra symbols `Fn'`, and
  its equations those of `grpTheory S` together with extra equations `E'` (arbitrary pairs of
  parallel paths). Restricting to the group symbols and equations gives back `grpTheory S`
  definitionally, which is the form in which Corollary 6.9 applies.

## Main results

* `UlmerBialgebras.Paper.Cart.grpSig`, `UlmerBialgebras.Paper.Cart.grpTheory`: the 1-signature and
  theory of groups in each sort of `S`.
* `UlmerBialgebras.Paper.Cart.grpTheory_isAlgebraic`: `grpTheory S` is algebraic (Definition 3.7).
* `UlmerBialgebras.Paper.Cart.grpExtSig`, `UlmerBialgebras.Paper.Cart.grpExtTheory`: a theory
  extending the theory of groups in each sort by extra symbols and equations (Corollary 6.9).
* `UlmerBialgebras.Paper.Cart.grpExtTheory_restrictSig`: restricting `grpExtTheory` to the group
  symbols and equations gives `grpTheory S`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 (`Σ_Cart`), Corollaries 6.9, 6.11
-/

@[expose] public section

universe u₁

namespace UlmerBialgebras.Paper.Cart

open CategoryTheory

/-! ## Substitution in cartesian terms -/

/-- Substituting `sub` into the variable term `v` gives `sub v`. -/
@[simp] lemma subst_var {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm cartFunSig wty (vty v)) (v : V) :
    (Trm.var v : Trm cartFunSig vty (vty v)).subst sub = sub v := rfl

/-- Substitution commutes with `□`: `(a □ b)[sub] = a[sub] □ b[sub]`. -/
@[simp] lemma subst_cartTens {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm cartFunSig wty (vty v)) (a b : Trm cartFunSig vty ()) :
    (cartTens a b).subst sub = cartTens (a.subst sub) (b.subst sub) :=
  congrArg (Trm.app (S := cartFunSig) CartFun.tens) (Matrix.map_vecTwo (Trm.subst sub) a b)

/-- Substitution fixes the unit term `I`. -/
@[simp] lemma subst_cartUnit {V W : Type} {vty : V → Unit} {wty : W → Unit}
    (sub : ∀ v : V, Trm cartFunSig wty (vty v)) :
    (cartUnit (vty := vty)).subst sub = cartUnit :=
  congrArg (Trm.app (S := cartFunSig) CartFun.unit) (funext fun i => i.elim0)

/-! ## Cartesian combinators on the term graph -/

section Comb

variable {sg : OneSig sigCart}

/-- `a □ b` as a closed term. -/
abbrev tensTerm (a b : sg.CTrm ()) : sg.CTrm () := cartTens a b

/-- `I` as a closed term. -/
abbrev unitTerm : sg.CTrm () := cartUnit

/-- The image `g □ b` of an arrow in the left slot of `□`. -/
def whiskerRightArr {a a' : sg.CTrm ()} (b : sg.CTrm ()) (g : sg.Arr a a') :
    sg.Arr (tensTerm a b) (tensTerm a' b) :=
  OneSig.Arr.app (sg := sg) CartFun.tens 0 ![a, b] ![a', b]
    (Matrix.vecTwo_eq_of_ne_zero a a' b) g

/-- The image `a □ g` of an arrow in the right slot of `□`. -/
def whiskerLeftArr (a : sg.CTrm ()) {b b' : sg.CTrm ()} (g : sg.Arr b b') :
    sg.Arr (tensTerm a b) (tensTerm a b') :=
  OneSig.Arr.app (sg := sg) CartFun.tens 1 ![a, b] ![a, b']
    (Matrix.vecTwo_eq_of_ne_one a b b') g

/-- A single arrow, as a path. -/
def arrPath {t t' : sg.CTrm ()} (g : sg.Arr t t') : sg.Path t t' := .cons g (.nil _)

/-- The image `p □ b` of a path in the left slot of `□`. -/
def whiskerRightPath (b : sg.CTrm ()) :
    ∀ {a t : sg.CTrm ()}, sg.Path a t → sg.Path (tensTerm a b) (tensTerm t b)
  | _, _, .nil _ => .nil _
  | _, _, .cons g p => .cons (whiskerRightArr b g) (whiskerRightPath b p)

/-- The image `a □ p` of a path in the right slot of `□`. -/
def whiskerLeftPath (a : sg.CTrm ()) :
    ∀ {b t : sg.CTrm ()}, sg.Path b t → sg.Path (tensTerm a b) (tensTerm a t)
  | _, _, .nil _ => .nil _
  | _, _, .cons g p => .cons (whiskerLeftArr a g) (whiskerLeftPath a p)

/-- The image `p □ q`: first `p` in the left slot, then `q` in the right slot. -/
def tensorPath {a a' b b' : sg.CTrm ()} (p : sg.Path a a') (q : sg.Path b b') :
    sg.Path (tensTerm a b) (tensTerm a' b') :=
  OneSig.Path.comp (whiskerRightPath b p) (whiskerLeftPath a' q)

/-- The source `x₀` of the diagonal `δ` of `Σ_Cart`, instantiated at `t`, is `t`. -/
lemma subst_diag_src (t : sg.CTrm ()) : (sigCart.trsrc CartTr.diag).subst ![t] = t := rfl

/-- The target `x₀ □ x₀` of the diagonal `δ` of `Σ_Cart`, instantiated at `t`, is `t □ t`. -/
lemma subst_diag_tgt (t : sg.CTrm ()) : (sigCart.trtgt CartTr.diag).subst ![t] = tensTerm t t :=
  congrArg (Trm.app (S := cartFunSig) CartFun.tens)
    (Matrix.map_vecTwo (Trm.subst ![t]) (.var 0) (.var 0))

/-- The source `x₀ □ x₁` of the projection `p₁`, instantiated at `a, b`, is `a □ b`. -/
lemma subst_proj₁_src (a b : sg.CTrm ()) :
    (sigCart.trsrc CartTr.proj₁).subst ![a, b] = tensTerm a b :=
  congrArg (Trm.app (S := cartFunSig) CartFun.tens)
    (Matrix.map_vecTwo (Trm.subst ![a, b]) (.var 0) (.var 1))

/-- The target `x₀` of the projection `p₁`, instantiated at `a, b`, is `a`. -/
lemma subst_proj₁_tgt (a b : sg.CTrm ()) : (sigCart.trtgt CartTr.proj₁).subst ![a, b] = a := rfl

/-- The source `x₀ □ x₁` of the projection `p₂`, instantiated at `a, b`, is `a □ b`. -/
lemma subst_proj₂_src (a b : sg.CTrm ()) :
    (sigCart.trsrc CartTr.proj₂).subst ![a, b] = tensTerm a b :=
  congrArg (Trm.app (S := cartFunSig) CartFun.tens)
    (Matrix.map_vecTwo (Trm.subst ![a, b]) (.var 0) (.var 1))

/-- The target `x₁` of the projection `p₂`, instantiated at `a, b`, is `b`. -/
lemma subst_proj₂_tgt (a b : sg.CTrm ()) : (sigCart.trtgt CartTr.proj₂).subst ![a, b] = b := rfl

/-- The source `x₀` of the terminal map `!`, instantiated at `t`, is `t`. -/
lemma subst_term_src (t : sg.CTrm ()) : (sigCart.trsrc CartTr.term).subst ![t] = t := rfl

/-- The target `I` of the terminal map `!`, instantiated at `t`, is `I`. -/
lemma subst_term_tgt (t : sg.CTrm ()) : (sigCart.trtgt CartTr.term).subst ![t] = unitTerm :=
  congrArg (Trm.app (S := cartFunSig) CartFun.unit) (funext fun i => i.elim0)

/-- The instance `δ_t : t → t□t` of the diagonal. -/
def diagArr (t : sg.CTrm ()) : sg.Arr t (tensTerm t t) :=
  OneSig.Arr.transport (subst_diag_src t) (subst_diag_tgt t)
    (OneSig.Arr.tr (sg := sg) CartTr.diag ![t])

/-- The instance `p₁ : a□b → a` of the first projection. -/
def fstArr (a b : sg.CTrm ()) : sg.Arr (tensTerm a b) a :=
  OneSig.Arr.transport (subst_proj₁_src a b) (subst_proj₁_tgt a b)
    (OneSig.Arr.tr (sg := sg) CartTr.proj₁ ![a, b])

/-- The instance `p₂ : a□b → b` of the second projection. -/
def sndArr (a b : sg.CTrm ()) : sg.Arr (tensTerm a b) b :=
  OneSig.Arr.transport (subst_proj₂_src a b) (subst_proj₂_tgt a b)
    (OneSig.Arr.tr (sg := sg) CartTr.proj₂ ![a, b])

/-- The instance `!_t : t → I`. -/
def toUnitArr (t : sg.CTrm ()) : sg.Arr t unitTerm :=
  OneSig.Arr.transport (subst_term_src t) (subst_term_tgt t)
    (OneSig.Arr.tr (sg := sg) CartTr.term ![t])

/-- The diagonal, as a path. -/
def diagPath (t : sg.CTrm ()) : sg.Path t (tensTerm t t) := arrPath (diagArr t)

/-- The first projection, as a path. -/
def fstPath (a b : sg.CTrm ()) : sg.Path (tensTerm a b) a := arrPath (fstArr a b)

/-- The second projection, as a path. -/
def sndPath (a b : sg.CTrm ()) : sg.Path (tensTerm a b) b := arrPath (sndArr a b)

/-- The unique map to `I`, as a path. -/
def toUnitPath (t : sg.CTrm ()) : sg.Path t unitTerm := arrPath (toUnitArr t)

/-- The pairing `⟨p, q⟩ : t → a□b` of two paths out of `t`, built from the diagonal. -/
def liftPath {t a b : sg.CTrm ()} (p : sg.Path t a) (q : sg.Path t b) : sg.Path t (tensTerm a b) :=
  OneSig.Path.comp (diagPath t) (tensorPath p q)

/-- The derived associator `(a□b)□c → a□(b□c)`. -/
def assocPath (a b c : sg.CTrm ()) : sg.Path (tensTerm (tensTerm a b) c)
    (tensTerm a (tensTerm b c)) :=
  liftPath (OneSig.Path.comp (fstPath (tensTerm a b) c) (fstPath a b))
    (liftPath (OneSig.Path.comp (fstPath (tensTerm a b) c) (sndPath a b))
        (sndPath (tensTerm a b) c))

end Comb

/-! ## The multi-sorted theory of groups -/

/-- The function symbols of the theory of groups at a sort. -/
inductive GrpFn | mul | one | inv
  deriving DecidableEq

/-- The equations of the theory of groups at a sort. -/
inductive GrpEqn | assoc | mulOne | oneMul | invMul | mulInv
  deriving DecidableEq

/-- The domain term of a group function symbol at the sort `s`. -/
def grpFnDom {S : Type u₁} : S × GrpFn → Trm cartFunSig (fun _ : S => ()) ()
  | (s, .mul) => cartTens (.var s) (.var s)
  | (_, .one) => cartUnit
  | (s, .inv) => .var s

/-- **The 1-signature of groups in each sort of `S`.** -/
def grpSig (S : Type u₁) : OneSig sigCart where
  Srt := S
  sty := fun _ => ()
  Fn := S × GrpFn
  fnty := fun _ => ()
  fndom := grpFnDom
  fncod := fun f => .var f.1

section GrpPaths

variable {S : Type u₁}

/-- The sort `s`, as a closed term. -/
abbrev sortTerm (s : S) : (grpSig S).CTrm () := .var s

/-- The multiplication of the sort `s`, as a path. -/
def mulPath (s : S) : (grpSig S).Path (tensTerm (sortTerm s) (sortTerm s)) (sortTerm s) :=
  arrPath (OneSig.Arr.fn (sg := grpSig S) (s, .mul))

/-- The unit of the sort `s`, as a path. -/
def onePath (s : S) : (grpSig S).Path unitTerm (sortTerm s) := arrPath
    (OneSig.Arr.fn (sg := grpSig S) (s, .one))

/-- The inverse of the sort `s`, as a path. -/
def invPath (s : S) : (grpSig S).Path (sortTerm s) (sortTerm s) :=
  arrPath (OneSig.Arr.fn (sg := grpSig S) (s, .inv))

/-- `! ; e : s → s`. -/
def constOnePath (s : S) : (grpSig S).Path (sortTerm s) (sortTerm s) := OneSig.Path.comp
    (toUnitPath (sortTerm s)) (onePath s)

/-- The domain term of a group axiom. -/
def grpEqnDom : S × GrpEqn → (grpSig S).CTrm ()
  | (s, .assoc) => tensTerm (tensTerm (sortTerm s) (sortTerm s)) (sortTerm s)
  | (s, .mulOne) => sortTerm s
  | (s, .oneMul) => sortTerm s
  | (s, .invMul) => sortTerm s
  | (s, .mulInv) => sortTerm s

/-- The left-hand side of a group axiom. -/
def grpEqnLhs : ∀ r : S × GrpEqn, (grpSig S).Path (grpEqnDom r) (sortTerm r.1)
  | (s, .assoc) => OneSig.Path.comp (whiskerRightPath (sortTerm s) (mulPath s)) (mulPath s)
  | (s, .mulOne) => OneSig.Path.comp (liftPath (.nil (sortTerm s)) (constOnePath s)) (mulPath s)
  | (s, .oneMul) => OneSig.Path.comp (liftPath (constOnePath s) (.nil (sortTerm s))) (mulPath s)
  | (s, .invMul) => OneSig.Path.comp (liftPath (invPath s) (.nil (sortTerm s))) (mulPath s)
  | (s, .mulInv) => OneSig.Path.comp (liftPath (.nil (sortTerm s)) (invPath s)) (mulPath s)

/-- The right-hand side of a group axiom. -/
def grpEqnRhs : ∀ r : S × GrpEqn, (grpSig S).Path (grpEqnDom r) (sortTerm r.1)
  | (s, .assoc) => OneSig.Path.comp (assocPath (sortTerm s) (sortTerm s) (sortTerm s))
      (OneSig.Path.comp (whiskerLeftPath (sortTerm s) (mulPath s)) (mulPath s))
  | (s, .mulOne) => .nil (sortTerm s)
  | (s, .oneMul) => .nil (sortTerm s)
  | (s, .invMul) => constOnePath s
  | (s, .mulInv) => constOnePath s

end GrpPaths

/-- **The theory of groups in each sort of `S`**: associativity, the two unit laws and the two
inverse laws. -/
def grpTheory (S : Type u₁) : Theory (grpSig S) where
  Eqn := S × GrpEqn
  eqty := fun _ => ()
  dom := grpEqnDom
  cod := fun r => sortTerm r.1
  lhs := grpEqnLhs
  rhs := grpEqnRhs

/-- The theory of groups `grpTheory S` is algebraic in the sense of Definition 3.7 of
[forsman2026syntactic]: all coarity terms of its symbols and equations are sorts. -/
lemma grpTheory_isAlgebraic (S : Type u₁) : (grpTheory S).IsAlgebraic :=
  ⟨fun _ => trivial, fun _ => trivial⟩

/-! ## Theories extending the theory of groups in each sort -/

section Ext

variable (S : Type u₁) (Fn' : Type u₁) (dom' cod' : Fn' → Trm cartFunSig (fun _ : S => ()) ())

/-- The 1-signature of groups in each sort of `S`, extended by function symbols `Fn'` with
arities `dom'` and coarities `cod'`. -/
def grpExtSig : OneSig sigCart where
  Srt := S
  sty := fun _ => ()
  Fn := (S × GrpFn) ⊕ Fn'
  fnty := fun _ => ()
  fndom := Sum.elim grpFnDom dom'
  fncod := Sum.elim (fun f => .var f.1) cod'

/-- Restricting `grpExtSig` to the group symbols gives `grpSig S` (definitionally). -/
lemma grpExtSig_restrictFn : (grpExtSig S Fn' dom' cod').restrictFn Sum.inl = grpSig S := rfl

variable {E' : Type u₁} (edom ecod : E' → (grpExtSig S Fn' dom' cod').CTrm ())
  (elhs erhs : ∀ e, (grpExtSig S Fn' dom' cod').Path (edom e) (ecod e))

/-- **A theory extending the theory of groups in each sort**: the group axioms of
`grpTheory S`, translated into `grpExtSig`, together with extra equations `E'`. -/
def grpExtTheory : Theory (grpExtSig S Fn' dom' cod') where
  Eqn := (S × GrpEqn) ⊕ E'
  eqty := fun _ => ()
  dom := Sum.elim grpEqnDom edom
  cod := Sum.elim (fun r => sortTerm r.1) ecod
  lhs := fun r => match r with
    | .inl r => OneSig.Path.ofRestrictFn (sg := grpExtSig S Fn' dom' cod') Sum.inl (grpEqnLhs r)
    | .inr e => elhs e
  rhs := fun r => match r with
    | .inl r => OneSig.Path.ofRestrictFn (sg := grpExtSig S Fn' dom' cod') Sum.inl (grpEqnRhs r)
    | .inr e => erhs e

/-- Restricting `grpExtTheory` to the group symbols and equations gives `grpTheory S`
(definitionally). -/
lemma grpExtTheory_restrictSig :
    (grpExtTheory S Fn' dom' cod' edom ecod elhs erhs).restrictSig Sum.inl Sum.inl
      (fun r => grpEqnLhs r) (fun r => grpEqnRhs r) = grpTheory S := rfl

end Ext

end UlmerBialgebras.Paper.Cart
