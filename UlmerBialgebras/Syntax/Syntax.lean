module

public import UlmerBialgebras.Basic.PIE

/-!
# Syntax: signature pairs, terms and the term graph

This file formalises Section 3.2 of *A Syntactic Approach to Ulmer's Bialgebras*:
2-signatures (Definition 3.3), relative 1-signatures (Definition 3.5), the term graph
(Definition 3.6) and bialgebraic theories (Definition 3.7).

The three symbol types of a 2-signature carry independent universe levels. So do the sorts and
function symbols of a 1-signature and the equations of a theory: each is the size of one of the
products that `M^σ` and `M^T` need (`UlmerBialgebras.HasChosenProductsOfSize`).

## Main results

* `UlmerBialgebras.FunSig`, `UlmerBialgebras.Trm`: category and functor symbols, and Σ-terms over
  typed variables (Definition 3.3).
* `UlmerBialgebras.TwoSig`: 2-signatures (Definition 3.3).
* `UlmerBialgebras.OneSig`: 1-signatures relative to a 2-signature (Definition 3.5).
* `UlmerBialgebras.OneSig.Arr`, `UlmerBialgebras.OneSig.Path`: the arrows and paths of the term
  graph (Definition 3.6).
* `UlmerBialgebras.Theory`, `UlmerBialgebras.Theory.IsAlgebraic`,
  `UlmerBialgebras.Theory.IsCoalgebraic`: bialgebraic theories, and algebraic and coalgebraic ones
  (Definition 3.7).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 3.2,
  Definitions 3.3, 3.5, 3.6, 3.7
-/

@[expose] public section

namespace UlmerBialgebras

universe u₁ u₂ u₃ u₄ u₅ u₆ uᵥ u𝓌

/-- The category symbols and functor symbols of a 2-signature (Definition 3.3 (1),(2)).
A functor symbol `B` has arity the list `art B : Fin (arn B) → Cat` and codomain `fcod B`. -/
structure FunSig where
  /-- The small set of category symbols. -/
  Cat : Type u₁
  /-- The small set of functor symbols. -/
  Fun : Type u₂
  /-- The length of the arity of a functor symbol. -/
  arn : Fun → ℕ
  /-- The arity of a functor symbol. -/
  art : ∀ B : Fun, Fin (arn B) → Cat
  /-- The codomain of a functor symbol. -/
  fcod : Fun → Cat

/-- Σ-terms over a typed set of variables (Definition 3.3 (3)).  A *context* of the paper is
here encoded by the variable type `V` itself; contexts `x₁ ⋯ xₙ` are the types `Fin n`. -/
inductive Trm (S : FunSig.{u₁, u₂}) {V : Type uᵥ} (vty : V → S.Cat) : S.Cat → Type (max u₁ u₂ uᵥ)
  | var (v : V) : Trm S vty (vty v)
  | app (B : S.Fun) (args : ∀ i : Fin (S.arn B), Trm S vty (S.art B i)) : Trm S vty (S.fcod B)

namespace Trm

variable {S : FunSig}

/-- Whether a term is a variable (used to say that a term is a sort). -/
def IsVar {V : Type uᵥ} {vty : V → S.Cat} : ∀ {c : S.Cat}, Trm S vty c → Prop
  | _, .var _ => True
  | _, .app _ _ => False

/-- Simultaneous substitution of terms for variables. -/
def subst {V : Type uᵥ} {W : Type u𝓌} {vty : V → S.Cat} {wty : W → S.Cat}
    (sub : ∀ v : V, Trm S wty (vty v)) : ∀ {c : S.Cat}, Trm S vty c → Trm S wty c
  | _, .var v => sub v
  | _, .app B args => .app B (fun i => subst sub (args i))

end Trm

/-- A 2-signature `Σ = (C, F, T)` (**Definition 3.3**, [forsman2026syntactic]). A transformation
symbol `α` comes with a context of length `trn α` typed by `trt α`, and a parallel pair of terms
`trsrc α`, `trtgt α` of type `trty α` in that context. -/
structure TwoSig extends FunSig.{u₁, u₂} where
  /-- The small set of transformation symbols. -/
  Tr : Type u₃
  /-- The length of the context of a transformation symbol. -/
  trn : Tr → ℕ
  /-- The types of the context variables of a transformation symbol. -/
  trt : ∀ a : Tr, Fin (trn a) → Cat
  /-- The type of the two terms of a transformation symbol. -/
  trty : Tr → Cat
  /-- The source term of a transformation symbol. -/
  trsrc : ∀ a : Tr, Trm toFunSig (trt a) (trty a)
  /-- The target term of a transformation symbol. -/
  trtgt : ∀ a : Tr, Trm toFunSig (trt a) (trty a)

/-- A 1-signature `σ = (S, F)` relative to a 2-signature (**Definition 3.5**,
[forsman2026syntactic]). -/
structure OneSig (Sg : TwoSig.{u₁, u₂, u₃}) where
  /-- The small set of sorts. -/
  Srt : Type u₄
  /-- The type of a sort. -/
  sty : Srt → Sg.Cat
  /-- The small set of function symbols. -/
  Fn : Type u₅
  /-- The type of a function symbol. -/
  fnty : Fn → Sg.Cat
  /-- The domain (arity) term of a function symbol. -/
  fndom : ∀ f : Fn, Trm Sg.toFunSig sty (fnty f)
  /-- The codomain (coarity) term of a function symbol. -/
  fncod : ∀ f : Fn, Trm Sg.toFunSig sty (fnty f)

namespace OneSig

variable {Sg : TwoSig} (sg : OneSig Sg)

/-- The closed Σ-terms over the sorts of `σ`: the vertices of the term graph. -/
abbrev CTrm (c : Sg.Cat) : Type _ := Trm Sg.toFunSig sg.sty c

/-- The arrows of the term graph `G_σ` (**Definition 3.6**, [forsman2026syntactic]). -/
inductive Arr : ∀ {c : Sg.Cat}, sg.CTrm c → sg.CTrm c → Type _
  /-- Each function symbol `f : t₁ → t₂` of `σ` is an arrow. -/
  | fn (f : sg.Fn) : Arr (sg.fndom f) (sg.fncod f)
  /-- Each instance `α_{t₁,…,tₙ}` of a transformation symbol of `Σ` at closed terms. -/
  | tr (a : Sg.Tr) (sub : ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i)) :
      Arr ((Sg.trsrc a).subst sub) ((Sg.trtgt a).subst sub)
  /-- The functorial image `B(t₀, …, g, …, tₙ)` of an arrow `g` in the `i`-th slot. -/
  | app (B : Sg.Fun) (i : Fin (Sg.arn B))
      (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
      (hne : ∀ j, j ≠ i → args j = args' j) (g : Arr (args i) (args' i)) :
      Arr (.app B args) (.app B args')

/-- Paths in the term graph `G_σ`. -/
inductive Path : ∀ {c : Sg.Cat}, sg.CTrm c → sg.CTrm c → Type _
  | nil {c : Sg.Cat} (t : sg.CTrm c) : Path t t
  | cons {c : Sg.Cat} {t t' t'' : sg.CTrm c} (g : sg.Arr t t') (p : Path t' t'') : Path t t''

end OneSig

/-- Transport of an arrow of the term graph along equalities of its endpoints. -/
def OneSig.Arr.transport {Sg : TwoSig} {sg : OneSig Sg} {c : Sg.Cat} {t₁ t₂ t₁' t₂' : sg.CTrm c}
    (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (g : sg.Arr t₁ t₂) : sg.Arr t₁' t₂' := h₁ ▸ h₂ ▸ g

/-- A bialgebraic σ-theory (**Definition 3.7**, [forsman2026syntactic]): a small set of parallel
paths in the term graph. -/
structure Theory {Sg : TwoSig.{u₁, u₂, u₃}} (sg : OneSig.{u₁, u₂, u₃, u₄, u₅} Sg) where
  /-- The small set of equations. -/
  Eqn : Type u₆
  /-- The type of an equation. -/
  eqty : Eqn → Sg.Cat
  /-- The (equational arity) domain term of an equation. -/
  dom : ∀ r : Eqn, sg.CTrm (eqty r)
  /-- The (equational coarity) codomain term of an equation. -/
  cod : ∀ r : Eqn, sg.CTrm (eqty r)
  /-- The first path of an equation. -/
  lhs : ∀ r : Eqn, sg.Path (dom r) (cod r)
  /-- The second path of an equation. -/
  rhs : ∀ r : Eqn, sg.Path (dom r) (cod r)

namespace Theory

variable {Sg : TwoSig} {sg : OneSig Sg} (T : Theory sg)

/-- `T` is *algebraic* if all coarity terms are sorts (Definition 3.7). -/
def IsAlgebraic : Prop :=
  (∀ f : sg.Fn, (sg.fncod f).IsVar) ∧ (∀ r : T.Eqn, (T.cod r).IsVar)

/-- `T` is *coalgebraic* if all arity terms are sorts (Definition 3.7). -/
def IsCoalgebraic : Prop :=
  (∀ f : sg.Fn, (sg.fndom f).IsVar) ∧ (∀ r : T.Eqn, (T.dom r).IsVar)

end Theory

end UlmerBialgebras
