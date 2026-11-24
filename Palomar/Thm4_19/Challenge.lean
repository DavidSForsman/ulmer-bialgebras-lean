module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.SuccPred.Nat

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 4.19

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 4.19: `UlmerBialgebras.Paper.thm_4_19`.

## How to read it

* The definitions come first, in the order in which Lean needs them, grouped by topic:
  each section heading says what the section defines. The statements come last, under
  the heading *The statements*.
* Each statement is proved by `sorry`. This is the format of a challenge: the
  matching solution file proves the same statements, and Lean's Comparator checks
  that it proves exactly these, with the axioms `propext`, `Quot.sound` and
  `Classical.choice` only.
* The docstring of each statement quotes the paper's statement, says how its notions are
  read in Lean (*Reading*), and lists the differences from the paper (*Deviations*).
* The other lemmas are stated with `sorry`: they are the properties that the definitions
  need (the proof fields of a structure, the casts along `eqToHom`). They are not claims of
  this file on their own: the solution file proves them, as part of the definitions.
* Every notion used here and not defined here is Mathlib's.

## Notation and Lean conventions

* Composition is diagrammatic: `f ≫ g` is g ∘ f and `F ⋙ G` is G ∘ F.
* `k ◁ η` and `η ▷ k` are the whiskerings of a 2-cell `η` by a 1-cell `k`, on the left and on the
  right.
* `LeftExt k d` and `RightExt k d` take `k` first and `d` second, opposite to the paper's LE(d, k)
  and RE(d, k).
* `Nonempty (IsInitial L)`, `Nonempty (RegularEpi f)`, `Nonempty (MonadicRightAdjoint U)` and the
  like turn `Type`-valued Mathlib classes into propositions; they do not weaken the claim.
* `toOne I : I ⟶ One` encodes ordinary `I`-indexed (co)limits in `Cat` as Kan extensions.
* In `Cat`, `.toFunctor` views a 1-cell as a functor, and `.toCatHom` a functor as a 1-cell.
* The `HasChosen…` instances supply chosen PIE limits.
* `s₁`, `s₂`, `s₃` are the sizes of the sorts, the function symbols and the equations.
* Universes: `Bicategory.{w, v}` on `Type u` has objects in `u`, 1-cells in `v` and 2-cells in `w`;
  `Cat.{v, u}` has objects in `u` and morphisms in `v`; `[Category.{v} C]` on `C : Type u` has
  objects in `u` and morphisms in `v`.
-/

set_option autoImplicit false

@[expose] public section

/-! The files of the formalization that the following sections come from do not import
`CategoryTheory.ReflQuiver.toQuiver` (Mathlib), so it is switched off here, and they elaborate
exactly as there. (It matters in 2-categories: with it, `⟶` between objects of a 2-category resolves
through `ReflQuiver` instead of the 2-category's own composition.) -/
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

/-! ## Colimits in a product of categories -/

section
universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {J : Type*} [Category J]

section Update

variable [DecidableEq ι]

/-- The insertion `a ↦ (x with `a` in slot `i`)`, as a functor `C i ⥤ ∀ j, C j`. -/
def updateFunctor (x : ∀ j, C j) (i : ι) : C i ⥤ (∀ j, C j) :=
  Functor.pi' fun j =>
    if h : j = i then (by subst h; exact 𝟭 (C j)) else (Functor.const (C i)).obj (x j)
end Update
end UlmerBialgebras
end

/-! ## PIE limits -/

section
open scoped CategoryTheory.Bicategory

universe u v w s

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-- A strict product of a small family of objects: the universal property is required both
for 1-cells and for 2-cells. -/
structure Product {ι : Type s} (c : ι → Obj) where
  /-- The product object. -/
  pt : Obj
  /-- The projections. -/
  π : ∀ i, pt ⟶ c i
  /-- The 1-cell induced by a family of 1-cells. -/
  lift : ∀ {x : Obj}, (∀ i, x ⟶ c i) → (x ⟶ pt)
  lift_π : ∀ {x : Obj} (g : ∀ i, x ⟶ c i) (i : ι), lift g ≫ π i = g i
  lift_uniq : ∀ {x : Obj} (h : x ⟶ pt), lift (fun i => h ≫ π i) = h
  /-- The 2-cell induced by a family of 2-cells. -/
  lift₂ : ∀ {x : Obj} {f g : x ⟶ pt}, (∀ i, (f ≫ π i) ⟶ (g ≫ π i)) → (f ⟶ g)
  lift₂_π : ∀ {x : Obj} {f g : x ⟶ pt} (α : ∀ i, (f ≫ π i) ⟶ (g ≫ π i)) (i : ι),
      (lift₂ α) ▷ π i = α i
  lift₂_uniq : ∀ {x : Obj} {f g : x ⟶ pt} (β : f ⟶ g), lift₂ (fun i => β ▷ π i) = β

variable [Bicategory.Strict Obj]

/-- Associativity helper for the universal property of an inserter. -/
lemma inserter_assoc_comp {a b pt x : Obj} {k : x ⟶ pt} {u : pt ⟶ a} {h : x ⟶ a}
    (hu : k ≫ u = h) (f : a ⟶ b) : k ≫ (u ≫ f) = h ≫ f := sorry

/-- A strict inserter of a parallel pair of 1-cells, with both universal properties. -/
structure Inserter {a b : Obj} (f g : a ⟶ b) where
  /-- The inserter object. -/
  pt : Obj
  /-- The canonical 1-cell out of the inserter. -/
  u : pt ⟶ a
  /-- The universal 2-cell. -/
  φ : u ≫ f ⟶ u ≫ g
  /-- The 1-cell induced by `h` together with a 2-cell `h ≫ f ⟶ h ≫ g`. -/
  lift : ∀ {x : Obj} (h : x ⟶ a), (h ≫ f ⟶ h ≫ g) → (x ⟶ pt)
  /-- The induced 1-cell followed by `u` is `h`. -/
  lift_u : ∀ {x : Obj} (h : x ⟶ a) (α : h ≫ f ⟶ h ≫ g), lift h α ≫ u = h
  /-- Whiskering `φ` by the induced 1-cell gives `α`, up to the associativity casts. -/
  lift_φ : ∀ {x : Obj} (h : x ⟶ a) (α : h ≫ f ⟶ h ≫ g),
      (lift h α) ◁ φ
        = eqToHom (inserter_assoc_comp (lift_u h α) f) ≫ α ≫
            eqToHom (inserter_assoc_comp (lift_u h α) g).symm
  /-- The induced 1-cell is the only one with these two properties. -/
  lift_uniq : ∀ {x : Obj} (k : x ⟶ pt) (h : x ⟶ a) (α : h ≫ f ⟶ h ≫ g),
      (hu : k ≫ u = h) →
      (k ◁ φ = eqToHom (inserter_assoc_comp hu f) ≫ α ≫
        eqToHom (inserter_assoc_comp hu g).symm) →
      k = lift h α
  /-- The 2-dimensional universal property. -/
  lift₂ : ∀ {x : Obj} {k₁ k₂ : x ⟶ pt} (α : k₁ ≫ u ⟶ k₂ ≫ u),
      ((eqToHom (Category.assoc k₁ u f) ≫ (k₁ ◁ φ) ≫ eqToHom (Category.assoc k₁ u g).symm) ≫ (α ▷ g)
        = (α ▷ f) ≫ (eqToHom (Category.assoc k₂ u f) ≫ (k₂ ◁ φ) ≫
          eqToHom (Category.assoc k₂ u g).symm)) →
      (k₁ ⟶ k₂)
  /-- Whiskering the induced 2-cell by `u` gives `α`. -/
  lift₂_u : ∀ {x : Obj} {k₁ k₂ : x ⟶ pt} (α : k₁ ≫ u ⟶ k₂ ≫ u) (h), (lift₂ α h) ▷ u = α
  /-- A 2-cell into the inserter is determined by its whiskering by `u`. -/
  lift₂_uniq : ∀ {x : Obj} {k₁ k₂ : x ⟶ pt} (β γ : k₁ ⟶ k₂), β ▷ u = γ ▷ u → β = γ

/-- A strict equifier of a parallel pair of 2-cells, with both universal properties. -/
structure Equifier {a b : Obj} {f g : a ⟶ b} (η θ : f ⟶ g) where
  /-- The equifier object. -/
  pt : Obj
  /-- The canonical 1-cell out of the equifier. -/
  e : pt ⟶ a
  /-- `e` equifies `η` and `θ`. -/
  cond : e ◁ η = e ◁ θ
  /-- The 1-cell induced by a 1-cell equifying `η` and `θ`. -/
  lift : ∀ {x : Obj} (h : x ⟶ a), (h ◁ η = h ◁ θ) → (x ⟶ pt)
  /-- The induced 1-cell followed by `e` is `h`. -/
  lift_e : ∀ {x : Obj} (h : x ⟶ a) (H : h ◁ η = h ◁ θ), lift h H ≫ e = h
  /-- The induced 1-cell is the only 1-cell `k` with `k ≫ e = h`. -/
  lift_uniq : ∀ {x : Obj} (k : x ⟶ pt) (h : x ⟶ a) (H : h ◁ η = h ◁ θ),
      k ≫ e = h → k = lift h H
  /-- Whiskering with `e`, `(-) ▷ e`, is full. -/
  full : ∀ {x : Obj} {k₁ k₂ : x ⟶ pt} (β : k₁ ≫ e ⟶ k₂ ≫ e), ∃ α : k₁ ⟶ k₂, α ▷ e = β
  /-- Whiskering with `e`, `(-) ▷ e`, is faithful. -/
  faithful : ∀ {x : Obj} {k₁ k₂ : x ⟶ pt} (α β : k₁ ⟶ k₂), α ▷ e = β ▷ e → α = β

/-- A 2-category with chosen strict products of the finite families `Fin n → Obj`. This is what
a Σ-model needs (Definition 3.8 of [forsman2026syntactic]): the arities of functor symbols and the
contexts of transformation symbols are finite. -/
class HasChosenFinProducts (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] where
  /-- Chosen products of finite families. -/
  finProd : ∀ {n : ℕ} (c : Fin n → Obj), Product c

/-- A 2-category with chosen strict inserters. -/
class HasChosenInserters (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] where
  /-- Chosen inserters. -/
  ins : ∀ {a b : Obj} (f g : a ⟶ b), Inserter f g

/-- A 2-category with chosen strict equifiers. -/
class HasChosenEquifiers (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] where
  /-- Chosen equifiers. -/
  equif : ∀ {a b : Obj} {f g : a ⟶ b} (η θ : f ⟶ g), Equifier η θ

/-- Chosen products indexed by types of universe `s`. With `HasChosenInserters` and
`HasChosenEquifiers`, this is the completeness the objects `M^σ` and `M^T` need for signatures
whose symbols live in universe `s'`. The size `s'` is an input of instance search, and the first
universe argument, so that `HasChosenProductsOfSize.{s'} Obj` names it. -/
@[univ_out_params]
class HasChosenProductsOfSize.{s', u', v', w'} (Obj : Type u') [Bicategory.{w',
  v'} Obj] [Bicategory.Strict Obj] where
  /-- Chosen products indexed by `Type s'`. -/
  prod : ∀ {ι : Type s'} (c : ι → Obj), Product c
end UlmerBialgebras
end

/-! ## `CAT` as a strict 2-category -/

section
universe v u

namespace UlmerBialgebras

open CategoryTheory

/-! ### The terminal category -/

/-- The underlying type of the terminal category: one object. -/
inductive OneObj : Type u
  | /-- The unique object. -/ star

/-- The terminal category structure on `OneObj`: a single morphism between any two objects. -/
instance : Category.{v} OneObj.{u} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- The terminal category, as an object of `CAT`. -/
def One : Cat.{v, u} := Cat.of OneObj.{u}

/-- The unique object of the terminal category. -/
abbrev One.star : One.{v, u} := OneObj.star
end UlmerBialgebras
end

/-! ## Syntax: signature pairs, terms and the term graph -/

section
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
end UlmerBialgebras
end

/-! ## Semantics: Σ-models and the interpretation of terms -/

section
open scoped CategoryTheory.Bicategory

universe u v w uᵥ u𝓌

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]

/-- The part of a Σ-model given by the interpretation of category and functor symbols. -/
structure PreModel (Sg : TwoSig) (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    [HasChosenFinProducts.{u, v, w} Obj] where
  /-- The object interpreting a category symbol. -/
  obj : Sg.Cat → Obj
  /-- The 1-cell interpreting a functor symbol, defined on the product of its arity. -/
  fn : ∀ B : Sg.Fun,
    (HasChosenFinProducts.finProd (fun i => obj (Sg.art B i))).pt ⟶ obj (Sg.fcod B)

namespace PreModel

variable {Sg : TwoSig} (M : PreModel Sg Obj)

/-- The chosen product of the arity of a functor symbol. -/
abbrev P (B : Sg.Fun) : Product (fun i => M.obj (Sg.art B i)) := HasChosenFinProducts.finProd _

/-- The chosen product of the context of a transformation symbol. -/
abbrev Pctx (a : Sg.Tr) : Product (fun i => M.obj (Sg.trt a i)) := HasChosenFinProducts.finProd _

/-- The interpretation of a term in an environment `ρ`. -/
@[implicit_reducible]
def interp {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v)) :
    ∀ {c : Sg.Cat}, Trm Sg.toFunSig vty c → (x ⟶ M.obj c)
  | _, .var v => ρ v
  | _, .app B args => (M.P B).lift (fun i => interp ρ (args i)) ≫ M.fn B

/-- The semantic substitution lemma: the first factorization of **Lemma 3.18**
([forsman2026syntactic]). -/
lemma interp_subst {V : Type uᵥ} {W : Type u𝓌} {vty : V → Sg.Cat} {wty : W → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (wty v)) (sub : ∀ v : V, Trm Sg.toFunSig wty (vty v))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interp ρ (t.subst sub) = M.interp (fun v => M.interp ρ (sub v)) t := sorry

/-- The image under a functor symbol `B` of a family of 2-cells between its arguments. -/
def appCell (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) :
    ((M.P B).lift g ≫ M.fn B) ⟶ ((M.P B).lift g' ≫ M.fn B) :=
  ((M.P B).lift₂ (fun i => eqToHom ((M.P B).lift_π g i) ≫ γ i ≫
    eqToHom ((M.P B).lift_π g' i).symm)) ▷ M.fn B
end PreModel

/-- A Σ-model in a 2-category with chosen finite products (**Definition 3.8**,
[forsman2026syntactic]; the paper works in a PIE-complete 2-category, but a model only uses the
finite products of its arities and contexts). The 2-cell interpreting a transformation symbol is
taken at the generic environment, i.e. at the projections of the product `M_x̄` over the context
`x̄` of the symbol. -/
structure Model (Sg : TwoSig) (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    [HasChosenFinProducts.{u, v, w} Obj] extends PreModel Sg Obj where
  /-- The 2-cell interpreting a transformation symbol. -/
  tr : ∀ a : Sg.Tr,
    toPreModel.interp (toPreModel.Pctx a).π (Sg.trsrc a) ⟶
      toPreModel.interp (toPreModel.Pctx a).π (Sg.trtgt a)

namespace Model

variable {Sg : TwoSig} (M : Model Sg Obj)

/-- The lift of an environment into the context product is compatible with the
interpretation. -/
lemma interp_lift_ctx (a : Sg.Tr) {x : Obj} (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i))
    {c : Sg.Cat} (t : Trm Sg.toFunSig (Sg.trt a) c) :
    M.interp ρ t = (M.Pctx a).lift ρ ≫ M.interp (M.Pctx a).π t := sorry

/-- The 2-cell interpreting a transformation symbol, at an arbitrary environment. -/
def trAt (a : Sg.Tr) {x : Obj} (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) :
    M.interp ρ (Sg.trsrc a) ⟶ M.interp ρ (Sg.trtgt a) :=
  eqToHom (M.interp_lift_ctx a ρ (Sg.trsrc a)) ≫ ((M.Pctx a).lift ρ ◁ M.tr a) ≫
    eqToHom (M.interp_lift_ctx a ρ (Sg.trtgt a)).symm
end Model
end UlmerBialgebras
end

/-! ## The objects `M^σ` of operations and `M^T` of bialgebras -/

section
open scoped CategoryTheory.Bicategory

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

/-! ### Evaluation of the term graph

`arrCellAlg` and `pathCellAlg` evaluate the arrows and the paths of the term graph at an
environment and a choice of 2-cells for the function symbols. -/

section Eval

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

omit [Bicategory Obj] [Bicategory.Strict Obj] [HasChosenFinProducts Obj] in
/-- Equality helper for off-coordinate terms in `arrCellAlg` and `arrCell`. -/
lemma arrCell_ne_eq {α : Type*} {B : Sg.Fun} {i : Fin (Sg.arn B)}
    {args args' : ∀ j, sg.CTrm (Sg.art B j)} (hne : ∀ j ≠ i, args j = args' j)
    (j : Fin (Sg.arn B)) (hj : j ≠ i) (F : sg.CTrm (Sg.art B j) → α) :
    F (args j) = F (args' j) := by
  rw [hne j hj]

/-- The evaluation of an arrow of the term graph at an environment `ρ : ∀ s, a ⟶ M_{c_s}` and a
choice of 2-cells `ψ f : M(t₁)(ρ) ⟶ M(t₂)(ρ)` for the function symbols `f : t₁ → t₂`. On `M^σ`,
with the inserter 2-cells, it is `Model.arrCellOf`. -/
def arrCellAlg {a : Obj} (ρ : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f)) :
    ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Arr t t' → (M.interp ρ t ⟶ M.interp ρ t')
  | _, _, _, .fn f => ψ f
  | _, _, _, .tr a sub =>
      eqToHom (M.toPreModel.interp_subst ρ sub (Sg.trsrc a)) ≫
        M.trAt a (fun i => M.interp ρ (sub i)) ≫
        eqToHom (M.toPreModel.interp_subst ρ sub (Sg.trtgt a)).symm
  | _, _, _, .app B i args args' hne g =>
      M.appCell B (fun j => if hj : j = i then
          cast (congrArg (fun k => (M.interp ρ (args k) ⟶ M.interp ρ (args' k))) hj.symm)
            (arrCellAlg ρ ψ g)
        else eqToHom (arrCell_ne_eq sg hne j hj (M.interp ρ)))

/-- The evaluation of a path of the term graph at an environment and a choice of 2-cells for the
function symbols (see `Model.arrCellAlg`). -/
def pathCellAlg {a : Obj} (ρ : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f)) :
    ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Path t t' → (M.interp ρ t ⟶ M.interp ρ t')
  | _, _, _, .nil _ => 𝟙 _
  | _, _, _, .cons g p => M.arrCellAlg sg ρ ψ g ≫ pathCellAlg ρ ψ p
end Eval

/-! ### `M^σ` and `M^T` at the chosen limits of `K` -/

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-- The object `M₀ = ∏_{s ∈ S} M_{c_s}`. -/
abbrev P0 : Product (fun s : sg.Srt => M.obj (sg.sty s)) :=
    HasChosenProductsOfSize.prod (ι := sg.Srt) _

/-- The 1-cell `M(t) : M₀ → M_c` attached to a closed term. -/
@[implicit_reducible]
def tm {c : Sg.Cat} (t : sg.CTrm c) : (M.P0 sg).pt ⟶ M.obj c := M.interp (M.P0 sg).π t

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- The product `∏_{f} M_{c_f}` over the function symbols of `σ`. -/
abbrev Pfn : Product (fun f : sg.Fn => M.obj (sg.fnty f)) :=
    HasChosenProductsOfSize.prod (ι := sg.Fn) _

/-- The 1-cell `(M(t₁))_f : M₀ → ∏_f M_{c_f}` of arities. -/
@[implicit_reducible]
def domCell : (M.P0 sg).pt ⟶ (M.Pfn sg).pt := (M.Pfn sg).lift (fun f => M.tm sg (sg.fndom f))

/-- The 1-cell `(M(t₂))_f : M₀ → ∏_f M_{c_f}` of coarities. -/
@[implicit_reducible]
def codCell : (M.P0 sg).pt ⟶ (M.Pfn sg).pt := (M.Pfn sg).lift (fun f => M.tm sg (sg.fncod f))

variable [HasChosenInserters.{u, v, w} Obj]

/-- The inserter defining the object of operations `M^σ` (Definition 3.13). -/
@[implicit_reducible]
def sigIns : Inserter (M.domCell sg) (M.codCell sg) := HasChosenInserters.ins _ _

/-- The object `M^σ` of operations. -/
abbrev sigObj : Obj := (M.sigIns sg).pt

/-- The canonical 1-cell `u_M : M^σ → M₀`. -/
abbrev u : M.sigObj sg ⟶ (M.P0 sg).pt := (M.sigIns sg).u

/-- The environment `s ↦ u_M ≫ π_s` used to interpret terms over `M^σ`. -/
abbrev sigEnv (s : sg.Srt) : M.sigObj sg ⟶ M.obj (sg.sty s) := M.u sg ≫ (M.P0 sg).π s

/-- The 1-cell `M^σ(t) = M(t) ∘ u_M`. -/
@[implicit_reducible]
def sigTm {c : Sg.Cat} (t : sg.CTrm c) : M.sigObj sg ⟶ M.obj c := M.interp (M.sigEnv sg) t

/-- The evaluation `M^σ(fndom f)` of the domain of `f` is `(u_M ≫ domCell) ≫ π_f`. -/
lemma sigTm_fndom (f : sg.Fn) :
    M.sigTm sg (sg.fndom f) = (M.u sg ≫ M.domCell sg) ≫ (M.Pfn sg).π f := sorry

/-- The evaluation `M^σ(fncod f)` of the codomain of `f` is `(u_M ≫ codCell) ≫ π_f`. -/
lemma sigTm_fncod (f : sg.Fn) :
    M.sigTm sg (sg.fncod f) = (M.u sg ≫ M.codCell sg) ≫ (M.Pfn sg).π f := sorry

/-- Substitution lemma for `M^σ(-)`: evaluating `t[sub]` on `M^σ` is interpreting `t` in the
environment `v ↦ M^σ(sub v)` (cf. Lemma 3.18 of [forsman2026syntactic]). -/
lemma sigTm_subst {V : Type uᵥ} {vty : V → Sg.Cat} {c : Sg.Cat} (t : Trm Sg.toFunSig vty c)
    (sub : ∀ v : V, sg.CTrm (vty v)) :
    M.sigTm sg (t.subst sub) = M.interp (fun v => M.sigTm sg (sub v)) t := sorry

/-- The evaluation `p̄_M` of an arrow of the term graph (Definition 3.14). -/
def arrCell : ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Arr t t' → (M.sigTm sg t ⟶ M.sigTm sg t')
  | _, _, _, .fn f =>
      eqToHom (M.sigTm_fndom sg f) ≫ ((M.sigIns sg).φ ▷ (M.Pfn sg).π f) ≫
        eqToHom (M.sigTm_fncod sg f).symm
  | _, _, _, .tr a sub =>
      eqToHom (M.sigTm_subst sg (Sg.trsrc a) sub) ≫
        M.trAt a (fun i => M.sigTm sg (sub i)) ≫
        eqToHom (M.sigTm_subst sg (Sg.trtgt a) sub).symm
  | _, _, _, .app B i args args' hne g =>
      M.appCell B (fun j => if hj : j = i then
          cast (congrArg (fun k => (M.sigTm sg (args k) ⟶ M.sigTm sg (args' k))) hj.symm)
            (arrCell g)
        else eqToHom (arrCell_ne_eq sg hne j hj (M.sigTm sg)))

/-- The evaluation `p̄_M` of a path of the term graph (Definition 3.14). -/
def pathCell : ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Path t t' → (M.sigTm sg t ⟶ M.sigTm sg t')
  | _, _, _, .nil _ => 𝟙 _
  | _, _, _, .cons g p => M.arrCell sg g ≫ pathCell p

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- The product `∏_{(p,q)} M_c` over the equations of the theory. -/
abbrev Peq : Product (fun r : T.Eqn => M.obj (T.eqty r)) :=
    HasChosenProductsOfSize.prod (ι := T.Eqn) _

/-- The 2-cell `(p̄_M)_{(p,q)}` given by the left-hand sides of the equations. -/
def lhsCell : ((M.Peq sg T).lift (fun r => M.sigTm sg (T.dom r))) ⟶
    ((M.Peq sg T).lift (fun r => M.sigTm sg (T.cod r))) :=
  (M.Peq sg T).lift₂ (fun r =>
    eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.dom r)) r) ≫
      M.pathCell sg (T.lhs r) ≫
      eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.cod r)) r).symm)

/-- The 2-cell `(q̄_M)_{(p,q)}` given by the right-hand sides of the equations. -/
def rhsCell : ((M.Peq sg T).lift (fun r => M.sigTm sg (T.dom r))) ⟶
    ((M.Peq sg T).lift (fun r => M.sigTm sg (T.cod r))) :=
  (M.Peq sg T).lift₂ (fun r =>
    eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.dom r)) r) ≫
      M.pathCell sg (T.rhs r) ≫
      eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.cod r)) r).symm)

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- The equifier defining the object `M^T` of `T`-bialgebras (Definition 3.14). -/
def thyEquif : Equifier (M.lhsCell sg T) (M.rhsCell sg T) := HasChosenEquifiers.equif _ _

/-- The object `M^T` of `T`-bialgebras. -/
abbrev thyObj : Obj := (M.thyEquif sg T).pt

/-- The canonical 1-cell `e_M : M^T → M^σ`. -/
abbrev e : M.thyObj sg T ⟶ M.sigObj sg := (M.thyEquif sg T).e
end Model
end UlmerBialgebras
end

/-! ## Internal limits: Kan extensions and their lifting along PIE limits -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-! ### Definition 4.3 -/

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor **strictly creates initial objects**: every initial object of the target has
a unique preimage, and that preimage is initial. -/
def StrictlyCreatesInitial (F : A ⥤ B) : Prop :=
  ∀ b : B, Nonempty (Limits.IsInitial b) →
    (∃! a : A, F.obj a = b) ∧ ∀ a : A, F.obj a = b → Nonempty (Limits.IsInitial a)

section Extensions

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-! ### Definition 4.2: categories of extensions -/

/-- A left extension of `d` along `k`: a 1-cell `l` together with a 2-cell `d ⟹ k l`; Mathlib's
`Bicategory.LeftExtension k d`. -/
abbrev LeftExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.LeftExtension k d

/-- The left extension given by a 1-cell `l` and a 2-cell `d ⟹ k l`. -/
abbrev LeftExt.mk {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (ext : X ⟶ c) (unit : d ⟶ k ≫ ext) :
    LeftExt k d := Bicategory.LeftExtension.mk ext unit

/-- The extending 1-cell of a left extension. -/
abbrev LeftExt.ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) : X ⟶ c :=
  Bicategory.LeftExtension.extension L

/-- The comparison 2-cell of a left extension. -/
abbrev LeftExt.unit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) : d ⟶ k ≫ L.ext :=
  Bicategory.LeftExtension.unit L

/-! ### The interface of morphisms of extensions

The category of left extensions is Mathlib's `StructuredArrow d (precomp _ k)`, and that of right
extensions is `CostructuredArrow (precomp _ k) d`. The library uses them only through the 2-cell of
a morphism, its compatibility with the comparison 2-cells, the morphism given by a compatible
2-cell, and extensionality. -/

namespace LeftExt

variable {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' L'' : LeftExt k d}

/-- The 2-cell `L.ext ⟶ L'.ext` of a morphism of left extensions. -/
abbrev homCell (α : L ⟶ L') : L.ext ⟶ L'.ext := α.right

/-- The morphism of left extensions given by a compatible 2-cell. -/
abbrev homMk (η : L.ext ⟶ L'.ext) (w : L.unit ≫ k ◁ η = L'.unit) : L ⟶ L' :=
  Bicategory.LeftExtension.homMk η w

/-- Morphisms of left extensions are equal when their 2-cells are. -/
@[ext] lemma hom_ext {α β : L ⟶ L'} (h : homCell α = homCell β) : α = β := sorry
end LeftExt
end Extensions

section TwoCat

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Post-composing a morphism of left extensions with `f` is compatible with the comparison
2-cells of the post-composed extensions. -/
lemma LeftExt.push_w {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') {L L' : LeftExt k d}
    (a : L ⟶ L') :
    ((L.unit ▷ f) ≫ eqToHom (Category.assoc k L.ext f)) ≫ k ◁ (LeftExt.homCell a ▷ f) =
      (L'.unit ▷ f) ≫ eqToHom (Category.assoc k L'.ext f) := sorry

/-- Post-composition with a 1-cell `f : c ⟶ c'`, as a functor between categories of left
extensions.  This is the functor `f∗` of Definition 4.4. -/
@[implicit_reducible]
def LeftExt.push {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') :
    LeftExt k d ⥤ LeftExt k (d ≫ f) where
  obj L := LeftExt.mk (L.ext ≫ f) ((L.unit ▷ f) ≫ eqToHom (Category.assoc k L.ext f))
  map a := LeftExt.homMk (LeftExt.homCell a ▷ f) (LeftExt.push_w k d f a)
  map_id L := LeftExt.hom_ext (Bicategory.id_whiskerRight L.ext f)
  map_comp _ _ := LeftExt.hom_ext (Bicategory.comp_whiskerRight _ _ f)

/-! ### Definition 4.4 -/

variable {I X c c' : Obj}

/-- `f` strictly creates the left Kan extensions of `d` along `k`. -/
def StrictlyCreatesLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  StrictlyCreatesInitial (LeftExt.push k d f)
end TwoCat
end UlmerBialgebras
end

/-! The files that the following sections come from import `CategoryTheory.ReflQuiver.toQuiver`
(Mathlib), so it is switched back on. -/
attribute [instance 1000] CategoryTheory.ReflQuiver.toQuiver

/-! ## `CAT` is PIE-complete -/

section
universe u v s

namespace UlmerBialgebras

open CategoryTheory
open scoped Bicategory

/-! ### Products -/

/-- A family of categories indexed in universe `s` has a strict product in CAT: the category of
families, in `Cat.{max s v, max s u}`. The lifts are taken componentwise. -/
def catProduct {ι : Type s} (c : ι → Cat.{max s v, max s u}) : Product c where
  pt := Cat.of (∀ i, (c i : Type (max s u)))
  π i := (Pi.eval _ i).toCatHom
  lift g := (Functor.pi' (fun i => (g i).toFunctor)).toCatHom
  lift_π _ _ := rfl
  lift_uniq _ := rfl
  -- Keep the components visible at reducible transparency for the concrete theory models.
  lift₂ {_ _ _} α :=
    { toNatTrans := {
        app := fun p i => (α i).toNatTrans.app p
        naturality := (NatTrans.pi' fun i => (α i).toNatTrans).naturality } }
  lift₂_π _ _ := rfl
  lift₂_uniq _ := rfl

section
end

/-- **Finite products in `CAT`**: `Cat.{v, u}` has the strict products of finite families, for
independent `u` and `v` (the product of a family indexed by `Fin n` stays in `Cat.{v, u}`). At
`Cat.{v, max u v}` this is the finite-products parent of `catPIEComplete`, up to unfolding. -/
instance catHasChosenFinProducts : HasChosenFinProducts Cat.{v, u} where
  finProd c := catProduct (ι := Fin _) c
end UlmerBialgebras
end

/-! ## Supports and Kan creation for theory objects -/

section
universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-! ### Kan creation for theory objects -/

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]
variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- The forgetful 1-cell `u : M^T → M₀`. -/
abbrev thyForget : M.thyObj sg T ⟶ (M.P0 sg).pt := M.e sg T ≫ M.u sg
end Model
end UlmerBialgebras
end

/-! ## Colimits as left Kan extensions along `I → 1` -/

section
universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

/-- The unique functor from a category to the terminal category. -/
def toOne (I : Cat.{v, u}) : I ⟶ One.{v, u} :=
  (Functor.const I).obj One.star |>.toCatHom
end UlmerBialgebras
end

/-! ## Definitions: `PreservesWidePushoutsOfRegEpis`, `RegEpisAreReflexiveCoequalizers` -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- A functor **preserves `K`-indexed wide pushouts of regular epimorphisms**
(Corollary 4.18 and Theorem 4.19 of [forsman2026syntactic]). -/
def PreservesWidePushoutsOfRegEpis (K : Type w) {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) : Prop :=
  ∀ dg : WidePushoutShape K ⥤ C,
    (∀ j, Nonempty (RegularEpi (dg.map (WidePushoutShape.Hom.init j)))) → PreservesColimit dg F

/-- Every regular epimorphism is the coequalizer of a reflexive pair. -/
def RegEpisAreReflexiveCoequalizers (C : Type u) [Category.{v} C] : Prop :=
  ∀ ⦃a b : C⦄ (f : a ⟶ b), Nonempty (RegularEpi f) →
    ∃ (r : C) (g h : r ⟶ a) (_ : IsReflexivePair g h) (w : g ≫ f = h ≫ f),
      Nonempty (IsColimit (Cofork.ofπ f w))
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 4 (lifting limits and colimits) -/

section
universe u v w uu₁ uu₂ uu₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ### Sifted colimits and wide pushouts of regular epimorphisms -/

section Sifted

/-- **Theorem 4.19** ([forsman2026syntactic], §4).

```latex
Let $(\Sigma,\sigma)$ be a signature pair,  $T$ a $\sigma$-theory, $M$ a $\Sigma$-model in $\CAT$,
and $I$ a set with cardinality at least $2$. Assume in each category $M_c$ regular epimorphisms are
reflexive coequalizers and each functor $M(B)$ preserves $I$-indexed wide pushouts of regular epis
componentwise. Let $f_i\colon a\to b_i$ be morphisms in $M^T$ such that $Uf_i$ is a regular
epimorphism for each $i\in I$. Then the forgetful functor $U\colon M^T\to M_0$ strictly creates the
$I$-indexed pushout of $(f_i)_{i\in I}$.
```

**Reading.**
* "cardinality at least 2", the wide pushout ↦ `(K : Type w) [Nontrivial K]` and
  `e : WidePushoutShape K ≌ (J : Type u)`, so the size of `K` is free.
* "$Uf_i$ is a regular epimorphism" ↦ `hd`, on the legs of `d` under `U = M.thyForget sg T`.
* "strictly creates the wide pushout" ↦ `StrictlyCreatesLeftKan (toOne J) d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem thm_4_19 [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Cat.{v, u})
    (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] (K : Type w) [Nontrivial K]
    (hreg : ∀ c : Sg.Cat, RegEpisAreReflexiveCoequalizers (M.obj c : Type u))
    (hB : ∀ (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
      PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙
        (M.fn B).toFunctor))
    (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u))
    (d : J ⟶ M.thyObj sg T)
    (hd : ∀ j, Nonempty (RegularEpi ((d ≫ M.thyForget sg T).toFunctor.map
        (e.functor.map (WidePushoutShape.Hom.init j))))) :
    StrictlyCreatesLeftKan (toOne J) d (M.thyForget sg T) := sorry
end Sifted
end UlmerBialgebras.Paper
end
