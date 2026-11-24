module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 5.7

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 5.7: `UlmerBialgebras.Paper.thm_5_7`.

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
* `Nonempty (IsInitial L)`, `Nonempty (RegularEpi f)`, `Nonempty (MonadicRightAdjoint U)` and the
  like turn `Type`-valued Mathlib classes into propositions; they do not weaken the claim.
* In `Cat`, `.toFunctor` views a 1-cell as a functor, and `.toCatHom` a functor as a 1-cell.
* `(C : Type u)` for an object `C` of `Cat` is its type of objects, with the category structure that
  `C` carries.
* `κ.ord.ToType` is the initial ordinal of the cardinal `κ`, as a well-ordered type; a `κ`-chain is
  a functor out of it.
* Universes: `Bicategory.{w, v}` on `Type u` has objects in `u`, 1-cells in `v` and 2-cells in `w`;
  `Cat.{v, u}` has objects in `u` and morphisms in `v`; `[Category.{v} C]` on `C : Type u` has
  objects in `u` and morphisms in `v`.
* `cor_5_8`, named in a *Reading*, is a statement of the formalization's full challenge
  (the development repository's `Challenge/`) that this file does not include.
-/

set_option autoImplicit false

@[expose] public section

/-! ## Relative left adjoints -/

section
universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- An `F`-relative left adjoint of `G`: an endofunctor `L` of `C` together with a
bijection `(L x ⟶ y) ≃ (F x ⟶ G y)` natural in `x` and `y`. -/
structure RelLeftAdjoint (F G : C ⥤ D) (L : C ⥤ C) where
  /-- The transposition bijection. -/
  homEquiv (x y : C) : (L.obj x ⟶ y) ≃ (F.obj x ⟶ G.obj y)
  /-- Naturality in the first variable. -/
  homEquiv_naturality_left {x x' y : C} (f : x' ⟶ x) (g : L.obj x ⟶ y) :
    homEquiv x' y (L.map f ≫ g) = F.map f ≫ homEquiv x y g
  /-- Naturality in the second variable. -/
  homEquiv_naturality_right {x y y' : C} (g : L.obj x ⟶ y) (h : y ⟶ y') :
    homEquiv x y' (g ≫ h) = homEquiv x y g ≫ G.map h
end UlmerBialgebras
end

/-! The files of the formalization that the following sections come from do not import
`CategoryTheory.ReflQuiver.toQuiver` (Mathlib), so it is switched off here, and they elaborate
exactly as there. (It matters in 2-categories: with it, `⟶` between objects of a 2-category resolves
through `ReflQuiver` instead of the 2-category's own composition.) -/
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

/-! ## PIE limits -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj]

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
end UlmerBialgebras
end

/-! The files that the following sections come from import `CategoryTheory.ReflQuiver.toQuiver`
(Mathlib), so it is switched back on. -/
attribute [instance 1000] CategoryTheory.ReflQuiver.toQuiver

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section TwoCat

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Definition 3.1: bialgebraic data -/

/-- **Definition 3.1** ([forsman2026syntactic]; after Ulmer [Ulmer1977Bialgebras]).
A bialgebraic datum on an object `c`:
supports `f, g : c ⟶ x` and `f', g' : c ⟶ y`, the inserter `(u', φ)` of `f` and `g`, and the
equations `α, β : f' u' ⟹ g' u'` (written `u' ≫ f'` in diagrammatic order). -/
structure BialgDatum where
  /-- The base object `c`. -/
  c : Obj
  /-- The codomain of the function supports. -/
  x : Obj
  /-- The codomain of the equational supports. -/
  y : Obj
  /-- The function arity support. -/
  f : c ⟶ x
  /-- The function coarity support. -/
  g : c ⟶ x
  /-- The equational arity support. -/
  f' : c ⟶ y
  /-- The equational coarity support. -/
  g' : c ⟶ y
  /-- The object of pre-bialgebras: the inserter of `f` and `g`. -/
  ins : Inserter f g
  /-- The first equation. -/
  α : ins.u ≫ f' ⟶ ins.u ≫ g'
  /-- The second equation. -/
  β : ins.u ≫ f' ⟶ ins.u ≫ g'

/-- **Definition 3.1 (2), (3)** ([forsman2026syntactic]). An object of bialgebras of a bialgebraic
datum `B` is an equifier `E` of `α, β`; the canonical morphism `u_B : Bialg(B) → c` is `e ≫ u'`. -/
abbrev BialgDatum.uB (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) : E.pt ⟶ B.c :=
  E.e ≫ B.ins.u
end TwoCat
end UlmerBialgebras.Paper
end

/-! ## Definitions: `PreservesJointEpiOfShape`, `HasColimitsOfSizeLE` -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- `F` preserves the joint epicness of colimiting cocones of shape `J`. -/
def PreservesJointEpiOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cocone Kd), IsColimit c → ∀ ⦃y : D⦄ (p q : F.obj c.pt ⟶ y),
    (∀ j, F.map (c.ι.app j) ≫ p = F.map (c.ι.app j) ≫ q) → p = q

/-- `C` has all colimits of size at most `κ` (indexed by small categories with at most `κ`
morphisms). -/
def HasColimitsOfSizeLE (κ : Cardinal.{w}) (C : Type u) [Category.{v} C] : Prop :=
  ∀ (J : Type w) [SmallCategory J], Cardinal.mk (Σ X Y : J, X ⟶ Y) ≤ κ →
    HasColimitsOfShape J C
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 5: free algebras, monadicity, local presentability -/

section
universe u w u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Thm57

/-- **Theorem 5.7** ([forsman2026syntactic], §5).

```latex
Fix an infinite cardinal $\kappa$. Let $\B = (\C,\ F,G,\ F',G',\ \alpha, \beta)$ be a bialgebraic
datum in $\CAT$. Assume the following:
\begin{enumerate}
    \item Functors $G$ and $G'$ have $F$- and $F'$-relative left adjoints $L_1$ and $L_2$,
    respectively.
    \item The category $\C$ has colimits of size at most $\kappa$.
    \item The functor $F$ preserves the colimiting cocones of $\kappa$-chains and $F'$ their
    joint epicness.
\end{enumerate}
Then $U\colon \BialgB\to \C$ is monadic and $\BialgB$ has colimits of size at most $\kappa$.
Furthermore, if $K\xleftarrow{k} I\xrightarrow{d}\BialgB$ is a span of functors, where the left
Kan extensions of $Ud$ and $L_1Ud$ along $k$ exist, then the left Kan extension of $d$ along $k$
exists.
```

**Reading.**
* bialgebraic datum in $\CAT$ ↦ `(B : BialgDatum)` at `Cat.{w, max u w}`.
* "Functors $G$ and $G'$ have relative left adjoints" ↦ relative left adjoint hypotheses
  `r₁` and `r₂` on the component functors.
* "$\C$ has colimits of size at most $\kappa$" ↦ `HasColimitsOfSizeLE κ (B.c : Type (max u w))`.
* "$U$ is monadic and $\BialgB$ has colimits of size at most $\kappa$" ↦
  monadicity of `B.uB E` and `HasColimitsOfSizeLE κ (E.pt : Type (max u w))`.
* detection of left Kan extensions ↦ Mathlib's `k.HasLeftKanExtension`: if those of $Ud$ and
  $L_1Ud$ exist, so does that of `d`.
* "a span of functors" $K\xleftarrow{k} I\xrightarrow{d}\BialgB$ ↦ any categories
  `I : Type u₁`, `Kc : Type u₂` with `Category.{v₁} I`, `Category.{v₂} Kc`, of sizes independent of
  `CAT`'s, as in `cor_5_8`.

**Deviations.**
- different (size): in `Cat.{w, max u w}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_5_7 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ)
    (B : BialgDatum (Obj := Cat.{w, max u w})) (E : Equifier B.α B.β)
    (L₁ L₂ : (B.c : Type (max u w)) ⥤ B.c)
    (r₁ : RelLeftAdjoint (B.f).toFunctor B.g.toFunctor L₁)
    (r₂ : RelLeftAdjoint (B.f').toFunctor B.g'.toFunctor L₂)
    (hC : HasColimitsOfSizeLE κ (B.c : Type (max u w)))
    (hF : PreservesColimitsOfShape κ.ord.ToType (B.f).toFunctor)
    (hF' : PreservesJointEpiOfShape κ.ord.ToType (B.f').toFunctor) :
    Nonempty (MonadicRightAdjoint (B.uB E).toFunctor) ∧
      HasColimitsOfSizeLE κ (E.pt : Type (max u w)) ∧
      ∀ {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
        (d : I ⥤ (E.pt : Type (max u w)))
        (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ (B.uB E).toFunctor) →
          k.HasLeftKanExtension ((d ⋙ (B.uB E).toFunctor) ⋙ L₁) →
            k.HasLeftKanExtension d := sorry
end Thm57
end UlmerBialgebras.Paper
end
