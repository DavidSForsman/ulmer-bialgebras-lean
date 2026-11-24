module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 5.11

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 5.11: `UlmerBialgebras.Paper.thm_5_11`.

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

/-! ## Definitions: `PreservesJointEpiOfShape`, `PreservesJointMonoOfShape` -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- `F` preserves the joint epicness of colimiting cocones of shape `J`. -/
def PreservesJointEpiOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cocone Kd), IsColimit c → ∀ ⦃y : D⦄ (p q : F.obj c.pt ⟶ y),
    (∀ j, F.map (c.ι.app j) ≫ p = F.map (c.ι.app j) ≫ q) → p = q

/-- `F` preserves the joint monicness of limiting cones of shape `J`. -/
def PreservesJointMonoOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cone Kd), IsLimit c → ∀ ⦃y : D⦄ (p q : y ⟶ F.obj c.pt),
    (∀ j, p ≫ F.map (c.π.app j) = q ≫ F.map (c.π.app j)) → p = q
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 5: free algebras, monadicity, local presentability -/

section
universe u w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section AAFT

/-- **Theorem 5.11** ([forsman2026syntactic], §5).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$ with $\C$ locally
presentable and $F,F',G,G'$ accessible. Then $U_\B\colon \BialgB\to \C$ is accessible and the
following hold:
\begin{enumerate}
    \item If $G$ is continuous and $G'$ preserves joint monicness of limiting cones, then $\BialgB$
    is locally presentable and the forgetful functor $U_\B\colon \BialgB\to \C$ is monadic.
    \item If $F$ preserves colimiting cocones and $F'$ preserves their joint epicness, then
    $\BialgB$ is locally presentable and $U_\B$ is comonadic.
\end{enumerate}
```

**Reading.**
* bialgebraic datum in $\CAT$ ↦ `(B : BialgDatum)` at `Cat.{w, u}`: categories with morphisms
  in `Type w` and objects in any universe `Type u`.
* "$\C$ locally presentable and $F,F',G,G'$ accessible" ↦
  `IsLocallyPresentable (B.c : Type u)` and accessibility instances on functors.
* "accessible" (in the paper's sense: between accessible categories) ↦ `Functor.IsAccessible.{w}`
  on `F, G, F', G'` plus `IsAccessibleCategory.{w}` on `B.x` and `B.y` (`B.c` is locally
  presentable); Mathlib's predicate does not include the latter.
* "$U_\B$ is accessible" ↦ `IsAccessibleCategory.{w} (E.pt : Type u)` and
  `Functor.IsAccessible.{w}` for `B.uB E`, the first conjunct.
* item 1 conclusion ↦ `IsLocallyPresentable (E.pt : Type u)` and
  monadicity of the forgetful functor `B.uB E`.
* item 2 conclusion ↦ `IsLocallyPresentable (E.pt : Type u)` and
  comonadicity of the forgetful functor `B.uB E`.

**Deviations.** none recorded.
-/
theorem thm_5_11 (B : BialgDatum (Obj := Cat.{w, u})) (E : Equifier B.α B.β)
    [IsLocallyPresentable.{w} (B.c : Type u)]
    [IsAccessibleCategory.{w} (B.x : Type u)] [IsAccessibleCategory.{w} (B.y : Type u)]
    [Functor.IsAccessible.{w} (B.f).toFunctor]
    [Functor.IsAccessible.{w} (B.g).toFunctor]
    [Functor.IsAccessible.{w} (B.f').toFunctor]
    [Functor.IsAccessible.{w} (B.g').toFunctor] :
    (IsAccessibleCategory.{w} (E.pt : Type u) ∧
      Functor.IsAccessible.{w} (B.uB E).toFunctor) ∧
    ((PreservesLimitsOfSize.{w, w} (B.g).toFunctor ∧
        ∀ (J : Type w) [SmallCategory J],
          PreservesJointMonoOfShape J (B.g').toFunctor) →
      IsLocallyPresentable.{w} (E.pt : Type u) ∧
        Nonempty (MonadicRightAdjoint (B.uB E).toFunctor)) ∧
    ((PreservesColimitsOfSize.{w, w} (B.f).toFunctor ∧
        ∀ (J : Type w) [SmallCategory J],
          PreservesJointEpiOfShape J (B.f').toFunctor) →
      IsLocallyPresentable.{w} (E.pt : Type u) ∧
        Nonempty (ComonadicLeftAdjoint (B.uB E).toFunctor)) := sorry
end AAFT
end UlmerBialgebras.Paper
end
