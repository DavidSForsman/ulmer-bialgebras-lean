module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 5.5

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 5.5: `UlmerBialgebras.Paper.thm_5_5_1`, `UlmerBialgebras.Paper.thm_5_5_2`.

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
* Every notion used here and not defined here is Mathlib's.

## Notation and Lean conventions

* Composition is diagrammatic: `f ≫ g` is g ∘ f and `F ⋙ G` is G ∘ F.
* `Nonempty (IsInitial L)`, `Nonempty (RegularEpi f)`, `Nonempty (MonadicRightAdjoint U)` and the
  like turn `Type`-valued Mathlib classes into propositions; they do not weaken the claim.
* `κ.ord.ToType` is the initial ordinal of the cardinal `κ`, as a well-ordered type; a `κ`-chain is
  a functor out of it.
* Universes: `[Category.{v} C]` on `C : Type u` has objects in `u` and morphisms in `v`.
-/

set_option autoImplicit false

@[expose] public section

/-! ## Inserter and equifier categories -/

section
universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-! ### The inserter category -/

/-- The inserter of a parallel pair of functors `F, G : C ⥤ D`: objects are pairs of an
object `x` of `C` and a morphism `F x ⟶ G x`. -/
structure Ins (F G : C ⥤ D) where
  /-- The underlying object of `C`. -/
  pt : C
  /-- The structure morphism. -/
  cell : F.obj pt ⟶ G.obj pt

namespace Ins

variable {F G : C ⥤ D}

/-- A morphism in the inserter category: a morphism of the underlying objects compatible
with the structure morphisms. -/
@[ext]
structure Hom (x y : Ins F G) where
  /-- The underlying morphism of `C`. -/
  base : x.pt ⟶ y.pt
  /-- Compatibility with the structure morphisms. -/
  w : x.cell ≫ G.map base = F.map base ≫ y.cell

/-- The category structure on the inserter: composition and identities are those of `C`. -/
instance : Category (Ins F G) where
  Hom x y := Hom x y
  id x := ⟨𝟙 x.pt, by simp⟩
  comp {x y z} f g :=
    ⟨f.base ≫ g.base, by
      rw [F.map_comp, G.map_comp, ← Category.assoc, f.w, Category.assoc, g.w, Category.assoc]⟩

/-- The forgetful functor from the inserter category. -/
@[simps, implicit_reducible]
def forget (F G : C ⥤ D) : Ins F G ⥤ C where
  obj x := x.pt
  map f := f.base
end Ins

/-! ### The equifier category -/

/-- The property of an object of `C` of equifying two natural transformations. -/
def equifProp {F G : C ⥤ D} (η θ : F ⟶ G) : ObjectProperty C := fun x => η.app x = θ.app x

/-- The equifier of two natural transformations `η, θ : F ⟶ G`: the full subcategory of `C`
spanned by the objects `x` with `η x = θ x`. -/
abbrev Equif {F G : C ⥤ D} (η θ : F ⟶ G) : Type u := (equifProp η θ).FullSubcategory

namespace Equif

variable {F G : C ⥤ D} {η θ : F ⟶ G}

/-- The forgetful functor from the equifier category. -/
abbrev forget (η θ : F ⟶ G) : Equif η θ ⥤ C := (equifProp η θ).ι
end Equif
end UlmerBialgebras
end

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

/-! ## Definitions: `HasChainColimitsUpTo`, `PreservesJointEpiOfShape` -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- **Definition 5.4** ([forsman2026syntactic]): `C` is `κ_≤`-cocomplete: it has colimits of
`μ`-chains for every infinite cardinal `μ ≤ κ` (a `μ`-chain is a functor out of `μ`, viewed as a
well-ordered set). -/
def HasChainColimitsUpTo (κ : Cardinal.{w}) (C : Type u) [Category.{v} C] : Prop :=
  ∀ μ : Cardinal.{w}, Cardinal.aleph0 ≤ μ → μ ≤ κ → HasColimitsOfShape μ.ord.ToType C

/-- `F` preserves the joint epicness of colimiting cocones of shape `J`. -/
def PreservesJointEpiOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cocone Kd), IsColimit c → ∀ ⦃y : D⦄ (p q : F.obj c.pt ⟶ y),
    (∀ j, F.map (c.ι.app j) ≫ p = F.map (c.ι.app j) ≫ q) → p = q
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 5: free algebras, monadicity, local presentability -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Thm55

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Theorem 5.5 (1)** ([forsman2026syntactic], §5).

```latex
Let $\kappa$ be an infinite cardinal and let $F,G\colon \C\to \D$ be functors with $\C$
$\kappa_\leq$-cocomplete. Assume that $G$ has an $F$-relative left adjoint $L$.\footnote{An
$F$-relative left adjoint $L$ for $G$ means that there is an isomorphism
$\hom(Lx,y)\cong\hom(Fx,Gy)$ natural in $x$ and $y$. If $G$ has a left adjoint $l$, then $L \cong
lF$ \cite{ulmerPropertiesDenseRelative1968}} Then the following assertions hold:
```

```latex
\item If $\C$ has finite coproducts and $F$ preserves $\kappa$-colimits, then $U\colon
\Ins(F,G)\to \C$ is monadic.
```

**Reading.**
* "$\kappa_\leq$-cocomplete" ↦ `HasChainColimitsUpTo κ C`.
* "$G$ has an $F$-relative left adjoint $L$" ↦ `ra : RelLeftAdjoint F G L`.
* "$F$ preserves $\kappa$-colimits" ↦ `PreservesColimitsOfShape κ.ord.ToType F`.
* "$U\colon \Ins(F,G)\to \C$ is monadic" ↦ `MonadicRightAdjoint (Ins.forget F G)`.

**Deviations.** none recorded.
-/
theorem thm_5_5_1 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ) (F G : C ⥤ D) (L : C ⥤ C)
    (ra : RelLeftAdjoint F G L) (hC : HasChainColimitsUpTo κ C) [HasFiniteCoproducts C]
    (hF : PreservesColimitsOfShape κ.ord.ToType F) :
    Nonempty (MonadicRightAdjoint (Ins.forget F G)) := sorry

/-- **Theorem 5.5 (2)** ([forsman2026syntactic], §5).

```latex
Let $\kappa$ be an infinite cardinal and let $F,G\colon \C\to \D$ be functors with $\C$
$\kappa_\leq$-cocomplete. Assume that $G$ has an $F$-relative left adjoint $L$.\footnote{An
$F$-relative left adjoint $L$ for $G$ means that there is an isomorphism
$\hom(Lx,y)\cong\hom(Fx,Gy)$ natural in $x$ and $y$. If $G$ has a left adjoint $l$, then $L \cong
lF$ \cite{ulmerPropertiesDenseRelative1968}} Then the following assertions hold:
```

```latex
\item Let $\alpha,\beta\colon F\Rightarrow G$ be natural transformations. If $\C$ has coequalizers
and $F$ preserves joint epicness of colimiting cocones of $\kappa$-chains, then the forgetful
functor $U\colon \Eq(\alpha,\beta)\to \C$ is monadic.
```

**Reading.**
* "$\kappa_\leq$-cocomplete" ↦ `HasChainColimitsUpTo κ C`.
* "$G$ has an $F$-relative left adjoint $L$" ↦ `ra : RelLeftAdjoint F G L`.
* "$F$ preserves joint epicness of colimiting cocones of $\kappa$-chains" ↦
  `PreservesJointEpiOfShape κ.ord.ToType F`.
* "$U\colon \Eq(\alpha,\beta)\to \C$ is monadic" ↦ `MonadicRightAdjoint (Equif.forget α β)`.

**Deviations.** none recorded.
-/
theorem thm_5_5_2 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ) (F G : C ⥤ D) (L : C ⥤ C)
    (ra : RelLeftAdjoint F G L) (α β : F ⟶ G) (hC : HasChainColimitsUpTo κ C)
    [HasCoequalizers C] (hF : PreservesJointEpiOfShape κ.ord.ToType F) :
    Nonempty (MonadicRightAdjoint (Equif.forget α β)) := sorry
end Thm55
end UlmerBialgebras.Paper
end
