module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 7.6

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 7.6: `UlmerBialgebras.Paper.thm_7_6`, `UlmerBialgebras.Paper.thm_7_6_monadic`.

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
* `κ.ord.ToType` is the initial ordinal of the cardinal `κ`, as a well-ordered type; a `κ`-chain is
  a functor out of it.
* The `IsA…` predicates are about the hom-categories `K(a, -)` for `a ∈ A`; the `IsCalA…` ones also
  ask for Kan extensions along 1-cells of `𝒜`.
* `AsBicat Obj` is a synonym for `Obj`, so that Mathlib's adjunctions in a bicategory apply.
* Universes: `Bicategory.{w, v}` on `Type u` has objects in `u`, 1-cells in `v` and 2-cells in `w`;
  `w₀` and `w₁` are diagram sizes, independent of the others.
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

/-! ## A strict 2-category as a bicategory: adjunctions and mates -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-- A type synonym for a strict 2-category, carrying the induced `Bicategory` structure. -/
abbrev AsBicat (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] : Type u := Obj

/-! ### Adjunctions -/

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- An adjunction `f ⊣ g` between 1-cells of a strict 2-category. -/
abbrev TwoAdj {a b : Obj} (f : a ⟶ b) (g : b ⟶ a) : Type w :=
  Bicategory.Adjunction (B := AsBicat.{u, v, w} Obj) f g

namespace TwoAdj

variable {a b : Obj} {f : a ⟶ b} {g : b ⟶ a}

/-- The unit of an adjunction, in the language of strict 2-categories. -/
abbrev unit' (A : TwoAdj f g) : 𝟙 a ⟶ f ≫ g := A.unit

/-- The counit of an adjunction, in the language of strict 2-categories. -/
abbrev counit' (A : TwoAdj f g) : g ≫ f ⟶ 𝟙 b := A.counit
end TwoAdj
end UlmerBialgebras
end

/-! ## Internal limits: Kan extensions and their lifting along PIE limits -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {A : Type*} [Category A] {B : Type*} [Category B]

section Extensions

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-! ### Definition 4.2: categories of extensions -/

/-- A left extension of `d` along `k`: a 1-cell `l` together with a 2-cell `d ⟹ k l`; Mathlib's
`Bicategory.LeftExtension k d`. -/
abbrev LeftExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.LeftExtension k d

/-- A right extension of `d` along `k`: a 1-cell `l` together with a 2-cell `k l ⟹ d`; Mathlib's
`Bicategory.RightExtension k d`. -/
abbrev RightExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.RightExtension k d
end Extensions
end UlmerBialgebras
end

/-! The files that the following sections come from import `CategoryTheory.ReflQuiver.toQuiver`
(Mathlib), so it is switched back on. -/
attribute [instance 1000] CategoryTheory.ReflQuiver.toQuiver

/-! ## Hom-categories of a 2-category and the representable comparison equivalences -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ### Pre- and post-composition functors -/

/-- Pre-composition with `f : x ⟶ y` as a functor `K(y, c) ⥤ K(x, c)`. -/
@[simps, implicit_reducible]
def precomp {x y : Obj} (f : x ⟶ y) (c : Obj) : (y ⟶ c) ⥤ (x ⟶ c) where
  obj h := f ≫ h
  map α := f ◁ α

/-- Post-composition with `u : c ⟶ d` as a functor `K(x, c) ⥤ K(x, d)`. -/
@[simps, implicit_reducible]
def postcomp (x : Obj) {c d : Obj} (u : c ⟶ d) : (x ⟶ c) ⥤ (x ⟶ d) where
  obj h := h ≫ u
  map α := α ▷ u

/-- Post-composition with a 2-cell `η : f ⟶ g` as a natural transformation between the
post-composition functors. -/
@[simps]
def postcompNat (x : Obj) {a b : Obj} {f g : a ⟶ b} (η : f ⟶ g) :
    postcomp x f ⟶ postcomp x g where
  app h := h ◁ η
  naturality _ _ α := Eq.symm <| Bicategory.whisker_exchange α η
end UlmerBialgebras
end

/-! ## Density of a class of objects in a 2-category -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ### Families of 2-cells -/

/-- A **family of 2-cells on the `A`-representables** from `p` to `q`: for every `x ∈ A` a
natural transformation `K(x, p) ⟶ K(x, q)`, compatible with pre-composition along the
1-cells of `K` whose source and target lie in `A`.

The compatibility is stated componentwise: at `k : y ⟶ c` and `u : x ⟶ y` it says that
whiskering the component at `k` by `u` is the component at `u ≫ k`, modulo associativity. -/
structure ACellFamily (A : ObjectProperty Obj) {c d : Obj} (p q : c ⟶ d) where
  /-- The component at an object of `A`. -/
  app : ∀ ⦃x : Obj⦄, A x → (postcomp x p ⟶ postcomp x q)
  /-- Compatibility with pre-composition. -/
  naturality : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ c),
    u ◁ ((app hy).app k)
      = eqToHom (Category.assoc u k p).symm ≫ (app hx).app (u ≫ k) ≫ eqToHom (Category.assoc u k q)

/-- **The local half of density**: a 2-cell of `K` is the same thing as a compatible family
of 2-cells on the `A`-representables. -/
def IsACellDense (A : ObjectProperty Obj) : Prop :=
  ∀ ⦃c d : Obj⦄ ⦃p q : c ⟶ d⦄ (Φ : ACellFamily A p q),
    ∃! α : p ⟶ q, ∀ ⦃x : Obj⦄ (hx : A x), postcompNat x α = Φ.app hx

/-! ### Pseudonatural families of functors -/

/-- A **pseudonatural family of functors** on the `A`-representables from `d` to `c`: for
every `x ∈ A` a functor `K(x, d) ⥤ K(x, c)`, together with comparison isomorphisms with
pre-composition, subject to the unit and cocycle conditions.

This is written out componentwise. It carries the 1-cell comparison isomorphisms and their
coherence laws, but not the 2-cell axiom of a genuine pseudonatural transformation:
`UlmerBialgebras.Paper.PsFamily` (Definition 7.1) extends it with that axiom, `nat₂`, and the
definition of bi-density uses `PsFamily`. -/
structure AHomFamily (A : ObjectProperty Obj) (d c : Obj) where
  /-- The functor at an object of `A`. -/
  fn : ∀ ⦃x : Obj⦄, A x → ((x ⟶ d) ⥤ (x ⟶ c))
  /-- The comparison isomorphism for pre-composition along `u : x ⟶ y`. -/
  nat : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y),
    precomp u d ⋙ fn hx ≅ fn hy ⋙ precomp u c
  /-- The comparison for an identity is the identity. -/
  nat_id : ∀ ⦃x : Obj⦄ (hx : A x) (k : x ⟶ d),
    (nat hx hx (𝟙 x)).hom.app k
      = eqToHom (by simp only [Functor.comp_obj, precomp_obj, Category.id_comp])
  /-- The comparisons compose. -/
  nat_comp : ∀ ⦃x y z : Obj⦄ (hx : A x) (hy : A y) (hz : A z) (u : x ⟶ y) (v : y ⟶ z)
      (k : z ⟶ d),
    (nat hx hz (u ≫ v)).hom.app k
      = eqToHom (by simp only [Functor.comp_obj, precomp_obj, Category.assoc]) ≫
          (nat hx hy u).hom.app (v ≫ k) ≫
          (u ◁ (nat hy hz v).hom.app k) ≫ eqToHom (Category.assoc u v ((fn hz).obj k)).symm

namespace AHomFamily

variable {A : ObjectProperty Obj} {d c : Obj}

/-- A **representation** of a pseudonatural family: a 1-cell of `K` inducing it. -/
structure Representation (G : AHomFamily A d c) where
  /-- The representing 1-cell. -/
  g : d ⟶ c
  /-- The comparison of the family with post-composition by `g`. -/
  iso : ∀ ⦃x : Obj⦄ (hx : A x), postcomp x g ≅ G.fn hx
  /-- The comparison is compatible with the pseudonaturality isomorphisms. -/
  iso_nat : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d),
    (iso hx).hom.app (u ≫ k) ≫ (G.nat hx hy u).hom.app k
      = eqToHom (Category.assoc u k g) ≫ (u ◁ (iso hy).hom.app k)
end AHomFamily
end UlmerBialgebras
end

/-! ## Representable adjunctions induced by an adjunction in `K` -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace TwoAdj

variable {c d : Obj} {f : c ⟶ d} {g : d ⟶ c} (Adj : TwoAdj f g)

/-- Naturality of the unit `k ↦ k ◁ η` of the adjunction induced on the hom-categories out of
`x` (`postcompUnit`), up to the `eqToHom`s of the strict unit and associativity laws. -/
theorem postcompUnit_naturality (x : Obj) {k k' : x ⟶ c} (α : k ⟶ k') :
    α ≫ (eqToHom (Category.comp_id k').symm ≫ (k' ◁ Adj.unit') ≫
        eqToHom (Category.assoc k' f g).symm) =
      (eqToHom (Category.comp_id k).symm ≫ (k ◁ Adj.unit') ≫
        eqToHom (Category.assoc k f g).symm) ≫ (α ▷ f) ▷ g := sorry

/-- The unit of the adjunction induced on the hom-categories out of `x`. -/
@[simps]
def postcompUnit (x : Obj) : 𝟭 (x ⟶ c) ⟶ postcomp x f ⋙ postcomp x g where
  app k := eqToHom (Category.comp_id k).symm ≫ (k ◁ Adj.unit') ≫ eqToHom (Category.assoc k f g).symm
  -- `id` gives the proof the field's own statement as its type, so the fingerprints, which
  -- erase proofs but keep their types, are those of the inline proof it replaces
  naturality _ _ α := id (Adj.postcompUnit_naturality x α)

/-- Naturality of the counit `k ↦ k ◁ ε` of the adjunction induced on the hom-categories out
of `x` (`postcompCounit`), up to the `eqToHom`s of the strict unit and associativity laws. -/
theorem postcompCounit_naturality (x : Obj) {k k' : x ⟶ d} (α : k ⟶ k') :
    (α ▷ g) ▷ f ≫ (eqToHom (Category.assoc k' g f) ≫ (k' ◁ Adj.counit') ≫
        eqToHom (Category.comp_id k')) =
      (eqToHom (Category.assoc k g f) ≫ (k ◁ Adj.counit') ≫ eqToHom (Category.comp_id k)) ≫
        α := sorry

/-- The counit of the adjunction induced on the hom-categories out of `x`. -/
@[simps]
def postcompCounit (x : Obj) : postcomp x g ⋙ postcomp x f ⟶ 𝟭 (x ⟶ d) where
  app k := eqToHom (Category.assoc k g f) ≫ (k ◁ Adj.counit') ≫ eqToHom (Category.comp_id k)
  naturality _ _ α := id (Adj.postcompCounit_naturality x α)

/-- The left triangle identity of the adjunction `K(x, f) ⊣ K(x, g)` induced by `f ⊣ g`
(`postcompAdj`): for `k : x ⟶ c`, whiskering the unit at `k` by `f` and then applying the
counit at `k ≫ f` is the identity of `k ≫ f`. -/
theorem postcompAdj_left_triangle (x : Obj) (k : x ⟶ c) :
    (postcomp x f).map ((Adj.postcompUnit x).app k) ≫
        (Adj.postcompCounit x).app ((postcomp x f).obj k) = 𝟙 ((postcomp x f).obj k) := sorry

/-- The right triangle identity of the adjunction `K(x, f) ⊣ K(x, g)` induced by `f ⊣ g`
(`postcompAdj`): for `k : x ⟶ d`, the unit at `k ≫ g` followed by the counit at `k` whiskered
by `g` is the identity of `k ≫ g`. -/
theorem postcompAdj_right_triangle (x : Obj) (k : x ⟶ d) :
    (Adj.postcompUnit x).app ((postcomp x g).obj k) ≫
        (postcomp x g).map ((Adj.postcompCounit x).app k) = 𝟙 ((postcomp x g).obj k) := sorry

/-- **A 2-adjunction is detected representably**: an adjunction `f ⊣ g` in a strict
2-category induces an adjunction `K(x, f) ⊣ K(x, g)` between the hom-categories out of any
object `x`. -/
def postcompAdj (x : Obj) : postcomp x f ⊣ postcomp x g where
  unit := Adj.postcompUnit x
  counit := Adj.postcompCounit x
  left_triangle_components k := id (Adj.postcompAdj_left_triangle x k)
  right_triangle_components k := id (Adj.postcompAdj_right_triangle x k)
end TwoAdj
end UlmerBialgebras
end

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

/-! ## Definition 7.1: bi-density -/

section BiDense

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- A pseudonatural transformation `K(-, d)|_{A^op} ⟹ K(-, c)|_{A^op}` between restricted
representables, as a 2-functor on the full sub-2-category spanned by `A`: an
`UlmerBialgebras.AHomFamily` (components and pseudonaturality isomorphisms for 1-cells, with the
unit and cocycle conditions) whose pseudonaturality isomorphisms are moreover natural in the
2-cells of `A`. -/
structure PsFamily (A : ObjectProperty Obj) (d c : Obj) extends AHomFamily A d c where
  /-- Compatibility with 2-cells `σ : u ⟹ u'` between 1-cells of `A`. -/
  nat₂ : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) {u u' : x ⟶ y} (σ : u ⟶ u') (k : y ⟶ d),
    (toAHomFamily.fn hx).map (σ ▷ k) ≫ (toAHomFamily.nat hx hy u').hom.app k
      = (toAHomFamily.nat hx hy u).hom.app k ≫ (σ ▷ (toAHomFamily.fn hy).obj k)

/-- **Definition 7.1** ([forsman2026syntactic]; cf. Hofstra–Karvonen
[hofstraInnerAutoequivalencesGeneral2024], Definition 6.2, and Street
[Street1980FibrationsBicategories], (1.9)). A class `A` of objects is **bi-dense** in `K` if for all
objects `c, d` the functor `K(c, d) → [K(-, c)|_{A^op}, K(-, d)|_{A^op}]_Psd`, `f ↦ f_*`, is an
equivalence of categories: it is fully faithful (2-cells correspond bijectively to
modifications, `UlmerBialgebras.IsACellDense`) and essentially surjective (every pseudonatural
transformation is isomorphic, by an invertible modification, to one induced by a 1-cell). -/
structure IsBiDense (A : ObjectProperty Obj) : Prop where
  /-- Full faithfulness. -/
  cell : IsACellDense A
  /-- Essential surjectivity. -/
  hom : ∀ ⦃d c : Obj⦄ (G : PsFamily A d c), Nonempty G.toAHomFamily.Representation
end BiDense

/-! ## Definitions 7.2 and 7.3: `A`-properties and `𝒜`-local presentability

The properties of the hom-categories `K(a, c)` refer to `w₀`-small (co)limits and to
`w₀`-accessibility, for a size universe `w₀` that is independent of the universes of `K`:
the paper's "small" is the Grothendieck universe `U`, while `K(a, c)` is in general a large,
locally small category. (Tying `w₀` to the universe of 2-cells would make every complete
hom-category thin, by Freyd's argument, in the 2-categories `CAT` and `V-CAT`.) -/

section AProperties

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Definition 7.2** ([forsman2026syntactic]) for cocompleteness: `K(a, c)` has all `w₀`-small
colimits for every `a ∈ A`. -/
def IsACocomplete.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃, v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃a : Obj⦄, A a → HasColimitsOfSize.{w₀, w₀} (a ⟶ c)

/-- `c` has right Kan extensions along every 1-cell of `𝒜`. -/
def HasARightKan (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (d : i ⟶ c),
    ∃ R : RightExt k d, Nonempty (IsTerminal R)
end AProperties
end UlmerBialgebras.Paper
end

section
universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Definition 5.1: monadicity in a 2-category -/

section Monadic2

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Definition 5.1** ([forsman2026syntactic]). A 1-cell `g : d ⟶ c` is **monadic** if it has a
left adjoint `f` (unit `η`, counit `ε`) such that `(d, g, gε)` is an Eilenberg–Moore object of the
monad `(gf, gεf, η)` up to equivalence: for each object `x`, the comparison functor
`K(x, d) → K(x, c)^{K(x, gf)}`, `h ↦ (gh, gεh)`, of the induced adjunction
`K(x, f) ⊣ K(x, g)` (`UlmerBialgebras.TwoAdj.postcompAdj`) is an equivalence of categories. -/
def IsMonadic2 {c d : Obj} (g : d ⟶ c) : Prop :=
  ∃ (f : c ⟶ d) (A : TwoAdj f g), ∀ x : Obj, (Monad.comparison (A.postcompAdj x)).IsEquivalence
end Monadic2
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 7: monadicity and local presentability in 2-categories -/

section
universe u v w w₀

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Sec7

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Theorem 7.6, Kan extension and cocompleteness** ([forsman2026syntactic], §7).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$. Assume:
\begin{enumerate}
    \item The morphisms $g$ and $g'$ are right adjoints.
    \item The object $c$ is $A$-cocomplete and has all right Kan extensions along morphisms in $\A$.
    \item The functors $f_a\coloneqq \K(a,f)\colon \K(a,c)\to \K(a,x)$ and $f_a'\coloneqq
    \K(a,f')\colon \K(a,c)\to \K(a,y)$ preserve $\kappa_a$-colimits, where $\kappa_a$ is an
    infinite cardinal, for each $a\in A$. 
\end{enumerate}
```

```latex
Furthermore, if $K\xleftarrow{k}I\xrightarrow{d} \BialgB$ is a span in $\K$ so that $K\in A$, and
the left Kan extensions of $ud$ and $fud$ along $k$ exist, then the left Kan extension of $d$
exists along $k$. In particular, $\BialgB$ is $A$-cocomplete.
```

**Reading.**
* bialgebraic datum in $\K$ ↦ `B : BialgDatum (Obj := Obj)`.
* span $K \leftarrow I \to \BialgB$ with $K \in A$ ↦ `k : I ⟶ X`, `d : I ⟶ E.pt` with `A X`.
* detection of left Kan extensions along $k$ ↦ existence of initial object in `LeftExt k d`.
* "$\BialgB$ is $A$-cocomplete" ↦ `IsACocomplete.{w₀} A E.pt`.
* the monadicity clause is formalized separately as `thm_7_6_monadic`.

**Deviations.**
- stronger: does not assume bi-density of $\A$ or right Kan extensions (CHALLENGE.md, *Same content,
  different form*).
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, and
  the statement takes the inserter and the equifier it uses as data (`B.ins`, `E`).
-/
theorem thm_7_6 (A : ObjectProperty Obj)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt), A X →
      (∃ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L)) →
      (∃ L : LeftExt k ((d ≫ B.uB E) ≫ B.f), Nonempty (IsInitial L)) →
        ∃ L : LeftExt k d, Nonempty (IsInitial L)) ∧
      IsACocomplete.{w₀} A E.pt := sorry

/-- **Theorem 7.6, monadicity clause** ([forsman2026syntactic], §7).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$. Assume:
\begin{enumerate}
    \item The morphisms $g$ and $g'$ are right adjoints.
    \item The object $c$ is $A$-cocomplete and has all right Kan extensions along morphisms in $\A$.
    \item The functors $f_a\coloneqq \K(a,f)\colon \K(a,c)\to \K(a,x)$ and $f_a'\coloneqq
    \K(a,f')\colon \K(a,c)\to \K(a,y)$ preserve $\kappa_a$-colimits, where $\kappa_a$ is an
    infinite cardinal, for each $a\in A$. 
\end{enumerate}
```

```latex
Then $u_\B\colon \BialgB\to c$ is monadic.
```

**Reading.**
* "bi-dense class $A$" ↦ `hA : IsBiDense A`.
* "$g, g'$ right adjoints" ↦ `TwoAdj l B.g`, `TwoAdj l B.g'`.
* "$c$ is $A$-cocomplete and has right Kan extensions along $\A$" ↦
  `IsACocomplete A B.c`, `HasARightKan A B.c`.
* "$f_a, f_a'$ preserve $\kappa_a$-colimits" ↦
  preservation of $\kappa_a$-colimits for `postcomp a B.f` and `postcomp a B.f'`.
* "$u_\B$ is monadic" ↦ `IsMonadic2 (B.uB E)`.

**Deviations.**
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, and
  the statement takes the inserter and the equifier it uses as data (`B.ins`, `E`).
-/
theorem thm_7_6_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c) (hRan : HasARightKan A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    IsMonadic2 (B.uB E) := sorry
end Sec7
end UlmerBialgebras.Paper
end
