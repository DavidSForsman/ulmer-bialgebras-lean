module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 6.6

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 6.6: `UlmerBialgebras.Paper.thm_6_6_1`, `UlmerBialgebras.Paper.thm_6_6_2`,
  `UlmerBialgebras.Paper.thm_6_6_3`, `UlmerBialgebras.Paper.thm_6_6_3_coeq`.

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

/-! ## Orthogonal factorization systems -/

section
universe v u

namespace UlmerBialgebras

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Two morphisms `e` and `m` are **orthogonal**, `e ⊥ m`, if every commutative square from
`e` to `m` has a unique diagonal filler. -/
def Orthogonal {a b c d : C} (e : a ⟶ b) (m : c ⟶ d) : Prop :=
  ∀ (f : a ⟶ c) (g : b ⟶ d), f ≫ m = e ≫ g → ∃! h : b ⟶ c, e ≫ h = f ∧ h ≫ m = g

/-- The right orthogonal class `A⊥` of a class `A` of morphisms. -/
def rightOrth (A : MorphismProperty C) : MorphismProperty C :=
  fun _ _ m => ∀ ⦃a b : C⦄ (e : a ⟶ b), A e → Orthogonal e m

/-- The left orthogonal class `⊥A` of a class `A` of morphisms. -/
def leftOrth (A : MorphismProperty C) : MorphismProperty C :=
  fun _ _ e => ∀ ⦃c d : C⦄ (m : c ⟶ d), A m → Orthogonal e m

/-- An **orthogonal factorization system** on a category `C` (Definition 6.1). -/
structure OFS (C : Type u) [Category.{v} C] where
  /-- The left class. -/
  E : MorphismProperty C
  /-- The right class. -/
  M : MorphismProperty C
  /-- Every morphism factors as a morphism of `E` followed by a morphism of `M`. -/
  fact : ∀ ⦃x y : C⦄ (f : x ⟶ y), ∃ (z : C) (e : x ⟶ z) (m : z ⟶ y), E e ∧ M m ∧ e ≫ m = f
  /-- `M = E⊥`. -/
  M_eq : M = rightOrth E
  /-- `E = ⊥M`. -/
  E_eq : E = leftOrth M
end UlmerBialgebras
end

/-! ## Barr-exact categories -/

section
universe v u

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/-- A category is **Barr-exact** (or *exact* in the sense of Barr) if it is regular and every
equivalence relation in it is effective, i.e. it is the kernel pair of its coequalizer. -/
class BarrExact : Prop extends Regular C where
  /-- Every equivalence relation is effective. -/
  isEffectiveEquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) [IsEquivalenceRelation p₁ p₂] :
    IsEffectiveEquivalenceRelation p₁ p₂
end CategoryTheory
end

/-! ## Regularity and exactness -/

section
universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A functor preserves the coequalizers of kernel pairs. -/
def PreservesCoequalizersOfKernelPairs (F : C ⥤ D) : Prop :=
  ∀ ⦃R x y : C⦄ (r s : R ⟶ x) (f : x ⟶ y) (hk : IsKernelPair f r s)
    (_ : IsColimit (Cofork.ofπ f hk.w)),
    Nonempty (IsColimit (F.mapCocone (Cofork.ofπ f hk.w)))
end UlmerBialgebras
end

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

/-- A functor **strictly creates terminal objects**. -/
def StrictlyCreatesTerminal (F : A ⥤ B) : Prop :=
  ∀ b : B, Nonempty (Limits.IsTerminal b) →
    (∃! a : A, F.obj a = b) ∧ ∀ a : A, F.obj a = b → Nonempty (Limits.IsTerminal a)

section Extensions

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-! ### Definition 4.2: categories of extensions -/

/-- A left extension of `d` along `k`: a 1-cell `l` together with a 2-cell `d ⟹ k l`; Mathlib's
`Bicategory.LeftExtension k d`. -/
abbrev LeftExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.LeftExtension k d

/-- A right extension of `d` along `k`: a 1-cell `l` together with a 2-cell `k l ⟹ d`; Mathlib's
`Bicategory.RightExtension k d`. -/
abbrev RightExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.RightExtension k d

/-- The left extension given by a 1-cell `l` and a 2-cell `d ⟹ k l`. -/
abbrev LeftExt.mk {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (ext : X ⟶ c) (unit : d ⟶ k ≫ ext) :
    LeftExt k d := Bicategory.LeftExtension.mk ext unit

/-- The right extension given by a 1-cell `l` and a 2-cell `k l ⟹ d`. -/
abbrev RightExt.mk {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (ext : X ⟶ c) (counit : k ≫ ext ⟶ d) :
    RightExt k d := Bicategory.RightExtension.mk ext counit

/-- The extending 1-cell of a left extension. -/
abbrev LeftExt.ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) : X ⟶ c :=
  Bicategory.LeftExtension.extension L

/-- The extending 1-cell of a right extension. -/
abbrev RightExt.ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : RightExt k d) : X ⟶ c :=
  Bicategory.RightExtension.extension L

/-- The comparison 2-cell of a left extension. -/
abbrev LeftExt.unit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : LeftExt k d) : d ⟶ k ≫ L.ext :=
  Bicategory.LeftExtension.unit L

/-- The comparison 2-cell of a right extension. -/
abbrev RightExt.counit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : RightExt k d) :
    k ≫ L.ext ⟶ d :=
  Bicategory.RightExtension.counit L

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

namespace RightExt

variable {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} {L L' L'' : RightExt k d}

/-- The 2-cell `L.ext ⟶ L'.ext` of a morphism of right extensions. -/
abbrev homCell (α : L ⟶ L') : L.ext ⟶ L'.ext := α.left

/-- The morphism of right extensions given by a compatible 2-cell. -/
abbrev homMk (η : L.ext ⟶ L'.ext) (w : k ◁ η ≫ L'.counit = L.counit) : L ⟶ L' :=
  Bicategory.RightExtension.homMk η w

/-- Morphisms of right extensions are equal when their 2-cells are. -/
@[ext] lemma hom_ext {α β : L ⟶ L'} (h : homCell α = homCell β) : α = β := sorry
end RightExt
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

/-- Post-composing a morphism of right extensions with `f` is compatible with the comparison
2-cells of the post-composed extensions. -/
lemma RightExt.push_w {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') {L L' : RightExt k d}
    (a : L ⟶ L') :
    k ◁ (RightExt.homCell a ▷ f) ≫ (eqToHom (Category.assoc k L'.ext f).symm ≫ (L'.counit ▷ f)) =
      eqToHom (Category.assoc k L.ext f).symm ≫ (L.counit ▷ f) := sorry

/-- Post-composition with a 1-cell `f : c ⟶ c'`, as a functor between categories of right
extensions. -/
@[implicit_reducible]
def RightExt.push {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') :
    RightExt k d ⥤ RightExt k (d ≫ f) where
  obj L := RightExt.mk (L.ext ≫ f) (eqToHom (Category.assoc k L.ext f).symm ≫ (L.counit ▷ f))
  map a := RightExt.homMk (RightExt.homCell a ▷ f) (RightExt.push_w k d f a)
  map_id L := RightExt.hom_ext (Bicategory.id_whiskerRight L.ext f)
  map_comp _ _ := RightExt.hom_ext (Bicategory.comp_whiskerRight _ _ f)

/-! ### Definition 4.4 -/

variable {I X c c' : Obj}

/-- `f` strictly creates the left Kan extensions of `d` along `k`. -/
def StrictlyCreatesLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  StrictlyCreatesInitial (LeftExt.push k d f)

/-- `f` strictly creates the right Kan extensions of `d` along `k`. -/
def StrictlyCreatesRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  StrictlyCreatesTerminal (RightExt.push k d f)
end TwoCat
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

/-! ## Definitions: `PreservesJointMonoOfShape`, `OrthogonalLE1` -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- `F` preserves the joint monicness of limiting cones of shape `J`. -/
def PreservesJointMonoOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cone Kd), IsLimit c → ∀ ⦃y : D⦄ (p q : y ⟶ F.obj c.pt),
    (∀ j, p ≫ F.map (c.π.app j) = q ≫ F.map (c.π.app j)) → p = q

/-- `e ⊥_! m` (Definition 6.1 of [forsman2026syntactic]): every commutative square from `e` to `m`
has at most one diagonal filler. -/
def OrthogonalLE1 {C : Type u} [Category.{v} C] {a b c d : C} (e : a ⟶ b) (m : c ⟶ d) : Prop :=
  ∀ (f : a ⟶ c) (g : b ⟶ d), f ≫ m = e ≫ g → ∀ h h' : b ⟶ c,
    e ≫ h = f → h ≫ m = g → e ≫ h' = f → h' ≫ m = g → h = h'
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 6: factorization systems, regularity, exactness -/

section
universe u v s

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- **Theorem 6.6 (1)** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item If $F(\E')\perp G(\M')$ and $F'(\E')\perp_! G'(\M')$, then the pair $(\E,\M)$ is the unique
OFS on $\BialgB$ preserved by $U_\B\colon \BialgB\to \C$.
```

**Reading.**
* bialgebraic datum in $\CAT$ ↦ `(B : BialgDatum)` at `Cat.{v, max u v}`.
* "unique OFS on $\BialgB$ preserved by $U_\B$" ↦ existence of an OFS on `E.pt`
  whose classes are the preimages under the forgetful functor of `S.E` and `S.M`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_1 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v)))
    (horth : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal ((B.f).toFunctor.map e) ((B.g).toFunctor.map m))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m)) :
    ∃ P : OFS (E.pt : Type (max u v)),
      (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
        P.E f ↔ S.E ((B.uB E).toFunctor.map f)) ∧
      (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
        P.M f ↔ S.M ((B.uB E).toFunctor.map f)) ∧
      ∀ P' : OFS (E.pt : Type (max u v)),
        (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
          P'.E f → S.E ((B.uB E).toFunctor.map f)) →
        (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
          P'.M f → S.M ((B.uB E).toFunctor.map f)) → P' = P := sorry

/-- **Theorem 6.6 (2)** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item Assume $\C$ is regular, $\M'$ is the class of monomorphisms in $\C$, and $\BialgB$ has a
terminal object. Assume that $F$ preserves regular epis, $F'(\E')\perp_! G'(\M')$, $G$ preserves
pullbacks, and $G'$ the joint monicness of pullback projections. Then $\BialgB$ is regular with
$U$ strictly creating pullbacks and preserving regular epimorphisms.
```

**Reading.**
* "$\C$ regular, $\M'$ monos, $\BialgB$ has terminal object" ↦ `[Regular (B.c : Type (max u v))]`,
  `S.M = MorphismProperty.monomorphisms (B.c : Type (max u v))`,
  `HasTerminal (E.pt : Type (max u v))`.
* "$\BialgB$ is regular" ↦ `Regular (E.pt : Type (max u v))`.
* "$U$ strictly creates pullbacks" ↦ `StrictlyCreatesRightKan (toOne J) d (B.uB E)` for any shape
  `J` equivalent to `WalkingCospan`.
* "$U$ preserves regular epimorphisms" ↦ preservation of regular epimorphisms by the
  forgetful functor `B.uB E`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_2 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v))) [Regular (B.c : Type (max u v))]
    (hM : S.M = MorphismProperty.monomorphisms (B.c : Type (max u v)))
    (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Nonempty (RegularEpi ((B.f).toFunctor.map e)))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    Regular (E.pt : Type (max u v)) ∧
      (∀ (J : Cat.{v, max u v}) (_ : WalkingCospan ≌ (J : Type (max u v)))
        (d : J ⟶ E.pt), StrictlyCreatesRightKan (toOne J) d (B.uB E)) ∧
      ∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y), Nonempty (RegularEpi f) →
        Nonempty (RegularEpi ((B.uB E).toFunctor.map f)) := sorry

/-- **Theorem 6.6 (3)** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item If $\C$ is exact, $\BialgB$ has a terminal object, $F$ preserves coequalizers of kernel
pairs, $F'$ maps regular epis to epis, $G$ preserves pullbacks and $G'$ the joint monicness of
pullback projections, then $\BialgB$ is exact with $U$ strictly creating coequalizers of kernel
pairs.
```

**Reading.**
* "$\C$ exact, $\BialgB$ has terminal object" ↦ `[BarrExact (B.c : Type (max u v))]` and
  `HasTerminal (E.pt : Type (max u v))`.
* "$\BialgB$ is exact" ↦ `BarrExact (E.pt : Type (max u v))`.
* strict creation of coequalizers of kernel pairs is formalized in `thm_6_6_3_coeq`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_3 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))] (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    BarrExact (E.pt : Type (max u v)) := sorry

/-- **Theorem 6.6 (3), creation clause** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item If $\C$ is exact, $\BialgB$ has a terminal object, $F$ preserves coequalizers of kernel
pairs, $F'$ maps regular epis to epis, $G$ preserves pullbacks and $G'$ the joint monicness of
pullback projections, then $\BialgB$ is exact with $U$ strictly creating coequalizers of kernel
pairs.
```

**Reading.**
* "strictly creating coequalizers of kernel pairs" ↦ for any kernel pair `r, s` of `f`,
  `StrictlyCreatesLeftKan (toOne J) ... (B.uB E)` for any shape `J` equivalent to
  `WalkingParallelPair`.
* omits the terminal object hypothesis: the creation clause holds without assuming `HasTerminal`.

**Deviations.**
- stronger: omits the hypothesis that $\BialgB$ has a terminal object (CHALLENGE.md, *Stronger than
  the paper*).
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_3_coeq (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))]
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)
    ⦃R a b : (E.pt : Type (max u v))⦄ (f : a ⟶ b) (r s : R ⟶ a) (hk : IsKernelPair f r s) :
    ∀ (J : Cat.{v, max u v}) (e : WalkingParallelPair ≌ (J : Type (max u v))),
      StrictlyCreatesLeftKan (toOne J) (e.inverse ⋙ parallelPair r s).toCatHom
        (B.uB E) := sorry
end UlmerBialgebras.Paper
end
