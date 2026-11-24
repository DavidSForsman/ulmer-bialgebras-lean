module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 4.7

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 4.7 (Lifting Kan Extensions Along PIE Limits):
  `UlmerBialgebras.Paper.thm_4_7_1_preserves`, `UlmerBialgebras.Paper.thm_4_7_1_creates`,
  `UlmerBialgebras.Paper.thm_4_7_1_quotient`, `UlmerBialgebras.Paper.thm_4_7_2_left`,
  `UlmerBialgebras.Paper.thm_4_7_2_right`, `UlmerBialgebras.Paper.thm_4_7_3_left`,
  `UlmerBialgebras.Paper.thm_4_7_3_right`.

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
* Universes: `Bicategory.{w, v}` on `Type u` has objects in `u`, 1-cells in `v` and 2-cells in `w`.
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
end UlmerBialgebras
end

/-! ## Internal limits: Kan extensions and their lifting along PIE limits -/

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-! ### Definition 4.1 -/

/-- An object is **quotient initial** if there is at most one morphism out of it. -/
def QuotientInitial {A : Type*} [Category A] (a : A) : Prop := ∀ b : A, Subsingleton (a ⟶ b)

/-- An object is **subterminal** if there is at most one morphism into it: Mathlib's
`CategoryTheory.IsSubterminal`. -/
abbrev Subterminal {A : Type*} [Category A] (a : A) : Prop := IsSubterminal a

/-! ### Definition 4.3 -/

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor preserves initial objects. -/
def PreservesInitial (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsInitial a) → Nonempty (Limits.IsInitial (F.obj a))

/-- A functor preserves terminal objects. -/
def PreservesTerminal (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsTerminal a) → Nonempty (Limits.IsTerminal (F.obj a))

/-- A functor **strictly creates initial objects**: every initial object of the target has
a unique preimage, and that preimage is initial. -/
def StrictlyCreatesInitial (F : A ⥤ B) : Prop :=
  ∀ b : B, Nonempty (Limits.IsInitial b) →
    (∃! a : A, F.obj a = b) ∧ ∀ a : A, F.obj a = b → Nonempty (Limits.IsInitial a)

/-- A functor **strictly creates terminal objects**. -/
def StrictlyCreatesTerminal (F : A ⥤ B) : Prop :=
  ∀ b : B, Nonempty (Limits.IsTerminal b) →
    (∃! a : A, F.obj a = b) ∧ ∀ a : A, F.obj a = b → Nonempty (Limits.IsTerminal a)

/-- A family of functors **jointly strictly creates initial objects**. -/
def JointlyStrictlyCreatesInitial {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, Nonempty (Limits.IsInitial b) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧
      ∀ a : A, (∀ i, (F i).obj a = b i) → Nonempty (Limits.IsInitial a)

/-- A family of functors **jointly strictly creates terminal objects**. -/
def JointlyStrictlyCreatesTerminal {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, Nonempty (Limits.IsTerminal b) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧
      ∀ a : A, (∀ i, (F i).obj a = b i) → Nonempty (Limits.IsTerminal a)

/-- A family of functors **jointly strictly creates quotient initial objects**: every family of
quotient initial objects has a unique lift, and every lift of it is quotient initial. -/
def JointlyStrictlyCreatesQuotientInitial {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, (∀ i, QuotientInitial (b i)) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧ ∀ a : A, (∀ i, (F i).obj a = b i) → QuotientInitial a

/-- A family of functors **jointly strictly creates subterminal objects**: every family of
subterminal objects has a unique lift, and every lift of it is subterminal. -/
def JointlyStrictlyCreatesSubterminal {ι : Type*} {B : ι → Type*} [∀ i, Category (B i)]
    (F : ∀ i, A ⥤ B i) : Prop :=
  ∀ b : ∀ i, B i, (∀ i, Subterminal (b i)) →
    (∃! a : A, ∀ i, (F i).obj a = b i) ∧ ∀ a : A, (∀ i, (F i).obj a = b i) → Subterminal a

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

/-- `f` preserves the left Kan extension of `d` along `k`. -/
def PreservesLeftKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  PreservesInitial (LeftExt.push k d f)

/-- `f` preserves the right Kan extension of `d` along `k`. -/
def PreservesRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  PreservesTerminal (RightExt.push k d f)

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

/-! ## The statements: Section 4 (lifting limits and colimits) -/

section
universe s u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section General

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Theorem 4.7 (1), preservation** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $(c_i)_{i \in J}$ be a family of objects in $\K$ whose product $c = \prod_{i\in J} c_i$
exists in $\K$. Then the family $(\pi_i \colon c \to c_i)_{i\in J}$ of projections preserves and
jointly strictly creates all right and left Kan extensions. Additionally, the family of projections
jointly strictly creates and preserves (subterminality) quotient initiality of a (right) left
extension.
```

**Reading.**
* "projections preserve all right and left Kan extensions" ↦ `PreservesLeftKan k d (P.π i)` and
  `PreservesRightKan k d (P.π i)` for each index `i`.

**Deviations.** none recorded.
-/
theorem thm_4_7_1_preserves {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) (i : ι) :
    PreservesLeftKan k d (P.π i) ∧ PreservesRightKan k d (P.π i) := sorry

/-- **Theorem 4.7 (1), creation** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $(c_i)_{i \in J}$ be a family of objects in $\K$ whose product $c = \prod_{i\in J} c_i$
exists in $\K$. Then the family $(\pi_i \colon c \to c_i)_{i\in J}$ of projections preserves and
jointly strictly creates all right and left Kan extensions. Additionally, the family of projections
jointly strictly creates and preserves (subterminality) quotient initiality of a (right) left
extension.
```

**Reading.**
* "jointly strictly creates all right and left Kan extensions" ↦ `JointlyStrictlyCreatesInitial` on
  the pushed left extensions and `JointlyStrictlyCreatesTerminal` on the pushed right extensions.

**Deviations.** none recorded.
-/
theorem thm_4_7_1_creates {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    JointlyStrictlyCreatesInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
      JointlyStrictlyCreatesTerminal (fun i : ι => RightExt.push k d (P.π i)) := sorry

/-- **Theorem 4.7 (1), quotient initiality and subterminality** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $(c_i)_{i \in J}$ be a family of objects in $\K$ whose product $c = \prod_{i\in J} c_i$
exists in $\K$. Then the family $(\pi_i \colon c \to c_i)_{i\in J}$ of projections preserves and
jointly strictly creates all right and left Kan extensions. Additionally, the family of projections
jointly strictly creates and preserves (subterminality) quotient initiality of a (right) left
extension.
```

**Reading.**
* "jointly strictly creates and preserves (subterminality) quotient initiality" ↦ equivalence of
  `QuotientInitial L` with componentwise quotient initiality, together with
  `JointlyStrictlyCreatesQuotientInitial`, and dually for `Subterminal R` and
  `JointlyStrictlyCreatesSubterminal`.

**Deviations.** none recorded.
-/
theorem thm_4_7_1_quotient {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    (∀ L : LeftExt k d,
      QuotientInitial L ↔ ∀ i, QuotientInitial ((LeftExt.push k d (P.π i)).obj L)) ∧
    JointlyStrictlyCreatesQuotientInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
    (∀ R : RightExt k d,
      Subterminal R ↔ ∀ i, Subterminal ((RightExt.push k d (P.π i)).obj R)) ∧
    JointlyStrictlyCreatesSubterminal (fun i : ι => RightExt.push k d (P.π i)) := sorry

/-- **Theorem 4.7 (2), left Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Consider the inserter diagram
\[
\begin{tikzcd}
{\Ins(f,g)} \arrow[d, "u"'] \arrow[r, "u"]        & a \arrow[d, "g"] \\
a \arrow[r, "f"'] \arrow[ru, "\phi" description, Rightarrow] & b
\end{tikzcd}
\]
in $\K$. Then the morphism $u$ strictly creates left Kan extensions that $f$ preserves, and strictly
creates right Kan extensions that $g$ preserves.
```

**Reading.**
* "morphism $u$ strictly creates left Kan extensions that $f$ preserves" ↦
  `hf : PreservesLeftKan k (d ≫ Ins.u) f` implies `StrictlyCreatesLeftKan k d Ins.u`.

**Deviations.** none recorded.
-/
theorem thm_4_7_2_left {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hf : PreservesLeftKan k (d ≫ Ins.u) f) :
    StrictlyCreatesLeftKan k d Ins.u := sorry

/-- **Theorem 4.7 (2), right Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Consider the inserter diagram
\[
\begin{tikzcd}
{\Ins(f,g)} \arrow[d, "u"'] \arrow[r, "u"]        & a \arrow[d, "g"] \\
a \arrow[r, "f"'] \arrow[ru, "\phi" description, Rightarrow] & b
\end{tikzcd}
\]
in $\K$. Then the morphism $u$ strictly creates left Kan extensions that $f$ preserves, and strictly
creates right Kan extensions that $g$ preserves.
```

**Reading.**
* "morphism $u$ strictly creates right Kan extensions that $g$ preserves" ↦
  `hg : PreservesRightKan k (d ≫ Ins.u) g` implies `StrictlyCreatesRightKan k d Ins.u`.

**Deviations.** none recorded.
-/
theorem thm_4_7_2_right {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hg : PreservesRightKan k (d ≫ Ins.u) g) :
    StrictlyCreatesRightKan k d Ins.u := sorry

/-- **Theorem 4.7 (3), left Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $\Eq(\eta,\theta)\xrightarrow{u}c$ be the equifier of $\eta,\theta \colon f \Rightarrow g
\colon c \to c'$. Then $u$ strictly creates left (right) Kan extensions whose quotient initiality
(subterminality) is preserved by $f$ $(g)$.
```

**Reading.**
* "strictly creates left Kan extensions whose quotient initiality is preserved by $f$" ↦ hypothesis
  `hf` stating that initial left extensions are pushed by `f` to quotient initial objects, implying
  `StrictlyCreatesLeftKan k d E.e`.

**Deviations.** none recorded.
-/
theorem thm_4_7_3_left {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hf : ∀ L : LeftExt k (d ≫ E.e), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ E.e) f).obj L)) :
    StrictlyCreatesLeftKan k d E.e := sorry

/-- **Theorem 4.7 (3), right Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $\Eq(\eta,\theta)\xrightarrow{u}c$ be the equifier of $\eta,\theta \colon f \Rightarrow g
\colon c \to c'$. Then $u$ strictly creates left (right) Kan extensions whose quotient initiality
(subterminality) is preserved by $f$ $(g)$.
```

**Reading.**
* "strictly creates right Kan extensions whose subterminality is preserved by $g$" ↦ hypothesis
  `hg` stating that terminal right extensions are pushed by `g` to subterminal objects, implying
  `StrictlyCreatesRightKan k d E.e`.

**Deviations.** none recorded.
-/
theorem thm_4_7_3_right {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hg : ∀ R : RightExt k (d ≫ E.e), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ E.e) g).obj R)) :
    StrictlyCreatesRightKan k d E.e := sorry
end General
end UlmerBialgebras.Paper
end
