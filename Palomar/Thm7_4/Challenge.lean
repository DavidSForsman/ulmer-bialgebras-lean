module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 7.4

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 7.4: `UlmerBialgebras.Paper.thm_7_4`.

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
* The `IsA…` predicates are about the hom-categories `K(a, -)` for `a ∈ A`; the `IsCalA…` ones also
  ask for Kan extensions along 1-cells of `𝒜`.
* `AsBicat Obj` is a synonym for `Obj`, so that Mathlib's adjunctions in a bicategory apply.
* Universes: `Bicategory.{w, v}` on `Type u` has objects in `u`, 1-cells in `v` and 2-cells in `w`;
  `w₀` and `w₁` are diagram sizes, independent of the others.
-/

set_option autoImplicit false

@[expose] public section

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

/-! The files of the formalization that the following sections come from do not import
`CategoryTheory.ReflQuiver.toQuiver` (Mathlib), so it is switched off here, and they elaborate
exactly as there. (It matters in 2-categories: with it, `⟶` between objects of a 2-category resolves
through `ReflQuiver` instead of the 2-category's own composition.) -/
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

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

/-- A functor preserves terminal objects. -/
def PreservesTerminal (F : A ⥤ B) : Prop :=
  ∀ a : A, Nonempty (Limits.IsTerminal a) → Nonempty (Limits.IsTerminal (F.obj a))

section Extensions

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-- A right extension of `d` along `k`: a 1-cell `l` together with a 2-cell `k l ⟹ d`; Mathlib's
`Bicategory.RightExtension k d`. -/
abbrev RightExt {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) := Bicategory.RightExtension k d

/-- The right extension given by a 1-cell `l` and a 2-cell `k l ⟹ d`. -/
abbrev RightExt.mk {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (ext : X ⟶ c) (counit : k ≫ ext ⟶ d) :
    RightExt k d := Bicategory.RightExtension.mk ext counit

/-- The extending 1-cell of a right extension. -/
abbrev RightExt.ext {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : RightExt k d) : X ⟶ c :=
  Bicategory.RightExtension.extension L

/-- The comparison 2-cell of a right extension. -/
abbrev RightExt.counit {I X c : Obj} {k : I ⟶ X} {d : I ⟶ c} (L : RightExt k d) :
    k ≫ L.ext ⟶ d :=
  Bicategory.RightExtension.counit L

/-! ### The interface of morphisms of extensions

The category of left extensions is Mathlib's `StructuredArrow d (precomp _ k)`, and that of right
extensions is `CostructuredArrow (precomp _ k) d`. The library uses them only through the 2-cell of
a morphism, its compatibility with the comparison 2-cells, the morphism given by a compatible
2-cell, and extensionality. -/

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

/-- `f` preserves the right Kan extension of `d` along `k`. -/
def PreservesRightKan (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c') : Prop :=
  PreservesTerminal (RightExt.push k d f)
end TwoCat
end UlmerBialgebras
end

/-! The files that the following sections come from import `CategoryTheory.ReflQuiver.toQuiver`
(Mathlib), so it is switched back on. -/
attribute [instance 1000] CategoryTheory.ReflQuiver.toQuiver

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

section
open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

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

/-- **Definition 7.2** ([forsman2026syntactic]) for having left adjoints: every `K(a, f)`, `a ∈ A`,
is a right adjoint (`f` is an `A`-right adjoint). -/
def IsARightAdjoint (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → (postcomp a f).IsRightAdjoint

/-- `c` has right Kan extensions along every 1-cell of `𝒜`. -/
def HasARightKan (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (d : i ⟶ c),
    ∃ R : RightExt k d, Nonempty (IsTerminal R)
end AProperties
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 7: monadicity and local presentability in 2-categories -/

section
universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Sec7

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Theorem 7.4** ([forsman2026syntactic], §7).

```latex
Let $g\colon d\to c$ be a morphism in $\K$. Assume that $d$ has and $g$ preserves all right Kan
extensions along morphisms in $\A$. If $g$ is an $A$-right adjoint, then $g$ is a right adjoint.
```

**Reading.**
* standing bi-density hypothesis ↦ `hA : IsBiDense A`.
* "$\A$-right adjoint" ↦ `IsARightAdjoint A g`.
* "$d$ has and $g$ preserves right Kan extensions along $\A$" ↦ `HasARightKan A d` and
  preservation of right Kan extensions `PreservesRightKan k e g` for all morphisms `k` in `A`.
* "$g$ is a right adjoint" ↦ `∃ f : c ⟶ d, Nonempty (TwoAdj f g)`.

**Deviations.**
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, which
  the proof does not use.
-/
theorem thm_7_4 (A : ObjectProperty Obj) (hA : IsBiDense A) {c d : Obj} (g : d ⟶ c)
    (hd : HasARightKan A d)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesRightKan k e g)
    (hadj : IsARightAdjoint A g) :
    ∃ f : c ⟶ d, Nonempty (TwoAdj f g) := sorry
end Sec7
end UlmerBialgebras.Paper
end
