module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
-- No declaration uses `Mathlib.CategoryTheory.MorphismProperty.Retract`,
-- `Mathlib.CategoryTheory.Limits.Shapes.Reflexive`, but without them the elaboration of a
-- declaration below changes (its instances are part of the environment that the fingerprints
-- were taken in).
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 6.3

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 6.3 (Lifting OFS Along PIE Limits): `UlmerBialgebras.Paper.thm_6_3_1`,
  `UlmerBialgebras.Paper.thm_6_3_2`, `UlmerBialgebras.Paper.thm_6_3_3`.

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
end Ins

/-! ### The equifier category -/

/-- The property of an object of `C` of equifying two natural transformations. -/
def equifProp {F G : C ⥤ D} (η θ : F ⟶ G) : ObjectProperty C := fun x => η.app x = θ.app x

/-- The equifier of two natural transformations `η, θ : F ⟶ G`: the full subcategory of `C`
spanned by the objects `x` with `η x = θ x`. -/
abbrev Equif {F G : C ⥤ D} (η θ : F ⟶ G) : Type u := (equifProp η θ).FullSubcategory
end UlmerBialgebras
end

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

/-! The files that the following sections come from import `CategoryTheory.ReflQuiver.toQuiver`
(Mathlib), so it is switched back on. -/
attribute [instance 1000] CategoryTheory.ReflQuiver.toQuiver

/-! ## Definitions: `OrthogonalLE1` -/

section
universe u v

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- `e ⊥_! m` (Definition 6.1 of [forsman2026syntactic]): every commutative square from `e` to `m`
has at most one diagonal filler. -/
def OrthogonalLE1 {C : Type u} [Category.{v} C] {a b c d : C} (e : a ⟶ b) (m : c ⟶ d) : Prop :=
  ∀ (f : a ⟶ c) (g : b ⟶ d), f ≫ m = e ≫ g → ∀ h h' : b ⟶ c,
    e ≫ h = f → h ≫ m = g → e ≫ h' = f → h' ≫ m = g → h = h'
end UlmerBialgebras.Paper
end

/-! ## The statements: Section 6: factorization systems, regularity, exactness -/

section
universe u v w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Sec6

variable {C : Type u} [Category.{v} C]

/-- **Theorem 6.3 (1)** ([forsman2026syntactic], §6).

```latex
Let $\C_i$ and $\C$ be categories equipped with orthogonal factorization systems $(\E_i',\M_i')$ and
$(\E',\M')$, respectively, for each $i\in I$. Let $F,G\colon \C\to \D$ be functors. Then the
following hold.
```

```latex
\item $(\prod_i \mathcal{E}_i',\prod_i \mathcal{M}_i')$ is the unique OFS on $\prod_i \C_i$
preserved by the projections.
```

**Reading.**
* OFS on product category ↦ existence of a product factorization system whose classes
  are given componentwise by `S i`.
* "preserved by projections" ↦ projections preserve and reflect classes.
* uniqueness ↦ any other OFS on the product preserving classes is identical.

**Deviations.** none recorded.
-/
theorem thm_6_3_1 {ι : Type w} {Ci : ι → Type u} [∀ i, Category.{v} (Ci i)] (S : ∀ i, OFS (Ci i)) :
    ∃ P : OFS (∀ i, Ci i),
      (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P.E f ↔ ∀ i, (S i).E (f i)) ∧
      (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P.M f ↔ ∀ i, (S i).M (f i)) ∧
      ∀ P' : OFS (∀ i, Ci i),
        (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P'.E f → ∀ i, (S i).E (f i)) →
        (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P'.M f → ∀ i, (S i).M (f i)) → P' = P := sorry

variable {D : Type u'} [Category.{v'} D]

/-- **Theorem 6.3 (2)** ([forsman2026syntactic], §6).

```latex
Let $\C_i$ and $\C$ be categories equipped with orthogonal factorization systems $(\E_i',\M_i')$ and
$(\E',\M')$, respectively, for each $i\in I$. Let $F,G\colon \C\to \D$ be functors. Then the
following hold.
```

```latex
\item If $F(\E')\perp G(\M')$, then $(U^{-1}(\mathcal{E}'),U^{-1}(\mathcal{M}'))$ is the unique
OFS on $\Ins(F,G)$ preserved by the forgetful functor $U\colon \Ins(F,G)\to \C$.
```

**Reading.**
* "$F(\E') \perp G(\M')$" ↦ `Orthogonal (F.map e) (G.map m)` for all `e ∈ S.E`, `m ∈ S.M`.
* uniqueness ↦ any other OFS `P'` on `Ins F G` whose classes map into `S.E` and `S.M` under
  base projection satisfies `P' = P`.

**Deviations.** none recorded.
-/
theorem thm_6_3_2 (S : OFS C) (F G : C ⥤ D)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal (F.map e) (G.map m)) :
    ∃ P : OFS (Ins F G),
      (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P.E f ↔ S.E f.base) ∧
      (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P.M f ↔ S.M f.base) ∧
      ∀ P' : OFS (Ins F G),
        (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P'.E f → S.E f.base) →
        (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P'.M f → S.M f.base) → P' = P := sorry

/-- **Theorem 6.3 (3)** ([forsman2026syntactic], §6).

```latex
Let $\C_i$ and $\C$ be categories equipped with orthogonal factorization systems $(\E_i',\M_i')$ and
$(\E',\M')$, respectively, for each $i\in I$. Let $F,G\colon \C\to \D$ be functors. Then the
following hold.
```

```latex
\item Let $\eta,\theta\colon F\Rightarrow G$ be natural transformations. If $F(\E')\perp_! G(\M')$,
then the equifier $E\colon \Eq(\eta,\theta)\to \C$ has a unique OFS $(E^{-1}(\mathcal{E}'),
E^{-1}(\mathcal{M}'))$ that is preserved by $E$.
```

**Reading.**
* "$F(\E') \perp_! G(\M')$" ↦ `OrthogonalLE1 (F.map e) (G.map m)` for all `e ∈ S.E`, `m ∈ S.M`.
* uniqueness ↦ any other OFS `P'` on `Equif η θ` whose classes map into `S.E` and `S.M` under
  hom projection satisfies `P' = P`.

**Deviations.** none recorded.
-/
theorem thm_6_3_3 (S : OFS C) {F G : C ⥤ D} (η θ : F ⟶ G)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 (F.map e) (G.map m)) :
    ∃ P : OFS (Equif η θ),
      (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P.E f ↔ S.E f.hom) ∧
      (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P.M f ↔ S.M f.hom) ∧
      ∀ P' : OFS (Equif η θ),
        (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P'.E f → S.E f.hom) →
        (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P'.M f → S.M f.hom) → P' = P := sorry
end Sec6
end UlmerBialgebras.Paper
end
