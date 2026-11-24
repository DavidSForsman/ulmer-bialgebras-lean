module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem A.5

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem A.5 (Bi-Density of 𝒜 in V-CAT): `UlmerBialgebras.Paper.appendix_biDense`.

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
* In `Cat`, `.toFunctor` views a 1-cell as a functor, and `.toCatHom` a functor as a 1-cell.
* The `IsA…` predicates are about the hom-categories `K(a, -)` for `a ∈ A`; the `IsCalA…` ones also
  ask for Kan extensions along 1-cells of `𝒜`.
* Universes: `Bicategory.{w, v}` on `Type u` has objects in `u`, 1-cells in `v` and 2-cells in `w`;
  `[Category.{v} C]` on `C : Type u` has objects in `u` and morphisms in `v`.
* `appendix_local_density`, named in a *Reading*, is a statement of the formalization's full
  challenge (the development repository's `Challenge/`) that this file does not include.
-/

set_option autoImplicit false

@[expose] public section

/-! The files of the formalization that the following sections come from do not import
`CategoryTheory.ReflQuiver.toQuiver` (Mathlib), so it is switched off here, and they elaborate
exactly as there. (It matters in 2-categories: with it, `⟶` between objects of a 2-category resolves
through `ReflQuiver` instead of the 2-category's own composition.) -/
attribute [-instance] CategoryTheory.ReflQuiver.toQuiver

/-! ## Strict bicategories from 2-category data -/

section
universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-- Turning a heterogeneous equality of morphisms into an equation involving `eqToHom`. -/
lemma twoCategoryData_eq_of_heq_hom {C : Type*} [Category C] {X Y X' Y' : C}
    (hX : X = X') (hY : Y = Y')
    (x : X ⟶ Y) (y : X' ⟶ Y') (h : HEq x y) : x = eqToHom hX ≫ y ≫ eqToHom hY.symm := sorry

/-- A field-by-field presentation of a strict 2-category, used to build
`Bicategory` + `Bicategory.Strict` instances (`TwoCategoryData.toBicategory`). -/
structure TwoCategoryData (Obj : Type u) where
  /-- The type of 1-cells. -/
  Hom : Obj → Obj → Type v
  /-- The type of 2-cells between two parallel 1-cells. -/
  Cell : ∀ {a b : Obj}, Hom a b → Hom a b → Type w
  /-- The identity 1-cell. -/
  id₁ : ∀ a : Obj, Hom a a
  /-- Composition of 1-cells, in diagrammatic order. -/
  comp₁ : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
  id₁_comp₁ : ∀ {a b : Obj} (f : Hom a b), comp₁ (id₁ a) f = f
  comp₁_id₁ : ∀ {a b : Obj} (f : Hom a b), comp₁ f (id₁ b) = f
  assoc₁ : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
      comp₁ (comp₁ f g) h = comp₁ f (comp₁ g h)
  /-- The identity 2-cell. -/
  id₂ : ∀ {a b : Obj} (f : Hom a b), Cell f f
  /-- Vertical composition of 2-cells. -/
  vcomp : ∀ {a b : Obj} {f g h : Hom a b}, Cell f g → Cell g h → Cell f h
  id₂_vcomp : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), vcomp (id₂ f) α = α
  vcomp_id₂ : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), vcomp α (id₂ g) = α
  vcomp_assoc : ∀ {a b : Obj} {f g h k : Hom a b} (α : Cell f g) (β : Cell g h) (γ : Cell h k),
      vcomp (vcomp α β) γ = vcomp α (vcomp β γ)
  /-- Whiskering a 2-cell by a 1-cell on the source side. -/
  whiskerL : ∀ {a b c : Obj} (f : Hom a b) {g h : Hom b c},
      Cell g h → Cell (comp₁ f g) (comp₁ f h)
  /-- Whiskering a 2-cell by a 1-cell on the target side. -/
  whiskerR : ∀ {a b c : Obj} {f g : Hom a b}, Cell f g → ∀ h : Hom b c,
      Cell (comp₁ f h) (comp₁ g h)
  whiskerL_id₂ : ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
      whiskerL f (id₂ g) = id₂ (comp₁ f g)
  whiskerR_id₂ : ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
      whiskerR (id₂ f) g = id₂ (comp₁ f g)
  whiskerL_vcomp : ∀ {a b c : Obj} (f : Hom a b) {g h k : Hom b c} (α : Cell g h)
      (β : Cell h k), whiskerL f (vcomp α β) = vcomp (whiskerL f α) (whiskerL f β)
  whiskerR_vcomp : ∀ {a b c : Obj} {f g h : Hom a b} (α : Cell f g) (β : Cell g h)
      (k : Hom b c), whiskerR (vcomp α β) k = vcomp (whiskerR α k) (whiskerR β k)
  /-- The interchange law. -/
  interchange : ∀ {a b c : Obj} {f g : Hom a b} {h k : Hom b c} (α : Cell f g) (β : Cell h k),
      vcomp (whiskerR α h) (whiskerL g β) = vcomp (whiskerL f β) (whiskerR α k)
  whiskerL_id₁ : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), HEq (whiskerL (id₁ a) α) α
  whiskerR_id₁ : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), HEq (whiskerR α (id₁ b)) α
  whiskerL_comp₁ : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) {h k : Hom c d}
      (α : Cell h k), HEq (whiskerL (comp₁ f g) α) (whiskerL f (whiskerL g α))
  whiskerR_comp₁ : ∀ {a b c d : Obj} {f g : Hom a b} (α : Cell f g) (h : Hom b c)
      (k : Hom c d), HEq (whiskerR α (comp₁ h k)) (whiskerR (whiskerR α h) k)
  whisker_mid : ∀ {a b c d : Obj} (f : Hom a b) {g h : Hom b c} (α : Cell g h)
      (k : Hom c d), HEq (whiskerL f (whiskerR α k)) (whiskerR (whiskerL f α) k)

namespace TwoCategoryData

variable {Obj : Type u} (D : TwoCategoryData.{u, v, w} Obj)

/-- The hom-categories of a presented strict 2-category. -/
@[reducible] def homCat (a b : Obj) : Category.{w} (D.Hom a b) where
  Hom f g := D.Cell f g
  id := D.id₂
  comp := D.vcomp
  id_comp := D.id₂_vcomp
  comp_id := D.vcomp_id₂
  assoc := D.vcomp_assoc

attribute [local instance] homCat

/-- Pentagon coherence for `TwoCategoryData.toBicategory`. -/
lemma toBicategory_pentagon {a b c d e : Obj}
    (f : D.Hom a b) (g : D.Hom b c) (h : D.Hom c d) (i : D.Hom d e) :
    D.whiskerR (eqToHom (D.assoc₁ f g h)) i ≫ eqToHom (D.assoc₁ f (D.comp₁ g h) i) ≫
        D.whiskerL f (eqToHom (D.assoc₁ g h i))
      = eqToHom (D.assoc₁ (D.comp₁ f g) h i) ≫ eqToHom (D.assoc₁ f g (D.comp₁ h i)) := sorry

/-- Triangle coherence for `TwoCategoryData.toBicategory`. -/
lemma toBicategory_triangle {a b c : Obj} (f : D.Hom a b) (g : D.Hom b c) :
    eqToHom (D.assoc₁ f (D.id₁ _) g) ≫ D.whiskerL f (eqToHom (D.id₁_comp₁ g))
      = D.whiskerR (eqToHom (D.comp₁_id₁ f)) g := sorry

/-- The bicategory of a strict 2-category presented by its fields; associators and unitors
are `eqToIso`. -/
@[reducible] def toBicategory : Bicategory.{w, v} Obj where
  Hom := D.Hom
  id := D.id₁
  comp := D.comp₁
  homCategory a b := D.homCat a b
  whiskerLeft f _ _ η := D.whiskerL f η
  whiskerRight η h := D.whiskerR η h
  associator f g h := eqToIso (D.assoc₁ f g h)
  leftUnitor f := eqToIso (D.id₁_comp₁ f)
  rightUnitor f := eqToIso (D.comp₁_id₁ f)
  whiskerLeft_id := D.whiskerL_id₂
  whiskerLeft_comp := D.whiskerL_vcomp
  id_whiskerLeft {_ _ f g} η :=
    twoCategoryData_eq_of_heq_hom (D.id₁_comp₁ f) (D.id₁_comp₁ g) _ _ (D.whiskerL_id₁ η)
  comp_whiskerLeft {_ _ _ _} f g {h k} η :=
    twoCategoryData_eq_of_heq_hom (D.assoc₁ f g h) (D.assoc₁ f g k) _ _
      (D.whiskerL_comp₁ f g η)
  id_whiskerRight := D.whiskerR_id₂
  comp_whiskerRight η θ i := D.whiskerR_vcomp η θ i
  whiskerRight_id {_ _ f g} η :=
    twoCategoryData_eq_of_heq_hom (D.comp₁_id₁ f) (D.comp₁_id₁ g) _ _ (D.whiskerR_id₁ η)
  whiskerRight_comp {_ _ _ _ f f'} η g h :=
    twoCategoryData_eq_of_heq_hom (D.assoc₁ f g h).symm (D.assoc₁ f' g h).symm _ _
      (D.whiskerR_comp₁ η g h)
  whisker_assoc {_ _ _ _} f {g g'} η h :=
    twoCategoryData_eq_of_heq_hom (D.assoc₁ f g h) (D.assoc₁ f g' h) _ _
      (D.whisker_mid f η h).symm
  whisker_exchange η θ := (D.interchange η θ).symm
  pentagon {_ _ _ _ _} f g h i := toBicategory_pentagon D f g h i
  triangle {_ _ _} f g := toBicategory_triangle D f g

/-- A presented strict 2-category is a strict bicategory. -/
theorem strict : @Bicategory.Strict Obj D.toBicategory := sorry
end TwoCategoryData
end UlmerBialgebras
end

/-! ## `CAT_V`: the strict 2-category of `V`-enriched categories -/

section
open scoped CategoryTheory.Bicategory

universe w v u u₁ u₂ u₃ u₄

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

section
end

/-! ### `V`-functors -/

/-- A `V`-functor between `V`-categories: an ordinary functor together with a compatible
action on the hom-objects. -/
structure VFunctor (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A]
    (B : Type u₂) [Category.{w} B] [EnrichedOrdinaryCategory V B] where
  /-- The underlying ordinary functor. -/
  toFunctor : A ⥤ B
  /-- The action on hom-objects. -/
  emap : ∀ X Y : A, (X ⟶[V] Y) ⟶ (toFunctor.obj X ⟶[V] toFunctor.obj Y)
  /-- The action on hom-objects is compatible with the enriched composition. -/
  emap_comp : ∀ X Y Z : A,
    eComp V X Y Z ≫ emap X Z
      = (emap X Y ⊗ₘ emap Y Z) ≫ eComp V (toFunctor.obj X) (toFunctor.obj Y) (toFunctor.obj Z)
  /-- The action on hom-objects computes the action of the underlying functor on morphisms. -/
  emap_hom : ∀ {X Y : A} (f : X ⟶ Y),
    eHomEquiv V f ≫ emap X Y = eHomEquiv V (toFunctor.map f)

namespace VFunctor

variable {V}
variable {A : Type u₁} [Category.{w} A] [EnrichedOrdinaryCategory V A]
  {B : Type u₂} [Category.{w} B] [EnrichedOrdinaryCategory V B]
  {C : Type u₃} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The action of a `V`-functor on objects. -/
abbrev obj (F : VFunctor V A B) (X : A) : B := F.toFunctor.obj X

/-- The action of a `V`-functor on morphisms of the underlying categories. -/
abbrev map (F : VFunctor V A B) {X Y : A} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y := F.toFunctor.map f

/-- The identity hom actions preserve enriched composition. -/
theorem id_emap_comp (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A]
    (X Y Z : A) :
    eComp V X Y Z ≫ 𝟙 (X ⟶[V] Z) =
      (𝟙 (X ⟶[V] Y) ⊗ₘ 𝟙 (Y ⟶[V] Z)) ≫ eComp V X Y Z := sorry

/-- The identity hom actions preserve the enriched representatives of ordinary morphisms. -/
theorem id_emap_hom (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A]
    {X Y : A} (f : X ⟶ Y) : eHomEquiv V f ≫ 𝟙 (X ⟶[V] Y) = eHomEquiv V f := sorry

/-- The identity `V`-functor. -/
@[simps]
def id (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A] : VFunctor V A A where
  toFunctor := Functor.id A
  emap _ _ := 𝟙 _
  emap_comp := id_emap_comp A
  emap_hom := id_emap_hom A

/-- Composing the hom actions of two enriched functors preserves enriched composition. -/
theorem comp_emap_comp (F : VFunctor V A B) (G : VFunctor V B C) (X Y Z : A) :
    eComp V X Y Z ≫ (F.emap X Z ≫ G.emap _ _) =
      ((F.emap X Y ≫ G.emap _ _) ⊗ₘ (F.emap Y Z ≫ G.emap _ _)) ≫
        eComp V (G.obj (F.obj X)) (G.obj (F.obj Y)) (G.obj (F.obj Z)) := sorry

/-- Composing hom actions agrees with the composition of the underlying ordinary functors. -/
theorem comp_emap_hom (F : VFunctor V A B) (G : VFunctor V B C) {X Y : A} (f : X ⟶ Y) :
    eHomEquiv V f ≫ (F.emap X Y ≫ G.emap _ _) =
      eHomEquiv V ((F.toFunctor ⋙ G.toFunctor).map f) := sorry

/-- Composition of `V`-functors, in diagrammatic order. -/
@[simps]
def comp (F : VFunctor V A B) (G : VFunctor V B C) : VFunctor V A C where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  emap X Y := F.emap X Y ≫ G.emap _ _
  emap_comp := comp_emap_comp F G
  emap_hom := comp_emap_hom F G

/-- Left unit law for composition of `V`-functors: `id ∘ F = F`. -/
@[simp] lemma id_comp (F : VFunctor V A B) : (VFunctor.id A).comp F = F := sorry

/-- Right unit law for composition of `V`-functors: `F ∘ id = F`. -/
@[simp] lemma comp_id (F : VFunctor V A B) : F.comp (VFunctor.id B) = F := sorry

/-- Associativity of composition of `V`-functors. -/
lemma comp_assoc {D : Type u₄} [Category.{w} D] [EnrichedOrdinaryCategory V D]
    (F : VFunctor V A B) (G : VFunctor V B C) (H : VFunctor V C D) :
    (F.comp G).comp H = F.comp (G.comp H) := sorry
end VFunctor

/-! ### `V`-natural transformations -/

variable {V}

/-- A `V`-natural transformation between `V`-functors: a family of morphisms of the
underlying categories satisfying the enriched naturality square. -/
@[ext]
structure VNatTrans {A : Type u₁} [Category.{w} A] [EnrichedOrdinaryCategory V A]
    {B : Type u₂} [Category.{w} B] [EnrichedOrdinaryCategory V B] (F G : VFunctor V A B) where
  /-- The components. -/
  app : ∀ X : A, F.obj X ⟶ G.obj X
  /-- Enriched naturality. -/
  vnaturality : ∀ X Y : A,
    F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (app Y)
      = G.emap X Y ≫ eHomWhiskerRight V (app X) (G.obj Y)

namespace VNatTrans

variable {A : Type u₁} [Category.{w} A] [EnrichedOrdinaryCategory V A]
  {B : Type u₂} [Category.{w} B] [EnrichedOrdinaryCategory V B]
  {C : Type u₃} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The family of identity morphisms is enriched natural. -/
theorem id_vnaturality (F : VFunctor V A B) (X Y : A) :
    F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (𝟙 (F.obj Y)) =
      F.emap X Y ≫ eHomWhiskerRight V (𝟙 (F.obj X)) (F.obj Y) := sorry

/-- The identity `V`-natural transformation. -/
@[simps]
def id (F : VFunctor V A B) : VNatTrans F F where
  app X := 𝟙 (F.obj X)
  vnaturality := id_vnaturality F

/-- The componentwise composite of enriched natural transformations is enriched natural. -/
theorem vcomp_vnaturality {F G H : VFunctor V A B} (α : VNatTrans F G) (β : VNatTrans G H)
    (X Y : A) :
    F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (α.app Y ≫ β.app Y) =
      H.emap X Y ≫ eHomWhiskerRight V (α.app X ≫ β.app X) (H.obj Y) := sorry

/-- Vertical composition of `V`-natural transformations. -/
@[simps]
def vcomp {F G H : VFunctor V A B} (α : VNatTrans F G) (β : VNatTrans G H) : VNatTrans F H where
  app X := α.app X ≫ β.app X
  vnaturality := vcomp_vnaturality α β

/-- Precomposition by an enriched functor preserves enriched naturality. -/
theorem whiskerL_vnaturality (H : VFunctor V C A) {F G : VFunctor V A B} (α : VNatTrans F G)
    (X Y : C) :
    (H.emap X Y ≫ F.emap _ _) ≫ eHomWhiskerLeft V (F.obj (H.obj X)) (α.app (H.obj Y)) =
      (H.emap X Y ≫ G.emap _ _) ≫ eHomWhiskerRight V (α.app (H.obj X)) (G.obj (H.obj Y)) := sorry

/-- Whiskering a `V`-natural transformation by a `V`-functor on the source side. -/
@[simps]
def whiskerL (H : VFunctor V C A) {F G : VFunctor V A B} (α : VNatTrans F G) :
    VNatTrans (H.comp F) (H.comp G) where
  app X := α.app (H.obj X)
  vnaturality := whiskerL_vnaturality H α

/-- Postcomposition by an enriched functor preserves enriched naturality. -/
theorem whiskerR_vnaturality {F G : VFunctor V A B} (α : VNatTrans F G) (H : VFunctor V B C)
    (X Y : A) :
    (F.emap X Y ≫ H.emap _ _) ≫ eHomWhiskerLeft V (H.obj (F.obj X)) (H.map (α.app Y)) =
      (G.emap X Y ≫ H.emap _ _) ≫ eHomWhiskerRight V (H.map (α.app X)) (H.obj (G.obj Y)) := sorry

/-- Whiskering a `V`-natural transformation by a `V`-functor on the target side. -/
@[simps]
def whiskerR {F G : VFunctor V A B} (α : VNatTrans F G) (H : VFunctor V B C) :
    VNatTrans (F.comp H) (G.comp H) where
  app X := H.map (α.app X)
  vnaturality := whiskerR_vnaturality α H

/-- Left unit law for vertical composition. -/
theorem id_vcomp {F G : VFunctor V A B} (α : VNatTrans F G) : (id F).vcomp α = α := sorry

/-- Right unit law for vertical composition. -/
theorem vcomp_id {F G : VFunctor V A B} (α : VNatTrans F G) : α.vcomp (id G) = α := sorry

/-- Vertical composition is associative. -/
theorem vcomp_assoc {F G H K : VFunctor V A B}
    (α : VNatTrans F G) (β : VNatTrans G H) (γ : VNatTrans H K) :
    (α.vcomp β).vcomp γ = α.vcomp (β.vcomp γ) := sorry

/-- Whiskering on the target side preserves the identity transformation. -/
theorem whiskerR_id (F : VFunctor V A B) (G : VFunctor V B C) :
    whiskerR (id F) G = id (F.comp G) := sorry

/-- Whiskering on the source side preserves vertical composition. -/
theorem whiskerL_vcomp (H : VFunctor V C A) {F G K : VFunctor V A B}
    (α : VNatTrans F G) (β : VNatTrans G K) :
    whiskerL H (α.vcomp β) = (whiskerL H α).vcomp (whiskerL H β) := sorry

/-- Whiskering on the target side preserves vertical composition. -/
theorem whiskerR_vcomp {F G H : VFunctor V A B} (α : VNatTrans F G) (β : VNatTrans G H)
    (K : VFunctor V B C) : whiskerR (α.vcomp β) K = (whiskerR α K).vcomp (whiskerR β K) := sorry

/-- The interchange law for whiskered enriched natural transformations. -/
theorem interchange {F G : VFunctor V A B} {H K : VFunctor V B C}
    (α : VNatTrans F G) (β : VNatTrans H K) :
    (whiskerR α H).vcomp (whiskerL G β) = (whiskerL F β).vcomp (whiskerR α K) := sorry

/-- Whiskering by the identity functor on the source side is the identity. -/
theorem whiskerL_id_functor {F G : VFunctor V A B} (α : VNatTrans F G) :
    HEq (whiskerL (VFunctor.id A) α) α := sorry

/-- Whiskering by the identity functor on the target side is the identity. -/
theorem whiskerR_id_functor {F G : VFunctor V A B} (α : VNatTrans F G) :
    HEq (whiskerR α (VFunctor.id B)) α := sorry
variable {D : Type u₄} [Category.{w} D] [EnrichedOrdinaryCategory V D]

/-- Whiskering on the source side by a composite is successive whiskering. -/
theorem whiskerL_comp_functor (F : VFunctor V A B) (G : VFunctor V B C)
    {H K : VFunctor V C D} (α : VNatTrans H K) :
    HEq (whiskerL (F.comp G) α) (whiskerL F (whiskerL G α)) := sorry

/-- Whiskering on the target side by a composite is successive whiskering. -/
theorem whiskerR_comp_functor {F G : VFunctor V A B} (α : VNatTrans F G)
    (H : VFunctor V B C) (K : VFunctor V C D) :
    HEq (whiskerR α (H.comp K)) (whiskerR (whiskerR α H) K) := sorry

/-- Whiskerings on the two sides commute up to reassociation. -/
theorem whisker_left_right (F : VFunctor V A B) {G H : VFunctor V B C}
    (α : VNatTrans G H) (K : VFunctor V C D) :
    HEq (whiskerL F (whiskerR α K)) (whiskerR (whiskerL F α) K) := sorry
end VNatTrans

/-! ### The 2-category `CAT_V` -/

variable (V)

/-- A `V`-category: a type with an ordinary category structure and a compatible enrichment
in `V`. -/
structure VCat where
  /-- The type of objects. -/
  carrier : Type u
  [cat : Category.{w} carrier]
  [enr : EnrichedOrdinaryCategory V carrier]

namespace VCat

attribute [instance] VCat.cat VCat.enr

variable {V}

/-- Bundle a `V`-category. -/
abbrev of (C : Type u) [Category.{w} C] [EnrichedOrdinaryCategory V C] : VCat.{w, v, u} V :=
  ⟨C⟩
end VCat

variable {V}

/-- **`CAT_V` is a strict 2-category**: `V`-categories, `V`-functors and `V`-natural
transformations. -/
abbrev vCatTwoCategoryData : TwoCategoryData (VCat.{w, v, u} V) where
  Hom A B := VFunctor V A.carrier B.carrier
  Cell F G := VNatTrans F G
  id₁ A := VFunctor.id A.carrier
  comp₁ F G := F.comp G
  id₁_comp₁ := VFunctor.id_comp
  comp₁_id₁ := VFunctor.comp_id
  assoc₁ := VFunctor.comp_assoc
  id₂ F := VNatTrans.id F
  vcomp α β := α.vcomp β
  id₂_vcomp := VNatTrans.id_vcomp
  vcomp_id₂ := VNatTrans.vcomp_id
  vcomp_assoc := VNatTrans.vcomp_assoc
  whiskerL := fun {_ _ _} H {_ _} α => VNatTrans.whiskerL H α
  whiskerR := fun {_ _ _} {_ _} α H => VNatTrans.whiskerR α H
  whiskerL_id₂ _ _ := rfl
  whiskerR_id₂ := VNatTrans.whiskerR_id
  whiskerL_vcomp := VNatTrans.whiskerL_vcomp
  whiskerR_vcomp := VNatTrans.whiskerR_vcomp
  interchange := VNatTrans.interchange
  whiskerL_id₁ := VNatTrans.whiskerL_id_functor
  whiskerR_id₁ := VNatTrans.whiskerR_id_functor
  whiskerL_comp₁ := VNatTrans.whiskerL_comp_functor
  whiskerR_comp₁ := VNatTrans.whiskerR_comp_functor
  whisker_mid := VNatTrans.whisker_left_right

/-- The bicategory structure on enriched ordinary categories. -/
instance vCatBicategory : CategoryTheory.Bicategory (VCat.{w, v, u} V) :=
  (vCatTwoCategoryData (V := V)).toBicategory

/-- Enriched ordinary categories form a strict 2-category. -/
instance vCatTwoCategory : CategoryTheory.Bicategory.Strict (VCat.{w, v, u} V) :=
  (vCatTwoCategoryData (V := V)).strict
end UlmerBialgebras
end

/-! ## The unit `V`-category -/

section
open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

/-- The type of objects of the unit `V`-category: a single object. -/
@[nolint unusedArguments]
def UnitVCat (V : Type v) [Category.{w} V] [MonoidalCategory V] : Type u := PUnit.{u + 1}

namespace UnitVCat

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- The underlying category of the unit `V`-category: the endomorphisms of the monoidal unit
`𝟙_ V`, composed in `V`. -/
instance : Category.{w} (UnitVCat.{w, v, u} V) where
  Hom _ _ := 𝟙_ V ⟶ 𝟙_ V
  id _ := 𝟙 _
  comp f g := f ≫ g

variable {V}

/-- The endomorphism of the unit underlying a morphism of the unit `V`-category. -/
def toEnd {X Y : UnitVCat.{w, v, u} V} (f : X ⟶ Y) : (𝟙_ V ⟶ 𝟙_ V) := f

/-- **Eckmann–Hilton for the unit object**: the tensor product of two endomorphisms of the
unit, conjugated by the left unitor, is their composite. -/
lemma tensor_endo_unit (f g : 𝟙_ V ⟶ 𝟙_ V) :
    (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ V)).hom = f ≫ g := sorry
variable (V)

/-- The unit `V`-category: its single hom-object is the monoidal unit `𝟙_ V`, with the left
unitor as composition. -/
instance : EnrichedOrdinaryCategory V (UnitVCat.{w, v, u} V) where
  Hom _ _ := 𝟙_ V
  id _ := 𝟙 _
  comp _ _ _ := (λ_ (𝟙_ V)).hom
  id_comp _ _ := by simp
  comp_id _ _ := by simp [MonoidalCategory.unitors_equal]
  assoc _ _ _ _ := by simp [MonoidalCategory.unitors_equal]
  homEquiv := Equiv.refl _
  homEquiv_id _ := rfl
  homEquiv_comp f g := (tensor_endo_unit (toEnd f) (toEnd g)).symm
end UnitVCat

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- The unit `V`-category, as an object of `CAT_V`. It is reducible, so that its objects are
those of `UnitVCat V` at reducible transparency, and `UnitVCat.star V` is an object of it. -/
abbrev unitVCat : VCat.{w, v, u} V := ⟨UnitVCat.{w, v, u} V⟩
end UlmerBialgebras
end

/-! ## The free `V`-category on an arrow -/

section
universe w v u₁

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory Limits

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-! ### An absorbing initial object -/

/-- An **absorbing initial object** of a monoidal category: an initial object whose tensor
products with arbitrary objects, on either side, are again initial.  When `V` is braided monoidal
closed (or biclosed) and has an initial object this is automatic, since `x ⊗ -` and `- ⊗ x` are
then left adjoints (this construction is not formalized here). -/
structure MonoidalInitial (V : Type v) [Category.{w} V] [MonoidalCategory V] where
  /-- The initial object. -/
  zero : V
  /-- It is initial. -/
  isInitial : IsInitial zero
  /-- Tensoring it on the left with anything is initial. -/
  zeroTensor : ∀ y : V, IsInitial (zero ⊗ y)
  /-- Tensoring it on the right with anything is initial. -/
  tensorZero : ∀ y : V, IsInitial (y ⊗ zero)

/-! ### The two-object `V`-category -/

/-- The two objects of the free `V`-category on an arrow. -/
inductive ArrowObj (Z : MonoidalInitial V) (x : V) : Type u₁ where
  /-- The source of the generic arrow. -/
  | src : ArrowObj Z x
  /-- The target of the generic arrow. -/
  | tgt : ArrowObj Z x

namespace ArrowObj

variable (Z : MonoidalInitial V) (x : V)

/-- The hom-objects of the free `V`-category on an arrow. -/
def hom : ArrowObj.{w, v, u₁} Z x → ArrowObj.{w, v, u₁} Z x → V
  | .src, .src => 𝟙_ V
  | .src, .tgt => x
  | .tgt, .src => Z.zero
  | .tgt, .tgt => 𝟙_ V

/-- The identities of the free `V`-category on an arrow. -/
def eid : ∀ a : ArrowObj.{w, v, u₁} Z x, 𝟙_ V ⟶ hom Z x a a
  | .src => 𝟙 _
  | .tgt => 𝟙 _

/-- The composition of the free `V`-category on an arrow: the unitors, except where the
source involves the initial hom-object `Hom(1,0)`, in which case it is forced. -/
def ecomp : ∀ a b c : ArrowObj.{w, v, u₁} Z x, hom Z x a b ⊗ hom Z x b c ⟶ hom Z x a c
  | .src, .src, .src => (λ_ (𝟙_ V)).hom
  | .src, .src, .tgt => (λ_ x).hom
  | .src, .tgt, .src => (Z.tensorZero x).to _
  | .src, .tgt, .tgt => (ρ_ x).hom
  | .tgt, .src, .src => (Z.zeroTensor _).to _
  | .tgt, .src, .tgt => (Z.zeroTensor x).to _
  | .tgt, .tgt, .src => (Z.tensorZero _).to _
  | .tgt, .tgt, .tgt => (λ_ (𝟙_ V)).hom

/-- The left unit law of `ecomp Z x`: the `V`-category axiom `id_comp`. -/
theorem ecomp_id_comp (a b : ArrowObj.{w, v, u₁} Z x) :
    (λ_ (hom Z x a b)).inv ≫ eid Z x a ▷ hom Z x a b ≫ ecomp Z x a a b = 𝟙 _ := sorry

/-- The right unit law of `ecomp Z x`: the `V`-category axiom `comp_id`. -/
theorem ecomp_comp_id (a b : ArrowObj.{w, v, u₁} Z x) :
    (ρ_ (hom Z x a b)).inv ≫ hom Z x a b ◁ eid Z x b ≫ ecomp Z x a b b = 𝟙 _ := sorry

/-- The associativity of `ecomp Z x`: the `V`-category axiom `assoc`. -/
theorem ecomp_assoc (a b c d : ArrowObj.{w, v, u₁} Z x) :
    (α_ (hom Z x a b) (hom Z x b c) (hom Z x c d)).inv ≫ ecomp Z x a b c ▷ hom Z x c d ≫
        ecomp Z x a c d =
      hom Z x a b ◁ ecomp Z x b c d ≫ ecomp Z x a b d := sorry

/-- The `V`-category structure on the two objects `src`, `tgt` of the free `V`-category on
an arrow of shape `x`, with composition `ecomp` and identities `eid`. -/
instance enrichedCategory : EnrichedCategory V (ArrowObj.{w, v, u₁} Z x) where
  Hom := hom Z x
  id := eid Z x
  comp := ecomp Z x
  id_comp := ecomp_id_comp Z x
  comp_id := ecomp_comp_id Z x
  assoc := ecomp_assoc Z x
end ArrowObj

variable (Z : MonoidalInitial V) (x : V)

/-- **The free `V`-category on an arrow of shape `x`**, as an object of `CAT_V`. -/
def arrowVCat : VCat.{w, v, u₁} V := VCat.of (ForgetEnrichment V (ArrowObj.{w, v, u₁} Z x))
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
end UlmerBialgebras.Paper
end

/-! ## The carrier of the linear three-object enriched category -/

section
universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The three vertices of a labelled linear graph. -/
inductive ThreeObj (Z : MonoidalInitial V) (x y : V) : Type u where
  | zero | one | two

namespace ThreeObj

variable (Z : MonoidalInitial V) (x y : V)

/-- Hom-objects of `𝟑_{x,y}`: `I` on the diagonal, `x` for `0 → 1`, `y` for `1 → 2`,
`x ⊗ y` for `0 → 2`, and the initial object `Z.zero` for the backward pairs. -/
def hom : ThreeObj.{w, v, u} Z x y → ThreeObj.{w, v, u} Z x y → V
  | .zero, .zero => 𝟙_ V
  | .zero, .one => x
  | .zero, .two => x ⊗ y
  | .one, .zero => Z.zero
  | .one, .one => 𝟙_ V
  | .one, .two => y
  | .two, .zero => Z.zero
  | .two, .one => Z.zero
  | .two, .two => 𝟙_ V

/-- Identities of `𝟑_{x,y}`: the identity of `I` at each object. -/
def eid : ∀ a : ThreeObj.{w, v, u} Z x y, 𝟙_ V ⟶ hom Z x y a a
  | .zero => 𝟙 _
  | .one => 𝟙 _
  | .two => 𝟙 _

/-- Composition `Hom(a,b) ⊗ Hom(b,c) → Hom(a,c)` of `𝟑_{x,y}`: unitors where one factor is
`I`, the identity `x ⊗ y → x ⊗ y` for `0 → 1 → 2`, and the unique map out of an initial tensor
otherwise. -/
def ecomp : ∀ a b c : ThreeObj.{w, v, u} Z x y,
    hom Z x y a b ⊗ hom Z x y b c ⟶ hom Z x y a c
  | .zero, .zero, .zero => (λ_ (𝟙_ V)).hom
  | .zero, .zero, .one => (λ_ x).hom
  | .zero, .zero, .two => (λ_ (x ⊗ y)).hom
  | .zero, .one, .one => (ρ_ x).hom
  | .zero, .one, .two => 𝟙 _
  | .zero, .two, .two => (ρ_ (x ⊗ y)).hom
  | .one, .one, .one => (λ_ (𝟙_ V)).hom
  | .one, .one, .two => (λ_ y).hom
  | .one, .two, .two => (ρ_ y).hom
  | .two, .two, .two => (λ_ (𝟙_ V)).hom
  | .one, .zero, _ => (Z.zeroTensor _).to _
  | .two, .zero, _ => (Z.zeroTensor _).to _
  | .two, .one, _ => (Z.zeroTensor _).to _
  | _, .one, .zero => (Z.tensorZero _).to _
  | _, .two, .zero => (Z.tensorZero _).to _
  | _, .two, .one => (Z.tensorZero _).to _

/-- The left unit law of `ecomp Z x y`: the `V`-category axiom `id_comp`. -/
theorem ecomp_id_comp (a b : ThreeObj.{w, v, u} Z x y) :
    (λ_ (hom Z x y a b)).inv ≫ eid Z x y a ▷ hom Z x y a b ≫ ecomp Z x y a a b = 𝟙 _ := sorry

/-- The right unit law of `ecomp Z x y`: the `V`-category axiom `comp_id`. -/
theorem ecomp_comp_id (a b : ThreeObj.{w, v, u} Z x y) :
    (ρ_ (hom Z x y a b)).inv ≫ hom Z x y a b ◁ eid Z x y b ≫ ecomp Z x y a b b = 𝟙 _ := sorry

/-- The associativity of `ecomp Z x y`: the `V`-category axiom `assoc`. -/
theorem ecomp_assoc (a b c d : ThreeObj.{w, v, u} Z x y) :
    (α_ (hom Z x y a b) (hom Z x y b c) (hom Z x y c d)).inv ≫ ecomp Z x y a b c ▷ hom Z x y c d ≫
        ecomp Z x y a c d =
      hom Z x y a b ◁ ecomp Z x y b c d ≫ ecomp Z x y a b d := sorry

/-- The `V`-category structure on `ThreeObj Z x y` given by `hom`, `eid` and `ecomp`. -/
instance : EnrichedCategory V (ThreeObj.{w, v, u} Z x y) where
  Hom := hom Z x y
  id := eid Z x y
  comp := ecomp Z x y
  id_comp := ecomp_id_comp Z x y
  comp_id := ecomp_comp_id Z x y
  assoc := ecomp_assoc Z x y
end ThreeObj
end UlmerBialgebras.Paper.Appendix
end

/-! ## The linear three-object enriched category -/

section
universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The free enriched category on a composable pair of labelled edges (the linear `V`-category
`𝟑_{x,y}` of Definition A.4 of [forsman2026syntactic], via Lemma A.3), in the library's tensor
order `x ⊗ y` (cf. `paperThreeVCat` in `UlmerBialgebras/Paper/AppendixDefsReverse.lean` for the
paper's
`y ⊗ x`). -/
def threeVCat (Z : MonoidalInitial V) (x y : V) : VCat.{w, v, u} V :=
  VCat.of (ForgetEnrichment V (ThreeObj.{w, v, u} Z x y))

/-- The exact class of the first three linear probes (Definition A.4 of [forsman2026syntactic]; the
class `A` of Theorem A.5),
expressed in the existing library's tensor-order convention. -/
def IsLinearProbe (Z : MonoidalInitial V) (A : VCat.{w, v, u} V) : Prop :=
  A = unitVCat.{w, v, u} V ∨
    (∃ x : V, A = arrowVCat.{w, v, u} Z x) ∨
    ∃ x y : V, A = threeVCat.{w, v, u} Z x y
end UlmerBialgebras.Paper.Appendix
end

/-! ## Translating the appendix's tensor order -/

section
universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- Initiality is unchanged by the monoidal-opposite wrapper. -/
def mopIsInitial {z : V} (hz : Limits.IsInitial z) : Limits.IsInitial (mop z) :=
  Limits.IsInitial.ofUniqueHom (fun y => (hz.to y.unmop).mop)
    (fun _ _ => MonoidalOpposite.hom_ext (hz.hom_ext _ _))

/-- An absorbing initial object remains absorbing when tensor order is reversed. -/
def reverseInitial (Z : MonoidalInitial V) : MonoidalInitial Vᴹᵒᵖ where
  zero := mop Z.zero
  isInitial := mopIsInitial Z.isInitial
  zeroTensor y := mopIsInitial (Z.tensorZero y.unmop)
  tensorZero y := mopIsInitial (Z.zeroTensor y.unmop)

/-- Enriched categories in the composition convention used by the paper. -/
abbrev PaperVCat (V : Type v) [Category.{w} V] [MonoidalCategory V] :=
  VCat.{w, v, u} Vᴹᵒᵖ

/-- The appendix's class `A` (Theorem A.5 of [forsman2026syntactic]) of point, arrow and
three-object linear probes. -/
abbrev IsPaperLinearProbe (Z : MonoidalInitial V) (A : PaperVCat.{w, v, u} V) : Prop :=
  IsLinearProbe.{w, v, u} (reverseInitial Z) A
end UlmerBialgebras.Paper.Appendix
end

/-! ## The statements: Appendix A: Lemma A.3, Definition A.4 and Theorem A.5 -/

section
universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Theorem A.5** ([forsman2026syntactic], Appendix A;
[hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1).

```latex
Let $\V$ be a monoidal category with an absorbing initial object. Then the class
$$
A \coloneqq \{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y} \mid x,y \in \Obj(\V)\}
$$
is bi-dense in the $2$-category $\K \coloneqq \V\text{-}\CAT$.
```

**Reading.**
* $\V$ monoidal category with absorbing initial object ↦ `[MonoidalCategory V]`,
  `Z : MonoidalInitial V`.
* $\K \coloneqq \V\text{-}\CAT$ ↦ `Appendix.PaperVCat V` (in paper's tensor convention).
* class $A \coloneqq \{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y}\}$ ↦
  `Appendix.IsPaperLinearProbe Z`.
* bi-dense in $\K$ ↦ `IsBiDense (Appendix.IsPaperLinearProbe Z)`.
* the carrier universe stays `max u w` (chosen by the author): the proof identifies the carrier of
  a `V`-category with its hom-category from the unit `V`-category, in `Type (max u w)`.
  The local density statement `appendix_local_density` takes carriers in any `Type u`.

**Deviations.**
- different (size): the 2-category `V-CAT` is that of the `V`-categories with objects in
  `Type (max u w)`, at least the universe `Type w` of `V`'s morphisms; a `V`-category with smaller
  objects is isomorphic, through `ULift`, to one of them. The proof identifies the objects of a
  `V`-category with the `V`-functors out of the unit `V`-category, which live in `Type (max u w)`.
-/
theorem appendix_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := Appendix.PaperVCat.{w, v, max u w} V)
      (Appendix.IsPaperLinearProbe.{w, v, max u w} Z) := sorry
end UlmerBialgebras.Paper
end
