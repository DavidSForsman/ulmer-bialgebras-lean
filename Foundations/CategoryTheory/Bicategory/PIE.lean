module

public import Foundations.CategoryTheory.Bicategory.TwoCategoryData
public import Foundations.CategoryTheory.Bicategory.StrictCoherence
public import Foundations.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Category.Cat

/-!
# PIE limits

Strict products, inserters and equifiers in a strict 2-category, following Definition 2.1
of *A Syntactic Approach to Ulmer's Bialgebras*.  Each notion is given by its explicit
universal property on 1-cells **and** on 2-cells.

Index types of products are taken to be small (`Type`), matching the paper's convention
that a PIE-complete 2-category has *small* products.

## Main definitions

* `UlmerBialgebras.Product`: a strict product of a small family of objects (Definition 2.1).
* `UlmerBialgebras.Inserter`: a strict inserter of a parallel pair of 1-cells (Definition 2.1).
* `UlmerBialgebras.Equifier`: a strict equifier of a parallel pair of 2-cells (Definition 2.1).
* `UlmerBialgebras.HasChosenFinProducts`, `UlmerBialgebras.HasChosenInserters`,
  `UlmerBialgebras.HasChosenEquifiers`: chosen finite products, inserters and equifiers.
* `UlmerBialgebras.HasChosenProductsOfSize`: chosen products indexed by `Type s`.
* `UlmerBialgebras.PIEComplete`: a 2-category with chosen small products, inserters and equifiers.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 2.1
* [G. J. Bird, G. M. Kelly, A. J. Power, R. Street, *Flexible limits for
  2-categories*][birdFlexibleLimits2categories1989]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w s t

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

namespace Product

variable {ι : Type s} {c : ι → Obj} (P : Product c)

/-- Two 1-cells into a product agreeing on all projections are equal. -/
lemma hom_ext {x : Obj} {h k : x ⟶ P.pt} (H : ∀ i, h ≫ P.π i = k ≫ P.π i) : h = k := by
  rw [← P.lift_uniq h, ← P.lift_uniq k]
  simp only [H]

/-- Two 2-cells into a product agreeing on all projections are equal. -/
lemma cell_ext {x : Obj} {f g : x ⟶ P.pt} {α β : f ⟶ g} (H : ∀ i, α ▷ P.π i = β ▷ P.π i) :
    α = β := by
  rw [← P.lift₂_uniq α, ← P.lift₂_uniq β]
  simp only [H]

/-- Induced 2-cells are compatible with vertical composition. -/
lemma lift₂_comp {x : Obj} {f g h : x ⟶ P.pt} (γ : ∀ i, (f ≫ P.π i) ⟶ (g ≫ P.π i))
    (δ : ∀ i, (g ≫ P.π i) ⟶ (h ≫ P.π i)) :
    P.lift₂ γ ≫ P.lift₂ δ = P.lift₂ (fun i => γ i ≫ δ i) := by
  refine P.cell_ext (fun i => ?_)
  rw [Bicategory.comp_whiskerRight, P.lift₂_π, P.lift₂_π, P.lift₂_π]

/-- The 2-cell induced by the identities is the identity. -/
lemma lift₂_id {x : Obj} {f : x ⟶ P.pt} : P.lift₂ (fun i => 𝟙 (f ≫ P.π i)) = 𝟙 f := by
  refine P.cell_ext (fun i => ?_)
  rw [P.lift₂_π]; simp

section Strict

variable [Bicategory.Strict Obj]

/-- A projection after the 1-cell into a power `X^ι` induced by a constant family, followed by
a 1-cell `k`: `lift (fun _ => h) ≫ π i ≫ k = h ≫ k`. -/
lemma lift_const_π_assoc {X : Obj} (Q : Product (fun _ : ι => X)) {x y : Obj} (h : x ⟶ X)
    (i : ι) (k : X ⟶ y) : Q.lift (fun _ => h) ≫ Q.π i ≫ k = h ≫ k :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ k) (Q.lift_π _ i))

/-- Pre-composing an induced 1-cell: `h ≫ lift g = lift (fun i => h ≫ g i)`. -/
lemma comp_lift {x y : Obj} (h : y ⟶ x) (g : ∀ i, x ⟶ c i) :
    h ≫ P.lift g = P.lift (fun i => h ≫ g i) := by
  refine P.hom_ext (fun i => ?_)
  rw [Category.assoc, P.lift_π, P.lift_π]

/-- The 1-cell induced by the projections followed by identities is the identity. -/
lemma lift_π_comp_id : P.lift (fun i => P.π i ≫ 𝟙 (c i)) = 𝟙 P.pt :=
  P.hom_ext fun i => by rw [P.lift_π, Category.comp_id, Category.id_comp]

/-- Composing the 1-cells `∏ cᵢ → ∏ dᵢ → ∏ cᵢ` induced componentwise by `Fᵢ` and `Gᵢ`, and
projecting, gives `πᵢ ≫ Fᵢ ≫ Gᵢ`. -/
lemma lift_comp_lift_π {d : ι → Obj} (Q : Product d) (F : ∀ i, c i ⟶ d i)
    (G : ∀ i, d i ⟶ c i) (i : ι) :
    (Q.lift (fun j => P.π j ≫ F j) ≫ P.lift (fun j => Q.π j ≫ G j)) ≫ P.π i =
      P.π i ≫ (F i ≫ G i) := by
  rw [Category.assoc, P.lift_π, ← Category.assoc, Q.lift_π, Category.assoc]

/-- Whiskering a 2-cell induced by the product with a 1-cell. -/
lemma whiskerLeft_lift₂ {x y : Obj} (h : y ⟶ x) {f g : x ⟶ P.pt}
    (γ : ∀ i, (f ≫ P.π i) ⟶ (g ≫ P.π i)) :
    h ◁ (P.lift₂ γ) = P.lift₂ (fun i =>
      eqToHom (Category.assoc h f (P.π i)) ≫ (h ◁ γ i) ≫
        eqToHom (Category.assoc h g (P.π i)).symm) := by
  refine P.cell_ext (fun i => ?_)
  rw [P.lift₂_π]
  have hh := Bicategory.Strict.whisker_assoc h (P.lift₂ γ) (P.π i)
  rw [P.lift₂_π] at hh
  rw [hh]
  simp

end Strict

/-- A product of `c` reindexed along `ULift` is a product of `c`. -/
@[implicit_reducible]
def ofULift {c : ι → Obj} (P : Product (fun j : ULift.{t} ι => c j.down)) : Product c where
  pt := P.pt
  π i := P.π ⟨i⟩
  lift g := P.lift (fun j => g j.down)
  lift_π g i := P.lift_π (fun j => g j.down) ⟨i⟩
  lift_uniq h := P.lift_uniq h
  lift₂ α := P.lift₂ (fun j => α j.down)
  lift₂_π α i := P.lift₂_π (fun j => α j.down) ⟨i⟩
  lift₂_uniq β := P.lift₂_uniq β

end Product

variable [Bicategory.Strict Obj]

/-- Associativity helper for the universal property of an inserter. -/
lemma inserter_assoc_comp {a b pt x : Obj} {k : x ⟶ pt} {u : pt ⟶ a} {h : x ⟶ a}
    (hu : k ≫ u = h) (f : a ⟶ b) : k ≫ (u ≫ f) = h ≫ f := by
  rw [← Category.assoc, hu]

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

namespace Inserter

variable {a b : Obj} {f g : a ⟶ b} (I : Inserter f g)

/-- The universal 2-cell of the inserter, whiskered by a 1-cell into the inserter. -/
def phiAt {x : Obj} (k : x ⟶ I.pt) : (k ≫ I.u) ≫ f ⟶ (k ≫ I.u) ≫ g :=
  eqToHom (Category.assoc k I.u f) ≫ (k ◁ I.φ) ≫ eqToHom (Category.assoc k I.u g).symm

/-- Two 2-cells into an inserter are equal as soon as their whiskerings by `u` are: the
inserter is "2-faithful". -/
lemma faithful {x : Obj} {k₁ k₂ : x ⟶ I.pt} (α β : k₁ ⟶ k₂) (H : α ▷ I.u = β ▷ I.u) : α = β :=
  I.lift₂_uniq α β H

/-- The 2-cell of the inserter induced by a compatible 2-cell of the whiskerings. -/
def lift₂' {x : Obj} {k₁ k₂ : x ⟶ I.pt} (α : k₁ ≫ I.u ⟶ k₂ ≫ I.u)
    (H : I.phiAt k₁ ≫ (α ▷ g) = (α ▷ f) ≫ I.phiAt k₂) : k₁ ⟶ k₂ :=
  I.lift₂ α H

/-- Whiskering `lift₂' α H` by `u` recovers `α`. -/
@[simp] lemma lift₂'_u {x : Obj} {k₁ k₂ : x ⟶ I.pt} (α : k₁ ≫ I.u ⟶ k₂ ≫ I.u)
    (H : I.phiAt k₁ ≫ (α ▷ g) = (α ▷ f) ≫ I.phiAt k₂) : I.lift₂' α H ▷ I.u = α :=
  I.lift₂_u α H

/-- Every 2-cell into the inserter is automatically compatible with the universal 2-cell. -/
lemma phiAt_square {x : Obj} {k₁ k₂ : x ⟶ I.pt} (α : k₁ ⟶ k₂) :
    I.phiAt k₁ ≫ ((α ▷ I.u) ▷ g) = ((α ▷ I.u) ▷ f) ≫ I.phiAt k₂ := by
  simp only [phiAt, Category.assoc]
  rw [Bicategory.Strict.whiskerRight_comp' α I.u g, Bicategory.Strict.whiskerRight_comp' α I.u f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (Eq.symm <| Bicategory.whisker_exchange α I.φ)]

end Inserter

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

/-- **PIE-complete_s** (Definition 2.1 of [forsman2026syntactic]): chosen products of
`Type s`-indexed families, chosen finite products, inserters and equifiers, all strict. The finite
products are extra data: they are not asked to agree with the size-`s` products. The size `s` is
the first universe argument and an input of instance search, as for `HasChosenProductsOfSize`. -/
@[univ_out_params]
class PIEComplete.{s', u', v', w'} (Obj : Type u') [Bicategory.{w', v'} Obj]
    [Bicategory.Strict Obj] extends HasChosenProductsOfSize.{s'} Obj, HasChosenFinProducts Obj,
    HasChosenInserters Obj, HasChosenEquifiers Obj

/-- Products of size `max s t` give products of size `s`. Not an instance: `t` cannot be
inferred. -/
@[implicit_reducible]
def HasChosenProductsOfSize.down [HasChosenProductsOfSize.{max s t, u, v, w} Obj] :
    HasChosenProductsOfSize.{s, u, v, w} Obj :=
  ⟨fun c => Product.ofULift (HasChosenProductsOfSize.prod (fun j : ULift.{t} _ => c j.down))⟩

end UlmerBialgebras
