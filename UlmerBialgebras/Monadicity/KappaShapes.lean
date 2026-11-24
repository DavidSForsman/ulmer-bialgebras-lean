module

public import Mathlib.CategoryTheory.Countable
public import UlmerBialgebras.Monadicity.AlgebraicFree

/-!
# `κ`-small shapes and `κ`-colimits

Fix an infinite cardinal `κ`.  A diagram shape is **`κ`-small** when it has at most `κ`
morphisms (`UlmerBialgebras.IsKappaSmall`), and a category has all **`κ`-colimits** when it has
colimits of every `κ`-small shape (`UlmerBialgebras.HasKappaColimits`).

This file collects the elementary shapes which are `κ`-small for every infinite `κ` — the
empty shape, the walking pair, the walking parallel pair, the walking reflexive pair and the
chain `ℕ` — together with the discrete shapes on a set of at most `κ` symbols, and records
the resulting existence and preservation statements in the form in which Mathlib expects
them (initial objects, binary coproducts, coequalizers, reflexive coequalizers, `ℕ`-indexed
colimits and small coproducts).

## Main results

* `UlmerBialgebras.IsKappaSmall`: a shape is `κ`-small when it has at most `κ` morphisms.
* `UlmerBialgebras.HasKappaColimits`: a category has colimits of every `κ`-small shape.
* `UlmerBialgebras.isKappaSmall_discreteCat`: a discrete shape on at most `κ` objects is `κ`-small.
* `UlmerBialgebras.HasKappaColimits.hasCoproductsOfShape`: a category with `κ`-colimits has
  coproducts indexed by at most `κ` objects.
* `UlmerBialgebras.HasKappaColimits.hasInitial`: a category with `κ`-colimits, `ℵ₀ ≤ κ`, has an
  initial object.

The cardinal and the shape live in the hom universe `v` (`κ : Cardinal.{v}`, shapes
`(J : Type v) [Category.{v} J]`), while the category `C : Type u` may live in any universe `u`,
as in Mathlib's `HasColimitsOfSize`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 5.4
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## Definitions -/

/-- A shape is **`κ`-small** when it has at most `κ` morphisms. -/
def IsKappaSmall (kappa : Cardinal.{v}) (J : Type v) [Category.{v} J] : Prop :=
  Cardinal.mk (Σ a b : J, (a ⟶ b)) ≤ kappa

/-- A category has all **`κ`-colimits** when it has colimits of every `κ`-small shape. -/
def HasKappaColimits (kappa : Cardinal.{v}) (C : Type u) [Category.{v} C] : Prop :=
  ∀ (J : Type v) [Category.{v} J], IsKappaSmall kappa J → HasColimitsOfShape J C

/-! ## Small models of the elementary shapes -/

/-- The morphisms of a discrete shape are its objects. -/
def discreteSigmaEquiv (X : Type u) : (Σ a b : Discrete X, (a ⟶ b)) ≃ X where
  toFun p := p.1.as
  invFun x := ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩
  left_inv := by rintro ⟨⟨a⟩, ⟨b⟩, ⟨⟨(rfl : a = b)⟩⟩⟩; rfl
  right_inv _ := rfl

/-- A discrete shape is `κ`-small iff it has at most `κ` objects. -/
lemma isKappaSmall_discrete_iff {kappa : Cardinal.{v}} {X : Type v} :
    IsKappaSmall kappa (Discrete X) ↔ Cardinal.mk X ≤ kappa := by
  rw [IsKappaSmall, Cardinal.mk_congr (discreteSigmaEquiv X)]

/-- The discrete shape on a small type, as an object of `Cat.{v, v}`. -/
def discreteCat (X : Type) : Cat.{v, v} := Cat.of (Discrete (ULift.{v} X))

/-! ## The walking reflexive pair is finite -/

/-! ## `κ`-smallness of the elementary shapes -/

variable {kappa : Cardinal.{v}}

/-- A discrete shape on at most `κ` objects is `κ`-small. -/
theorem isKappaSmall_discreteCat {X : Type} (hX : Cardinal.lift.{v} (Cardinal.mk X) ≤ kappa) :
    IsKappaSmall kappa (discreteCat.{v} X) :=
  isKappaSmall_discrete_iff.mpr ((Cardinal.mk_uLift X).trans_le hX)

/-! ## Consequences of having `κ`-colimits -/

variable {C : Type u} [Category.{v} C] (h : HasKappaColimits kappa C)
  (hk : Cardinal.aleph0.{v} ≤ kappa)

include h hk

omit hk

/-- Coproducts indexed by at most `κ` objects. -/
theorem HasKappaColimits.hasCoproductsOfShape {X : Type}
    (hX : Cardinal.lift.{v} (Cardinal.mk X) ≤ kappa) : HasCoproductsOfShape X C := by
  have : HasColimitsOfShape (Discrete (ULift.{v} X)) C :=
    h (discreteCat.{v} X) (isKappaSmall_discreteCat hX)
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)

/-- Coproducts indexed by a type of any universe with at most `κ` elements. -/
theorem HasKappaColimits.hasCoproductsOfShape' {X : Type w}
    (hX : Cardinal.lift.{v} (Cardinal.mk X) ≤ Cardinal.lift.{w} kappa) :
    HasCoproductsOfShape X C := by
  obtain ⟨emb⟩ : Nonempty (X ↪ kappa.out) := by
    rw [← Cardinal.lift_mk_le', Cardinal.mk_out]
    exact hX
  have : Small.{v} X := small_of_injective emb.injective
  have hY : IsKappaSmall kappa (Discrete (Shrink.{v} X)) := by
    rw [isKappaSmall_discrete_iff, ← Cardinal.mk_out kappa]
    exact Cardinal.mk_le_of_injective
      (f := fun y => emb ((equivShrink X).symm y))
      (emb.injective.comp (equivShrink X).symm.injective)
  have : HasColimitsOfShape (Discrete (Shrink.{v} X)) C := h _ hY
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink X).symm)

include hk

/-- A category with `κ`-small colimits, `ℵ₀ ≤ κ`, has an initial object (the empty coproduct). -/
theorem HasKappaColimits.hasInitial : HasInitial C := by
  have := h.hasCoproductsOfShape (X := PEmpty.{1})
    ((Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0).trans hk)
  exact inferInstanceAs (HasCoproductsOfShape PEmpty.{1} C)

end UlmerBialgebras
