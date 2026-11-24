module

public import UlmerBialgebras.Basic.CatTwoCat
public import UlmerBialgebras.Models.BicatTwoCat
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Adjunctions in the strict 2-category `CAT`

In the strict 2-category `Cat.{v, u}` (`CategoryTheory.Cat.bicategory`), a 2-categorical adjunction
`UlmerBialgebras.TwoAdj F G` is the same thing as an ordinary adjunction `F ⊣ G` of functors. This
file records that dictionary, for arbitrary universes `v` and `u` (the component lemmas of
`CatCells.lean` are stated only for `Cat.{u, u}`).

## Main definitions

* `UlmerBialgebras.TwoAdj.toAdjunction`: a 2-adjunction in `Cat` is an adjunction of functors.
* `UlmerBialgebras.Adjunction.toTwoAdj`: an adjunction of functors is a 2-adjunction in `Cat`.
* `UlmerBialgebras.TwoAdj.equivAdjunction`: the two notions are equivalent.

## Main results

* `UlmerBialgebras.exists_twoAdj_left_iff_isRightAdjoint`,
  `UlmerBialgebras.exists_twoAdj_right_iff_isLeftAdjoint`: a functor is a right (left) adjoint in
  the 2-categorical sense exactly when it is one in Mathlib's sense.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2 and
  Definition 5.1 (adjunctions in a 2-category, specialised to `CAT`)
* [G. M. Kelly, R. Street,
  *Review of the elements of 2-categories*][kellyReviewElements2categories1974]
-/

universe v u

namespace UlmerBialgebras

open CategoryTheory

section Cells

variable {A B D : Cat.{v, u}}

/- Mathlib's component lemmas for 2-cells of `Cat.{v, u}`, as simp lemmas (the others are
already). -/
attribute [simp] Cat.whiskerLeft_app Cat.whiskerRight_app Cat.eqToHom_app Cat.Hom.comp_obj

/-- Two 2-cells of `Cat.{v, u}` with the same components are equal. -/
lemma catVU_cell_ext {F G : A ⟶ B} {α β : F ⟶ G} (h : ∀ x, α.toNatTrans.app x = β.toNatTrans.app
    x) : α = β :=
  Cat.Hom₂.ext (NatTrans.ext (funext h))

end Cells

variable {C D : Cat.{v, u}} {F : C ⟶ D} {G : D ⟶ C}

/-- A 2-categorical adjunction `F ⊣ G` in `Cat` is an adjunction of functors, with the same unit
and counit. -/
@[simps]
def TwoAdj.toAdjunction (A : TwoAdj (Obj := Cat.{v, u}) F G) : F.toFunctor ⊣ G.toFunctor where
  unit := A.unit'.toNatTrans
  counit := A.counit'.toNatTrans
  left_triangle_components X := by
    have h := NatTrans.congr_app congr($(A.left_triangle').toNatTrans) X
    simpa using h
  right_triangle_components Y := by
    have h := NatTrans.congr_app congr($(A.right_triangle').toNatTrans) Y
    simpa using h

/-- An adjunction of functors `F ⊣ G` is a 2-categorical adjunction in `Cat`, with the same unit
and counit. -/
def Adjunction.toTwoAdj (adj : F.toFunctor ⊣ G.toFunctor) : TwoAdj (Obj := Cat.{v, u}) F G :=
  TwoAdj.mk' adj.unit.toCatHom₂ adj.counit.toCatHom₂
    (catVU_cell_ext fun X => by simp)
    (catVU_cell_ext fun Y => by simp)

/-- The unit of `Adjunction.toTwoAdj adj` is the unit of `adj`. -/
@[simp] lemma Adjunction.toTwoAdj_unit (adj : F.toFunctor ⊣ G.toFunctor) :
    (Adjunction.toTwoAdj adj).unit'.toNatTrans = adj.unit := rfl

/-- The counit of `Adjunction.toTwoAdj adj` is the counit of `adj`. -/
@[simp] lemma Adjunction.toTwoAdj_counit (adj : F.toFunctor ⊣ G.toFunctor) :
    (Adjunction.toTwoAdj adj).counit'.toNatTrans = adj.counit := rfl

/-- Turning an adjunction into a 2-adjunction and back gives the original adjunction. -/
@[simp] lemma Adjunction.toTwoAdj_toAdjunction (adj : F.toFunctor ⊣ G.toFunctor) :
    (Adjunction.toTwoAdj adj).toAdjunction = adj := rfl

/-- Turning a 2-adjunction into an adjunction and back gives the original 2-adjunction. -/
@[simp] lemma TwoAdj.toAdjunction_toTwoAdj (A : TwoAdj (Obj := Cat.{v, u}) F G) :
    Adjunction.toTwoAdj A.toAdjunction = A := rfl

/-- In `Cat`, 2-categorical adjunctions `F ⊣ G` are equivalent to adjunctions of functors. -/
@[simps]
def TwoAdj.equivAdjunction : TwoAdj (Obj := Cat.{v, u}) F G ≃ (F.toFunctor ⊣ G.toFunctor) where
  toFun A := A.toAdjunction
  invFun adj := Adjunction.toTwoAdj adj
  left_inv _ := rfl
  right_inv _ := rfl

/-- A functor is a right adjoint in the 2-category `Cat` if and only if it is a right adjoint. -/
theorem exists_twoAdj_left_iff_isRightAdjoint (G : D ⟶ C) :
    (∃ f : C ⟶ D, Nonempty (TwoAdj (Obj := Cat.{v, u}) f G)) ↔ G.toFunctor.IsRightAdjoint :=
  ⟨fun ⟨_, ⟨A⟩⟩ => A.toAdjunction.isRightAdjoint,
    fun _ => ⟨G.toFunctor.leftAdjoint.toCatHom, ⟨Adjunction.toTwoAdj (Adjunction.ofIsRightAdjoint
        _)⟩⟩⟩

/-- A functor is a left adjoint in the 2-category `Cat` if and only if it is a left adjoint. -/
theorem exists_twoAdj_right_iff_isLeftAdjoint (F : C ⟶ D) :
    (∃ g : D ⟶ C, Nonempty (TwoAdj (Obj := Cat.{v, u}) F g)) ↔ F.toFunctor.IsLeftAdjoint :=
  ⟨fun ⟨_, ⟨A⟩⟩ => A.toAdjunction.isLeftAdjoint,
    fun _ => ⟨F.toFunctor.rightAdjoint.toCatHom, ⟨Adjunction.toTwoAdj (Adjunction.ofIsLeftAdjoint
        _)⟩⟩⟩

end UlmerBialgebras
