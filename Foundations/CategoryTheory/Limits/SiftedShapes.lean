module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# Sifted and cosifted shapes

This file treats the two standard families of sifted shapes, filtered categories and the
walking reflexive pair.

Dually, a category is **cosifted** when its opposite is sifted (`UlmerBialgebras.IsCosifted`), so
that its limits are the "cosifted limits"; we prove that the walking *coreflexive pair*
(`UlmerBialgebras.walkingCoreflexivePair_isCosifted`), the shape whose limits are the coreflexive
equalizers, is cosifted.

Siftedness of the walking reflexive pair is proved directly: for every pair `(X, Y)` of its
objects the comma category `StructuredArrow (X, Y) (diag)` is shown to be connected by
exhibiting, for each of its objects, an explicit zigzag to the object
`UlmerBialgebras.wrpBase X Y` sitting over `one`.

These are the shapes to which Corollary 4.17 of *A Syntactic Approach to Ulmer's
Bialgebras* and its dual are applied in `SiftedApplications.lean`.

## Main results

* `UlmerBialgebras.walkingReflexivePair_isSifted` — the walking *reflexive pair*, the shape whose
  colimits are the reflexive coequalizers, is sifted;
* `UlmerBialgebras.IsCosifted` — a category is cosifted when its opposite is sifted;
* `UlmerBialgebras.walkingCoreflexivePair_isCosifted` — the walking coreflexive pair is cosifted.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 4.3,
  Corollary 4.17
* [J. Adámek, J. Rosický, E. M. Vitale, *What Are Sifted
  Colimits?*][AdamekRosickyVitale2010SiftedColimits]
* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories: A Categorical Introduction to General
  Algebra*][Adamek-Rosicky-Vitale]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits Functor WalkingReflexivePair WalkingReflexivePair.Hom

/-! ## The walking reflexive pair is sifted -/

/-- The base point used to prove that the comma categories of the diagonal of the walking
reflexive pair are connected: the object lying over `one`. -/
def wrpBase (X Y : WalkingReflexivePair) : StructuredArrow (X, Y) (diag WalkingReflexivePair) :=
  StructuredArrow.mk (Y := WalkingReflexivePair.one)
    ((match X with | .zero => reflexion | .one => 𝟙 _),
     (match Y with | .zero => reflexion | .one => 𝟙 _))

variable {W : WalkingReflexivePair × WalkingReflexivePair}

/-- A two-step zigzag `j → k ← b`. -/
theorem wrpZigzag₂ {j k b : StructuredArrow W (diag WalkingReflexivePair)} (h₁ : j ⟶ k)
    (h₂ : b ⟶ k) : Zigzag j b :=
  (Zigzag.of_hom h₁).trans (Zigzag.of_inv h₂)

/-- A three-step zigzag `j ← k → m ← b`. -/
theorem wrpZigzag₃ {j k m b : StructuredArrow W (diag WalkingReflexivePair)}
    (h₁ : k ⟶ j) (h₂ : k ⟶ m) (h₃ : b ⟶ m) : Zigzag j b :=
  ((Zigzag.of_inv h₁).trans (Zigzag.of_hom h₂)).trans (Zigzag.of_inv h₃)

/-- Every object of the comma category of the diagonal of the walking reflexive pair is
connected to the base point by a zigzag. -/
theorem wrp_zigzag_wrpBase (X Y Z : WalkingReflexivePair) (a : WalkingReflexivePair.Hom X Z)
    (b : WalkingReflexivePair.Hom Y Z) :
    Zigzag (StructuredArrow.mk (T := diag WalkingReflexivePair) (Y := Z)
      ((a : X ⟶ Z), (b : Y ⟶ Z))) (wrpBase X Y) := by
  cases X <;> cases Y <;> cases a <;> cases b <;>
    first
      | exact Relation.ReflTransGen.refl
      | exact Zigzag.of_hom (StructuredArrow.homMk reflexion rfl)
      | exact Zigzag.of_inv (StructuredArrow.homMk left rfl)
      | exact Zigzag.of_inv (StructuredArrow.homMk right rfl)
      | exact Zigzag.of_inv (StructuredArrow.homMk leftCompReflexion rfl)
      | exact Zigzag.of_inv (StructuredArrow.homMk rightCompReflexion rfl)
      | exact wrpZigzag₂ (k := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (leftCompReflexion, leftCompReflexion))
          (StructuredArrow.homMk leftCompReflexion rfl)
          (StructuredArrow.homMk leftCompReflexion rfl)
      | exact wrpZigzag₂ (k := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (rightCompReflexion, rightCompReflexion))
          (StructuredArrow.homMk rightCompReflexion rfl)
          (StructuredArrow.homMk rightCompReflexion rfl)
      | exact wrpZigzag₃ (k := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (Hom.id WalkingReflexivePair.one, rightCompReflexion))
          (m := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (rightCompReflexion, rightCompReflexion))
          (StructuredArrow.homMk leftCompReflexion rfl)
          (StructuredArrow.homMk rightCompReflexion rfl)
          (StructuredArrow.homMk rightCompReflexion rfl)
      | exact wrpZigzag₃ (k := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (Hom.id WalkingReflexivePair.one, leftCompReflexion))
          (m := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (leftCompReflexion, leftCompReflexion))
          (StructuredArrow.homMk rightCompReflexion rfl)
          (StructuredArrow.homMk leftCompReflexion rfl)
          (StructuredArrow.homMk leftCompReflexion rfl)
      | exact wrpZigzag₃ (k := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (Hom.id WalkingReflexivePair.one, rightCompReflexion))
          (m := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (rightCompReflexion, rightCompReflexion))
          (StructuredArrow.homMk left rfl)
          (StructuredArrow.homMk rightCompReflexion rfl)
          (StructuredArrow.homMk rightCompReflexion rfl)
      | exact wrpZigzag₃ (k := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (Hom.id WalkingReflexivePair.one, leftCompReflexion))
          (m := StructuredArrow.mk (T := diag WalkingReflexivePair)
            (Y := WalkingReflexivePair.one) (leftCompReflexion, leftCompReflexion))
          (StructuredArrow.homMk right rfl)
          (StructuredArrow.homMk leftCompReflexion rfl)
          (StructuredArrow.homMk leftCompReflexion rfl)

/-- The diagonal functor of the walking reflexive pair is final. -/
instance walkingReflexivePair_final_diag : Final (diag WalkingReflexivePair) where
  out := by
    rintro ⟨X, Y⟩
    have : Nonempty (StructuredArrow (X, Y) (diag WalkingReflexivePair)) := ⟨wrpBase X Y⟩
    refine zigzag_isConnected (fun j j' => ?_)
    have h : ∀ k : StructuredArrow (X, Y) (diag WalkingReflexivePair), Zigzag k (wrpBase X Y) :=
      fun k => wrp_zigzag_wrpBase X Y k.right k.hom.1 k.hom.2
    exact (h j).trans (h j').symm

/-- The walking reflexive pair — the shape of a reflexive pair, whose colimits are the
reflexive coequalizers — is a sifted category. -/
instance walkingReflexivePair_isSifted : IsSifted WalkingReflexivePair where

/-! ## Cosifted categories -/

/-- A category is **cosifted** if its opposite category is sifted; equivalently, if it is
nonempty and the diagonal `C ⥤ C × C` is initial.  Limits of cosifted shape are the ones
which commute with finite coproducts in `Type`. -/
abbrev IsCosifted (C : Type u) [Category.{v} C] : Prop := IsSifted Cᵒᵖ

/-- The walking coreflexive pair: the shape of a coreflexive pair, whose limits are the
coreflexive equalizers. -/
abbrev WalkingCoreflexivePair : Type := WalkingReflexivePairᵒᵖ

/-- The walking coreflexive pair is cosifted. -/
instance walkingCoreflexivePair_isCosifted : IsCosifted WalkingCoreflexivePair :=
  IsSifted.isSifted_of_equiv (opOpEquivalence WalkingReflexivePair)

end UlmerBialgebras
