module

public import Foundations.CategoryTheory.Monoidal.CocommProducts

/-!
# Compatibilities of the projections of a tensor product of comonoids

`Foundations/CategoryTheory/Monoidal/CocommProducts.lean` constructs the projections
`UlmerBialgebras.CocommComon.fst A B : A ⊗ B ⟶ A`, `UlmerBialgebras.CocommComon.snd A B : A ⊗ B ⟶ B`
and the pairing `UlmerBialgebras.CocommComon.lift` exhibiting the tensor product of cocommutative
comonoids as their categorical product.  This file records the elementary compatibilities of the
projections with tensoring morphisms and with the associator, which are needed to compute with the
multiplication of a group object of `CommComon V`.

## Main results

* `UlmerBialgebras.CocommComon.tensorHom_id_fst`: `(f ⊗ 𝟙 Z) ≫ fst Y Z = fst X Z ≫ f`.
* `UlmerBialgebras.CocommComon.tensorHom_id_snd`: for a comonoid morphism `f`,
  `(f ⊗ 𝟙 Z) ≫ snd Y Z = snd X Z`.
* `UlmerBialgebras.CocommComon.isComonHom_associator_hom`: the associator of a tensor product of
  comonoids is a morphism of comonoids.
* `UlmerBialgebras.CocommComon.comp_lift`: for a comonoid morphism `h`,
  `h ≫ lift f g = lift (h ≫ f) (h ≫ g)`.
* `UlmerBialgebras.CocommComon.lift_eq_associator`: in a symmetric monoidal category, for
  cocommutative comonoids the pairing of the three projections of `(A ⊗ B) ⊗ C` is the associator.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace UlmerBialgebras.CocommComon

open scoped MonObj Obj

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- `(f ⊗ 𝟙 Z) ≫ fst Y Z = fst X Z ≫ f`. -/
@[reassoc]
theorem tensorHom_id_fst {X Y : V} (Z : V) [ComonObj Z] (f : X ⟶ Y) :
    (f ⊗ₘ 𝟙 Z) ≫ fst Y Z = fst X Z ≫ f := by
  simp only [fst, tensorHom_id, ← whisker_exchange_assoc, Category.assoc,
    rightUnitor_naturality]

/-- For a comonoid morphism `f`, `(f ⊗ 𝟙 Z) ≫ snd Y Z = snd X Z`. -/
@[reassoc]
theorem tensorHom_id_snd {X Y : V} (Z : V) [ComonObj X] [ComonObj Y] (f : X ⟶ Y)
    [IsComonHom f] : (f ⊗ₘ 𝟙 Z) ≫ snd Y Z = snd X Z := by
  simp only [snd, tensorHom_id, ← comp_whiskerRight_assoc, IsComonHom.hom_counit]

/-- For a comonoid morphism `f`, `(𝟙 Z ⊗ f) ≫ fst Z Y = fst Z X`. -/
@[reassoc]
theorem id_tensorHom_fst {X Y : V} (Z : V) [ComonObj X] [ComonObj Y] (f : X ⟶ Y)
    [IsComonHom f] : (𝟙 Z ⊗ₘ f) ≫ fst Z Y = fst Z X := by
  simp only [fst, id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc,
    IsComonHom.hom_counit]

section Associator

variable (X Y Z : V)

/-- Reassociating and then projecting `Y ⊗ Z` onto `Y` is projecting `(X ⊗ Y) ⊗ Z` onto
`X ⊗ Y`. -/
@[reassoc]
theorem associator_hom_whiskerLeft_fst [ComonObj Z] :
    (α_ X Y Z).hom ≫ (X ◁ fst Y Z) = fst (X ⊗ Y) Z := by
  simp only [fst, MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
    ← associator_naturality_right]
  monoidal

/-- Reassociating and then projecting onto `Y ⊗ Z` is projecting `X ⊗ Y` onto `Y`. -/
@[reassoc]
theorem associator_hom_snd [ComonObj X] :
    (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) = snd X Y ▷ Z := by
  simp only [snd, ← Category.assoc, ← associator_naturality_left]
  monoidal

/-- `(α_ X Y Z).hom ≫ fst X (Y ⊗ Z) = fst (X ⊗ Y) Z ≫ fst X Y`. -/
@[reassoc]
theorem associator_hom_fst [BraidedCategory V] [ComonObj Y] [ComonObj Z] :
    (α_ X Y Z).hom ≫ fst X (Y ⊗ Z) = fst (X ⊗ Y) Z ≫ fst X Y := by
  rw [← associator_hom_whiskerLeft_fst X Y Z, Category.assoc,
    ← MonoidalCategory.id_tensorHom, id_tensorHom_fst]

/-- `(α_ X Y Z).hom ≫ snd X (Y ⊗ Z) ≫ fst Y Z = fst (X ⊗ Y) Z ≫ snd X Y`. -/
@[reassoc]
theorem associator_hom_snd_fst [ComonObj X] [ComonObj Z] :
    (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) ≫ fst Y Z = fst (X ⊗ Y) Z ≫ snd X Y := by
  rw [← Category.assoc, associator_hom_snd, ← MonoidalCategory.tensorHom_id,
    tensorHom_id_fst]

/-- `(α_ X Y Z).hom ≫ snd X (Y ⊗ Z) ≫ snd Y Z = snd (X ⊗ Y) Z`. -/
@[reassoc]
theorem associator_hom_snd_snd [BraidedCategory V] [ComonObj X] [ComonObj Y] :
    (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) ≫ snd Y Z = snd (X ⊗ Y) Z := by
  rw [← Category.assoc, associator_hom_snd, ← MonoidalCategory.tensorHom_id,
    tensorHom_id_snd]

end Associator

/-- The associator of a tensor product of comonoids is a morphism of comonoids. -/
instance isComonHom_associator_hom [BraidedCategory V] (X Y Z : V) [ComonObj X] [ComonObj Y]
    [ComonObj Z] :
    IsComonHom (α_ X Y Z).hom := by
  have h := (α_ (Comon.mk X) (Comon.mk Y) (Comon.mk Z)).hom.isComonHom_hom
  rw [Comon.monoidal_associator_hom_hom] at h
  convert h using 1
  change IsComonHom (α_ X Y Z).hom ↔
    IsComonHom (𝟙 (X ⊗ Y) ▷ Z ≫ (α_ X Y Z).hom ≫ X ◁ 𝟙 (Y ⊗ Z))
  rw [MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Category.comp_id]

section Lift

/-- Naturality of the pairing: for a comonoid morphism `h`,
`h ≫ lift f g = lift (h ≫ f) (h ≫ g)`. -/
@[reassoc]
theorem comp_lift {S T A B : V} [ComonObj S] [ComonObj T]
    (h : S ⟶ T) [IsComonHom h] (f : T ⟶ A) (g : T ⟶ B) :
    h ≫ lift f g = lift (h ≫ f) (h ≫ g) := by
  rw [lift, lift, ← Category.assoc, IsComonHom.hom_comul, Category.assoc,
    tensorHom_comp_tensorHom]

/-- The pairing of the two projections of a tensor product of comonoids is the identity. -/
theorem lift_fst_snd_self [BraidedCategory V] (A B : V) [ComonObj A] [ComonObj B] :
    lift (fst A B) (snd A B) = 𝟙 (A ⊗ B) := lift_fst_snd A B

/-- Pairing the two components of a projection gives the projection back. -/
theorem lift_fst_fst_snd [BraidedCategory V] (A B C : V) [ComonObj A] [ComonObj B] [ComonObj C] :
    lift (fst (A ⊗ B) C ≫ fst A B) (fst (A ⊗ B) C ≫ snd A B) = fst (A ⊗ B) C := by
  rw [← comp_lift, lift_fst_snd_self, Category.comp_id]

/-- `lift (f ≫ u) g = lift f g ≫ (u ⊗ 𝟙)`. -/
@[reassoc]
theorem lift_comp_left {T A B A' : V} [ComonObj T] (f : T ⟶ A)
    (g : T ⟶ B) (u : A ⟶ A') : lift (f ≫ u) g = lift f g ≫ (u ⊗ₘ 𝟙 B) := by
  rw [lift, lift, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- `lift f (g ≫ v) = lift f g ≫ (𝟙 ⊗ v)`. -/
@[reassoc]
theorem lift_comp_right {T A B B' : V} [ComonObj T] (f : T ⟶ A)
    (g : T ⟶ B) (v : B ⟶ B') : lift f (g ≫ v) = lift f g ≫ (𝟙 A ⊗ₘ v) := by
  rw [lift, lift, Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

end Lift

section Symmetric

variable {W : Type u} [Category.{v} W] [MonoidalCategory W] [SymmetricCategory W]

/-- The associator is the pairing of the three projections of a triple tensor product. -/
theorem lift_eq_associator (A B C : W) [ComonObj A] [ComonObj B] [ComonObj C]
    [IsCommComonObj A] [IsCommComonObj B] [IsCommComonObj C] :
    lift (fst (A ⊗ B) C ≫ fst A B)
      (lift (fst (A ⊗ B) C ≫ snd A B) (snd (A ⊗ B) C)) = (α_ A B C).hom := by
  refine hom_ext ?_ ?_
  · rw [lift_fst, associator_hom_fst]
  · rw [lift_snd]
    refine hom_ext ?_ ?_
    · rw [lift_fst, Category.assoc, associator_hom_snd_fst]
    · rw [lift_snd, Category.assoc, associator_hom_snd_snd]

end Symmetric

end UlmerBialgebras.CocommComon
