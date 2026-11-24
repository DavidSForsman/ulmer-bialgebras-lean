module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.CommComon_

/-!
# Cocommutative comonoids form a cartesian monoidal category

Let `V` be a symmetric monoidal category.  This file proves that the category
`CategoryTheory.CommComon V` of **cocommutative comonoid objects** of `V` — for
`V = ModuleCat k` this is the category `Comon^coc_k` of cocommutative coalgebras over a
commutative ring `k` — has finite products, which are computed by the tensor product of `V`.

This is the structural input needed to view cocommutative Hopf algebras as the internal groups
`Grp (CommComon V)` of a cartesian monoidal category, and thus to apply to them the general theory
of Newman's correspondence (`InternalGroups/SubgroupCorrespondence.lean`). In the paper,
`Hopf_A^coc` is defined as `Grp(Comon_A^coc)` in Section 6.3, before Corollary 6.11.

## Main results

* `UlmerBialgebras.CocommComon.fst`, `UlmerBialgebras.CocommComon.snd` — the two projections
  `A ⊗ B ⟶ A`, `A ⊗ B ⟶ B` of a tensor product of comonoids, obtained by counting out one
  factor; they are morphisms of comonoids;
* `UlmerBialgebras.CocommComon.lift` — the pairing `⟨f, g⟩ = Δ ≫ (f ⊗ g)` of two comonoid morphisms
  out of a comonoid; when the source is **cocommutative** it is a morphism of comonoids
  (`UlmerBialgebras.CocommComon.isComonHom_lift`, via `UlmerBialgebras.CocommComon.comul_tensorμ`);
* `UlmerBialgebras.CommComon.binaryFanIsLimit` — the resulting binary fan is a limit cone, so
  `CommComon V` has binary products; together with the terminal object `𝟙_ V` this gives
  `HasFiniteProducts (CommComon V)` and hence a `CartesianMonoidalCategory` structure on
  `CommComon V`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 6.3 and Corollary 6.11
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory Limits ComonObj BraidedCategory

namespace CocommComon

section Braided

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]

/-! ## Iterated comultiplication -/

/-- Applying the comultiplication three times, written with the four resulting copies
grouped as `(1 ⊗ 2) ⊗ (3 ⊗ 4)` on the left and as `1 ⊗ ((2 ⊗ 3) ⊗ 4)` on the right. -/
theorem coassoc4 (T : V) [ComonObj T] :
    Δ[T] ≫ (Δ[T] ⊗ₘ Δ[T]) = Δ[T] ≫ (Δ[T] ▷ T) ≫ (α_ T T T).hom ≫ (T ◁ (Δ[T] ▷ T)) ≫
      (T ◁ (α_ T T T).hom) ≫ (α_ T T (T ⊗ T)).inv := by
  rw [← comul_assoc_assoc, MonoidalCategory.tensorHom_def, comul_assoc_flip_assoc]
  have hnat : (α_ T T T).inv ≫ ((T ⊗ T) ◁ Δ[T])
      = (T ◁ (T ◁ Δ[T])) ≫ (α_ T T (T ⊗ T)).inv := by simp
  have hmid : T ◁ (Δ[T] ≫ T ◁ Δ[T])
      = (T ◁ (Δ[T] ≫ Δ[T] ▷ T)) ≫ (T ◁ (α_ T T T).hom) := by
    rw [← MonoidalCategory.whiskerLeft_comp, Category.assoc, ← comul_assoc]
  rw [hnat, ← Category.assoc (T ◁ Δ[T]), ← MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc (T ◁ Δ[T]), ← MonoidalCategory.whiskerLeft_comp, hmid]
  simp

/-! ## The projections and the pairing: definitions -/

section ProjectionDefs

variable (A B : V) [ComonObj A] [ComonObj B]

/-- The first projection of a tensor product of comonoids. -/
noncomputable def fst : A ⊗ B ⟶ A := (A ◁ ε[B]) ≫ (ρ_ A).hom

/-- The second projection of a tensor product of comonoids. -/
noncomputable def snd : A ⊗ B ⟶ B := (ε[A] ▷ B) ≫ (λ_ B).hom

end ProjectionDefs

section LiftDefs

variable {T A B : V} [ComonObj T]

/-- The pairing of two morphisms out of a comonoid. -/
noncomputable def lift (f : T ⟶ A) (g : T ⟶ B) : T ⟶ A ⊗ B := Δ[T] ≫ (f ⊗ₘ g)

/-- `lift f g ≫ fst A B = f` when `g` is a morphism of comonoids. -/
@[reassoc (attr := simp)]
theorem lift_fst [ComonObj B] (f : T ⟶ A) (g : T ⟶ B) [IsComonHom g] :
    lift f g ≫ fst A B = f := by
  rw [lift, fst, Category.assoc, ← Category.assoc (f ⊗ₘ g), ← id_tensorHom A ε[B],
    tensorHom_comp_tensorHom, Category.comp_id, IsComonHom.hom_counit, ← Category.assoc,
    comul_counit_hom]
  simp

/-- `lift f g ≫ snd A B = g` when `f` is a morphism of comonoids. -/
@[reassoc (attr := simp)]
theorem lift_snd [ComonObj A] (f : T ⟶ A) (g : T ⟶ B) [IsComonHom f] :
    lift f g ≫ snd A B = g := by
  rw [lift, snd, Category.assoc, ← Category.assoc (f ⊗ₘ g),
    ← MonoidalCategory.tensorHom_id ε[A] B, tensorHom_comp_tensorHom, Category.comp_id,
    IsComonHom.hom_counit, ← Category.assoc, counit_comul_hom]
  simp

end LiftDefs

variable [BraidedCategory V]

/-- **The comultiplication of a cocommutative comonoid is a morphism of comonoids**: this is
its compatibility with the comultiplication of `T ⊗ T`. -/
@[reassoc]
theorem comul_tensorμ (T : V) [ComonObj T] [IsCommComonObj T] :
    Δ[T] ≫ (Δ[T] ⊗ₘ Δ[T]) ≫ tensorμ T T T T = Δ[T] ≫ (Δ[T] ⊗ₘ Δ[T]) := by
  conv_lhs => rw [← Category.assoc, coassoc4]
  rw [coassoc4]
  dsimp only [tensorμ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.comp_whiskerRight,
    IsCommComonObj.comul_comm]

/-! ## The projections -/

section Projections

variable (A B : V) [ComonObj A] [ComonObj B]

/-- The first projection `fst A B : A ⊗ B ⟶ A` is a morphism of comonoids. -/
instance isComonHom_fst : IsComonHom (fst A B) where
  hom_counit := by
    rw [fst, Category.assoc, Comon.tensorObj_counit, MonoidalCategory.tensorHom_def']
    simp [unitors_equal]
  hom_comul := by
    rw [fst, Comon.tensorObj_comul]
    simp only [Category.assoc]
    have key : tensorμ A A (𝟙_ V) (𝟙_ V) ≫ ((ρ_ A).hom ⊗ₘ (ρ_ A).hom)
        = ((A ⊗ A) ◁ (λ_ (𝟙_ V)).hom) ≫ (ρ_ (A ⊗ A)).hom := by
      rw [tensor_right_unitality A A]
      simp [← whiskerLeft_comp_assoc]
    have hB : Δ[B] ≫ (ε[B] ⊗ₘ ε[B]) ≫ (λ_ (𝟙_ V)).hom = ε[B] := by
      rw [← Category.assoc, counit_comul_hom]; simp
    rw [← tensorHom_comp_tensorHom, ← Category.assoc (tensorμ A A B B),
      ← tensorμ_natural_right A A ε[B] ε[B], Category.assoc, key,
      ← whiskerLeft_comp_assoc, ← Category.assoc,
      ← id_tensorHom (A ⊗ A) ((ε[B] ⊗ₘ ε[B]) ≫ (λ_ (𝟙_ V)).hom),
      tensorHom_comp_tensorHom_assoc, Category.comp_id, hB, MonoidalCategory.tensorHom_def']
    simp

/-- The second projection `snd A B : A ⊗ B ⟶ B` is a morphism of comonoids. -/
instance isComonHom_snd : IsComonHom (snd A B) where
  hom_counit := by
    rw [snd, Category.assoc, Comon.tensorObj_counit, MonoidalCategory.tensorHom_def]
    simp
  hom_comul := by
    rw [snd, Comon.tensorObj_comul]
    simp only [Category.assoc]
    have key : tensorμ (𝟙_ V) (𝟙_ V) B B ≫ ((λ_ B).hom ⊗ₘ (λ_ B).hom)
        = ((λ_ (𝟙_ V)).hom ▷ (B ⊗ B)) ≫ (λ_ (B ⊗ B)).hom := by
      rw [tensor_left_unitality B B]
      simp
    have hA : Δ[A] ≫ (ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ V)).hom = ε[A] := by
      rw [← Category.assoc, counit_comul_hom]; simp
    rw [← tensorHom_comp_tensorHom, ← Category.assoc (tensorμ A A B B),
      ← tensorμ_natural_left ε[A] ε[A] B B, Category.assoc, key,
      ← comp_whiskerRight_assoc, ← Category.assoc,
      ← tensorHom_id ((ε[A] ⊗ₘ ε[A]) ≫ (λ_ (𝟙_ V)).hom) (B ⊗ B),
      tensorHom_comp_tensorHom_assoc, Category.comp_id, hA, MonoidalCategory.tensorHom_def]
    simp

/-- The comultiplication of `A ⊗ B` followed by the tensor product of the two projections is the
identity: `Δ[A ⊗ B] ≫ (fst A B ⊗ₘ snd A B) = 𝟙 (A ⊗ B)`. -/
theorem lift_fst_snd : Δ[A ⊗ B] ≫ (fst A B ⊗ₘ snd A B) = 𝟙 (A ⊗ B) := by
  rw [fst, snd, ← tensorHom_comp_tensorHom, Comon.tensorObj_comul]
  simp only [Category.assoc]
  rw [← id_tensorHom A ε[B], ← MonoidalCategory.tensorHom_id ε[A] B,
    ← tensorμ_natural_assoc (𝟙 A) ε[A] ε[B] (𝟙 B),
    ← Category.assoc, tensorHom_comp_tensorHom, id_tensorHom, MonoidalCategory.tensorHom_id,
    comul_counit, counit_comul]
  dsimp only [tensorμ]
  simp only [braiding_tensorUnit_right, Category.assoc]
  monoidal

end Projections

/-! ## The pairing -/

section Lift

variable {T A B : V} [ComonObj T] [ComonObj A] [ComonObj B]

/-- If `T` is cocommutative and `f`, `g` are morphisms of comonoids, then so is `lift f g`. -/
instance isComonHom_lift [IsCommComonObj T] (f : T ⟶ A) (g : T ⟶ B) [IsComonHom f]
    [IsComonHom g] : IsComonHom (lift f g) where
  hom_counit := by
    rw [lift, Category.assoc, Comon.tensorObj_counit, ← Category.assoc (f ⊗ₘ g),
      tensorHom_comp_tensorHom, IsComonHom.hom_counit, IsComonHom.hom_counit,
      ← Category.assoc, counit_comul_hom]
    simp
  hom_comul := by
    rw [lift, Category.assoc, Comon.tensorObj_comul, ← Category.assoc (f ⊗ₘ g),
      tensorHom_comp_tensorHom, IsComonHom.hom_comul, IsComonHom.hom_comul,
      ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [tensorμ_natural, comul_tensorμ_assoc]
    simp [← tensorHom_comp_tensorHom]

/-- Two comonoid morphisms into a tensor product agree as soon as their two components
agree. -/
theorem hom_ext {h k : T ⟶ A ⊗ B} [IsComonHom h] [IsComonHom k]
    (h₁ : h ≫ fst A B = k ≫ fst A B) (h₂ : h ≫ snd A B = k ≫ snd A B) : h = k := by
  have expand : ∀ (u : T ⟶ A ⊗ B), IsComonHom u →
      u = Δ[T] ≫ ((u ≫ fst A B) ⊗ₘ (u ≫ snd A B)) := by
    intro u _
    rw [← tensorHom_comp_tensorHom, ← Category.assoc, ← IsComonHom.hom_comul,
      Category.assoc, lift_fst_snd, Category.comp_id]
  rw [expand h inferInstance, expand k inferInstance, h₁, h₂]

end Lift

end Braided

/-! ## Cocommutativity of a tensor product -/

section Symmetric

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]

end Symmetric

end CocommComon

/-! ## Finite products in the category of cocommutative comonoids -/

namespace CommComon

open CocommComon

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]

/-- A morphism of cocommutative comonoids, from a morphism of the underlying objects which
is compatible with the comonoid structures. -/
def homMk {A B : CommComon V} (f : A.X ⟶ B.X) [IsComonHom f] : A ⟶ B :=
  InducedCategory.homMk (F := CommComon.toComon)
    (Comon.Hom.mk (isComonHom_hom := ‹IsComonHom f›) f)

/-- The underlying morphism of `homMk f` is `f`. -/
@[simp]
lemma homMk_hom {A B : CommComon V} (f : A.X ⟶ B.X) [IsComonHom f] :
    (homMk f).hom.hom = f := rfl

/-- The trivial cocommutative comonoid is a terminal object. -/
noncomputable def trivialIsTerminal : IsTerminal (CommComon.trivial V) := by
  refine IsTerminal.ofUnique (h := fun A => ?_)
  exact Equiv.unique (α := (A ⟶ CommComon.trivial V)) (β := (A.toComon ⟶ Comon.trivial V))
    InducedCategory.homEquiv

/-- The category of cocommutative comonoids has a terminal object. -/
instance : HasTerminal (CommComon V) := trivialIsTerminal.hasTerminal

/-- The underlying map of a morphism of cocommutative comonoids is a comonoid morphism. -/
instance isComonHom_hom_hom {A B : CommComon V} (f : A ⟶ B) :
    IsComonHom (M := A.X) (N := B.X) f.hom.hom :=
  f.hom.isComonHom_hom

/-- The tensor product of two cocommutative comonoids, as a cocommutative comonoid. -/
noncomputable abbrev tensorObj (A B : CommComon V) : CommComon V where
  X := A.X ⊗ B.X

/-- The binary fan on two cocommutative comonoids given by their tensor product and the two
counit projections. -/
@[implicit_reducible]
noncomputable def binaryFan (A B : CommComon V) : BinaryFan A B :=
  BinaryFan.mk (P := tensorObj A B) (homMk (fst A.X B.X)) (homMk (snd A.X B.X))

/-- **The tensor product of cocommutative comonoids is their categorical product.** -/
noncomputable def binaryFanIsLimit (A B : CommComon V) : IsLimit (binaryFan A B) :=
  BinaryFan.IsLimit.mk _
    (fun {T} f g =>
      haveI : IsComonHom (M := T.X) (N := A.X ⊗ B.X) (lift f.hom.hom g.hom.hom) :=
        isComonHom_lift _ _
      homMk (A := T) (B := tensorObj A B) (lift f.hom.hom g.hom.hom))
    (fun {T} f g => by ext; exact lift_fst (T := T.X) (A := A.X) (B := B.X) f.hom.hom g.hom.hom)
    (fun {T} f g => by ext; exact lift_snd (T := T.X) (A := A.X) (B := B.X) f.hom.hom g.hom.hom)
    (fun {T} f g m h₁ h₂ => by
      ext
      have : IsComonHom (M := T.X) (N := A.X ⊗ B.X) m.hom.hom := isComonHom_hom_hom m
      have : IsComonHom (M := T.X) (N := A.X ⊗ B.X) (lift f.hom.hom g.hom.hom) :=
        isComonHom_lift _ _
      refine CocommComon.hom_ext (T := T.X) (A := A.X) (B := B.X) ?_ ?_
      · exact (congr(($(h₁)).hom.hom)).trans
          (lift_fst (T := T.X) (A := A.X) (B := B.X) f.hom.hom g.hom.hom).symm
      · exact (congr(($(h₂)).hom.hom)).trans
          (lift_snd (T := T.X) (A := A.X) (B := B.X) f.hom.hom g.hom.hom).symm)

/-- Any two cocommutative comonoids have a binary product, given by their tensor product. -/
instance hasLimitPair (A B : CommComon V) : HasLimit (pair A B) :=
  ⟨_, binaryFanIsLimit A B⟩

/-- The category of cocommutative comonoids has binary products. -/
instance : HasBinaryProducts (CommComon V) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The category of cocommutative comonoids has finite products. -/
instance : HasFiniteProducts (CommComon V) := hasFiniteProducts_of_has_binary_and_terminal

/-- **The category of cocommutative comonoids in a symmetric monoidal category is cartesian
monoidal**, with the tensor product of `V` as categorical product (Fox's theorem
[foxCoalgebrasCartesianCategories1976], `binaryFanIsLimit`) and the trivial comonoid as terminal
object. The products are the chosen Fox cones, so `A ⊗ B` is `tensorObj A B` and the projections
are the counit projections, by definition. -/
noncomputable instance : CartesianMonoidalCategory (CommComon V) :=
  .ofChosenFiniteProducts ⟨_, trivialIsTerminal⟩
    (fun A B => ⟨binaryFan A B, binaryFanIsLimit A B⟩)

end CommComon

end UlmerBialgebras
