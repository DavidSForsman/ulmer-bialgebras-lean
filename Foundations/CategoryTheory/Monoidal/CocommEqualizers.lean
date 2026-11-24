module
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.CommComon_
public import Foundations.CategoryTheory.Monoidal.CocommProducts
public import Foundations.CategoryTheory.Exact.CoreflexiveTransport

/-!
# Coreflexive equalizers of cocommutative comonoids

Let `V` be a monoidal category.  This file proves that the equalizer of a **coreflexive pair**
`f g : X ⟶ Y` of comonoids (a pair with a common retraction `r : Y ⟶ X`, `f ≫ r = 𝟙 X = g ≫ r`)
carries a comonoid structure, and that the equalizer map is a morphism of comonoids, under the
hypothesis that tensoring in either variable preserves coreflexive equalizers.

The construction is the standard one.  Let `e : E ⟶ X` be the equalizer of the underlying
morphisms in `V`.  The candidate comultiplication `d = e ≫ Δ_X` satisfies
`d ≫ (f ⊗ 𝟙) = d ≫ (g ⊗ 𝟙)` because `Δ_X ≫ (u ⊗ 𝟙) = u ≫ Δ_Y ≫ (𝟙 ⊗ r)` for
`u ∈ {f, g}` (using `u ≫ r = 𝟙` and that `u` is a comonoid morphism).  Since `E ⊗ X` is the
equalizer of `f ⊗ 𝟙` and `g ⊗ 𝟙`, `d` factors through `E ⊗ X` as `d₁`.  The mirror identity
`d₁ ≫ (𝟙 ⊗ f) = d₁ ≫ (𝟙 ⊗ g)` is obtained by cancelling the monomorphism `e ⊗ 𝟙`; since `E ⊗ E`
is the equalizer of `𝟙 ⊗ f` and `𝟙 ⊗ g`, `d₁` factors as `Δ₀ ≫ (𝟙 ⊗ e)`, and
`Δ₀ ≫ (e ⊗ e) = e ≫ Δ_X`.  The counit is `e ≫ ε_X`; the comonoid axioms are inherited from `X`
by cancelling the monomorphisms `e` and `(e ⊗ e) ⊗ e` (see below), and cocommutativity is
inherited by cancelling `e ⊗ e`.

All the monomorphisms used are images of the coreflexive pair `(f, g)` (or of the derived
coreflexive pairs `(f ⊗ 𝟙, g ⊗ 𝟙)` and `(𝟙 ⊗ f, 𝟙 ⊗ g)`) under the tensor functors, so the
single hypothesis that tensoring preserves coreflexive equalizers componentwise suffices.

## Main results

* `UlmerBialgebras.coreflexiveComonObj`: the comonoid structure on the equalizer;
* `UlmerBialgebras.isComonHom_coreflexiveEqι`: the equalizer map is a comonoid morphism;
* `UlmerBialgebras.isCommComonObj_coreflexiveEq`: the equalizer comonoid is cocommutative;
* the equalizer is an equalizer in `CommComon A`:
  `Foundations/CategoryTheory/Monoidal/CommComonEqualizers.lean`.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/



@[expose] public section
universe v u
open CategoryTheory MonoidalCategory Limits
open scoped ComonObj

namespace UlmerBialgebras

section Generic

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]

/-- A limit fork whose leg is the image of the equalizer map under a functor.  This is Mathlib's
`Limits.isLimitOfHasEqualizerOfPreservesLimit`. -/
noncomputable abbrev isLimitMapFork {X Y : V} {u v : X ⟶ Y} [HasEqualizer u v] (F : V ⥤ V)
    [PreservesLimit (parallelPair u v) F] :
    IsLimit (Fork.ofι (f := F.map u) (g := F.map v) (F.map (equalizer.ι u v))
      (by simp only [← F.map_comp]; rw [equalizer.condition])) :=
  Limits.isLimitOfHasEqualizerOfPreservesLimit F u v

variable {X Y : V} [ComonObj X] [ComonObj Y]
variable {f g : X ⟶ Y} [IsComonHom f] [IsComonHom g]

/-- `Δ_X` followed by the tensor with a retraction. -/
lemma comul_comp_tensor_id {u : X ⟶ Y} [IsComonHom u] {r : Y ⟶ X} (hu : u ≫ r = 𝟙 X) :
    Δ[X] ≫ (u ⊗ₘ 𝟙 X) = u ≫ Δ[Y] ≫ (𝟙 Y ⊗ₘ r) := by
  have h : (u ⊗ₘ u) ≫ (𝟙 Y ⊗ₘ r) = u ⊗ₘ 𝟙 X := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, hu]
  rw [← h, ← Category.assoc, ← IsComonHom.hom_comul, Category.assoc]

/-- The mirror of `comul_comp_tensor_id`. -/
lemma comul_comp_id_tensor {u : X ⟶ Y} [IsComonHom u] {r : Y ⟶ X} (hu : u ≫ r = 𝟙 X) :
    Δ[X] ≫ (𝟙 X ⊗ₘ u) = u ≫ Δ[Y] ≫ (r ⊗ₘ 𝟙 Y) := by
  have h : (u ⊗ₘ u) ≫ (r ⊗ₘ 𝟙 Y) = 𝟙 X ⊗ₘ u := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, hu]
  rw [← h, ← Category.assoc, ← IsComonHom.hom_comul, Category.assoc]

omit [MonoidalCategory V] in
/-- The image under `F` of the leg of a limit fork is a monomorphism, when `F` preserves the
fork's parallel pair.  This is Mathlib's `Limits.isLimitForkMapOfIsLimit`. -/
lemma mono_map_fork_ι {A B W : V} {u v : A ⟶ B} {h : W ⟶ A} {w : h ≫ u = h ≫ v}
    (ht : IsLimit (Fork.ofι h w)) (F : V ⥤ V)
    [PreservesLimit (parallelPair u v) F] : Mono (F.map h) :=
  Fork.IsLimit.mono (Limits.isLimitForkMapOfIsLimit F w ht)

/-- The action of `tensorRight Z` on morphisms. -/
lemma tensorRight_map_eq (Z : V) {A B : V} (u : A ⟶ B) :
    (tensorRight Z).map u = u ⊗ₘ 𝟙 Z := by
  simp [tensorRight, MonoidalCategory.curriedTensor]

/-- The action of `tensorLeft Z` on morphisms. -/
lemma tensorLeft_map_eq (Z : V) {A B : V} (u : A ⟶ B) :
    (tensorLeft Z).map u = 𝟙 Z ⊗ₘ u := by
  simp [tensorLeft, MonoidalCategory.curriedTensor]

end Generic


/-- Tensoring in either variable preserves coreflexive equalizers.  This is the conjunction of
Mathlib's `Comonad.PreservesLimitOfIsCoreflexivePair` for the two tensor functors, so the
preservation predicate itself is not duplicated. -/
class TensorPreservesCoreflexiveEqualizers (V : Type u) [Category.{v} V]
    [MonoidalCategory.{v} V] : Prop where
  preserves_left : ∀ Z : V, Comonad.PreservesLimitOfIsCoreflexivePair (tensorLeft Z)
  preserves_right : ∀ Z : V, Comonad.PreservesLimitOfIsCoreflexivePair (tensorRight Z)

/-- The left tensor functor preserves coreflexive equalizers. -/
instance tensorLeft_preservesLimitOfIsCoreflexivePair {V : Type u} [Category.{v} V]
    [MonoidalCategory.{v} V] (Z : V) [TensorPreservesCoreflexiveEqualizers V] :
    Comonad.PreservesLimitOfIsCoreflexivePair (tensorLeft Z) :=
  TensorPreservesCoreflexiveEqualizers.preserves_left Z

/-- The right tensor functor preserves coreflexive equalizers. -/
instance tensorRight_preservesLimitOfIsCoreflexivePair {V : Type u} [Category.{v} V]
    [MonoidalCategory.{v} V] (Z : V) [TensorPreservesCoreflexiveEqualizers V] :
    Comonad.PreservesLimitOfIsCoreflexivePair (tensorRight Z) :=
  TensorPreservesCoreflexiveEqualizers.preserves_right Z

section Coreflexive

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
variable {X Y : V} [ComonObj X] [ComonObj Y]
variable {f g : X ⟶ Y} [IsComonHom f] [IsComonHom g] [IsCoreflexivePair f g]

/-- The tensor of a coreflexive pair with an object on the right is coreflexive. -/
instance isCoreflexivePair_tensorRight (Z : V) :
    IsCoreflexivePair (f ⊗ₘ 𝟙 Z) (g ⊗ₘ 𝟙 Z) :=
  IsCoreflexivePair.mk' (commonRetraction f g ⊗ₘ 𝟙 Z)
    (by rw [tensorHom_comp_tensorHom, left_comp_retraction, Category.comp_id,
      id_tensorHom_id])
    (by rw [tensorHom_comp_tensorHom, right_comp_retraction, Category.comp_id,
      id_tensorHom_id])

/-- The tensor of a coreflexive pair with an object on the left is coreflexive. -/
instance isCoreflexivePair_tensorLeft (Z : V) :
    IsCoreflexivePair (𝟙 Z ⊗ₘ f) (𝟙 Z ⊗ₘ g) :=
  IsCoreflexivePair.mk' (𝟙 Z ⊗ₘ commonRetraction f g)
    (by rw [tensorHom_comp_tensorHom, left_comp_retraction, Category.id_comp,
      id_tensorHom_id])
    (by rw [tensorHom_comp_tensorHom, right_comp_retraction, Category.id_comp,
      id_tensorHom_id])

end Coreflexive


section Equalizer

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
variable {X Y : V} [ComonObj X] [ComonObj Y]
variable {f g : X ⟶ Y} [IsComonHom f] [IsComonHom g] [IsCoreflexivePair f g]
variable [HasEqualizer f g]

/-- The underlying equalizer of a coreflexive pair of comonoids. -/
noncomputable abbrev coreflexiveEq : V := equalizer f g

/-- The equalizer map of a coreflexive pair of comonoids. -/
noncomputable abbrev coreflexiveEqι : coreflexiveEq (f := f) (g := g) ⟶ X :=
  equalizer.ι f g

/-- `e ≫ Δ_X`, the candidate comultiplication before the first factorization. -/
noncomputable def coreflexiveD : coreflexiveEq (f := f) (g := g) ⟶ X ⊗ X :=
  coreflexiveEqι (f := f) (g := g) ≫ Δ[X]

/-- The first factorization identity. -/
lemma coreflexiveD_comp_tensor :
    coreflexiveD (f := f) (g := g) ≫ (f ⊗ₘ 𝟙 X) =
      coreflexiveD (f := f) (g := g) ≫ (g ⊗ₘ 𝟙 X) := by
  have h1 := comul_comp_tensor_id (u := f) (left_comp_retraction f g)
  have h2 := comul_comp_tensor_id (u := g) (right_comp_retraction f g)
  have hcond : coreflexiveEqι (f := f) (g := g) ≫ f =
      coreflexiveEqι (f := f) (g := g) ≫ g := equalizer.condition f g
  calc coreflexiveD (f := f) (g := g) ≫ (f ⊗ₘ 𝟙 X)
      = coreflexiveEqι (f := f) (g := g) ≫ (Δ[X] ≫ (f ⊗ₘ 𝟙 X)) := by
        rw [coreflexiveD, Category.assoc]
    _ = coreflexiveEqι (f := f) (g := g) ≫
          (f ≫ Δ[Y] ≫ (𝟙 Y ⊗ₘ commonRetraction f g)) := by rw [h1]
    _ = coreflexiveEqι (f := f) (g := g) ≫
          (g ≫ Δ[Y] ≫ (𝟙 Y ⊗ₘ commonRetraction f g)) := by
        rw [← Category.assoc, ← Category.assoc, hcond, Category.assoc, Category.assoc]
    _ = coreflexiveEqι (f := f) (g := g) ≫ (Δ[X] ≫ (g ⊗ₘ 𝟙 X)) := by rw [h2]
    _ = coreflexiveD (f := f) (g := g) ≫ (g ⊗ₘ 𝟙 X) := by
        rw [coreflexiveD, Category.assoc]

/-- The second (mirror) factorization identity. -/
lemma coreflexiveD_comp_id_tensor :
    coreflexiveD (f := f) (g := g) ≫ (𝟙 X ⊗ₘ f) =
      coreflexiveD (f := f) (g := g) ≫ (𝟙 X ⊗ₘ g) := by
  have h1 := comul_comp_id_tensor (u := f) (left_comp_retraction f g)
  have h2 := comul_comp_id_tensor (u := g) (right_comp_retraction f g)
  have hcond : coreflexiveEqι (f := f) (g := g) ≫ f =
      coreflexiveEqι (f := f) (g := g) ≫ g := equalizer.condition f g
  calc coreflexiveD (f := f) (g := g) ≫ (𝟙 X ⊗ₘ f)
      = coreflexiveEqι (f := f) (g := g) ≫ (Δ[X] ≫ (𝟙 X ⊗ₘ f)) := by
        rw [coreflexiveD, Category.assoc]
    _ = coreflexiveEqι (f := f) (g := g) ≫
          (f ≫ Δ[Y] ≫ (commonRetraction f g ⊗ₘ 𝟙 Y)) := by rw [h1]
    _ = coreflexiveEqι (f := f) (g := g) ≫
          (g ≫ Δ[Y] ≫ (commonRetraction f g ⊗ₘ 𝟙 Y)) := by
        rw [← Category.assoc, ← Category.assoc, hcond, Category.assoc, Category.assoc]
    _ = coreflexiveEqι (f := f) (g := g) ≫ (Δ[X] ≫ (𝟙 X ⊗ₘ g)) := by rw [h2]
    _ = coreflexiveD (f := f) (g := g) ≫ (𝟙 X ⊗ₘ g) := by
        rw [coreflexiveD, Category.assoc]

end Equalizer


section Factor

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
variable {X Y : V} [ComonObj X] [ComonObj Y]
variable {f g : X ⟶ Y} [IsComonHom f] [IsComonHom g] [IsCoreflexivePair f g]
variable [HasEqualizer f g] [TensorPreservesCoreflexiveEqualizers V]

/-- The factorization of `d` through `E ⊗ X`, the equalizer of `f ⊗ 𝟙` and `g ⊗ 𝟙`. -/
noncomputable def coreflexiveD₁ :
    coreflexiveEq (f := f) (g := g) ⟶ coreflexiveEq (f := f) (g := g) ⊗ X :=
  (isLimitMapFork (u := f) (v := g) (tensorRight X)).lift
    (Fork.ofι (f := (tensorRight X).map f) (g := (tensorRight X).map g)
      (coreflexiveD (f := f) (g := g)) (by
        rw [tensorRight_map_eq X, tensorRight_map_eq X]
        exact coreflexiveD_comp_tensor (f := f) (g := g)))

/-- The defining property of `coreflexiveD₁`. -/
lemma coreflexiveD₁_spec :
    coreflexiveD₁ (f := f) (g := g) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 X) =
      coreflexiveD (f := f) (g := g) := by
  have h := Fork.IsLimit.lift_ι (isLimitMapFork (u := f) (v := g) (tensorRight X))
    (t := Fork.ofι (f := (tensorRight X).map f) (g := (tensorRight X).map g)
      (coreflexiveD (f := f) (g := g)) (by
        rw [tensorRight_map_eq X, tensorRight_map_eq X]
        exact coreflexiveD_comp_tensor (f := f) (g := g)))
  have h' : coreflexiveD₁ (f := f) (g := g) ≫
      (tensorRight X).map (coreflexiveEqι (f := f) (g := g)) =
        coreflexiveD (f := f) (g := g) := by
    simpa only [coreflexiveD₁, Fork.ι_ofι] using h
  rw [tensorRight_map_eq X] at h'
  exact h'

/-- The mirror identity for `coreflexiveD₁`. -/
lemma coreflexiveD₁_comp_id_tensor :
    coreflexiveD₁ (f := f) (g := g) ≫
        (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ f) =
      coreflexiveD₁ (f := f) (g := g) ≫
        (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ g) := by
  have hmono : Mono (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 Y) := by
    have h := Fork.IsLimit.mono (isLimitMapFork (u := f) (v := g) (tensorRight Y))
    have h' : Mono ((tensorRight Y).map (coreflexiveEqι (f := f) (g := g))) := by
      simpa only [Fork.ι_ofι] using h
    rwa [tensorRight_map_eq] at h'
  apply (cancel_mono (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 Y)).mp
  have hleft : (coreflexiveD₁ (f := f) (g := g) ≫
      (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ f)) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 Y) =
      coreflexiveD (f := f) (g := g) ≫ (𝟙 X ⊗ₘ f) := by
    have h1 : (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ f) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 Y) =
          coreflexiveEqι (f := f) (g := g) ⊗ₘ f := by
      rw [tensorHom_comp_tensorHom]
      simp
    have h2 : (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 X) ≫ (𝟙 X ⊗ₘ f) =
        coreflexiveEqι (f := f) (g := g) ⊗ₘ f := by
      rw [tensorHom_comp_tensorHom]
      simp
    rw [Category.assoc, h1, ← h2, ← Category.assoc, coreflexiveD₁_spec]
  have hright : (coreflexiveD₁ (f := f) (g := g) ≫
      (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ g)) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 Y) =
      coreflexiveD (f := f) (g := g) ≫ (𝟙 X ⊗ₘ g) := by
    have h1 : (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ g) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 Y) =
          coreflexiveEqι (f := f) (g := g) ⊗ₘ g := by
      rw [tensorHom_comp_tensorHom]
      simp
    have h2 : (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 X) ≫ (𝟙 X ⊗ₘ g) =
        coreflexiveEqι (f := f) (g := g) ⊗ₘ g := by
      rw [tensorHom_comp_tensorHom]
      simp
    rw [Category.assoc, h1, ← h2, ← Category.assoc, coreflexiveD₁_spec]
  exact hleft.trans ((coreflexiveD_comp_id_tensor (f := f) (g := g)).trans hright.symm)

end Factor


section SecondFactor

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
variable {X Y : V} [ComonObj X] [ComonObj Y]
variable {f g : X ⟶ Y} [IsComonHom f] [IsComonHom g] [IsCoreflexivePair f g]
variable [HasEqualizer f g] [TensorPreservesCoreflexiveEqualizers V]

/-- The second factorization of `d` through `E ⊗ E`. -/
noncomputable def coreflexiveD₂ :
    coreflexiveEq (f := f) (g := g) ⟶
      coreflexiveEq (f := f) (g := g) ⊗ coreflexiveEq (f := f) (g := g) :=
  (isLimitMapFork (u := f) (v := g)
      (tensorLeft (coreflexiveEq (f := f) (g := g)))).lift
    (Fork.ofι (f := (tensorLeft (coreflexiveEq (f := f) (g := g))).map f)
      (g := (tensorLeft (coreflexiveEq (f := f) (g := g))).map g)
      (coreflexiveD₁ (f := f) (g := g)) (by
        rw [tensorLeft_map_eq (coreflexiveEq (f := f) (g := g)),
          tensorLeft_map_eq (coreflexiveEq (f := f) (g := g))]
        exact coreflexiveD₁_comp_id_tensor (f := f) (g := g)))

/-- The defining property of `coreflexiveD₂`. -/
lemma coreflexiveD₂_spec :
    coreflexiveD₂ (f := f) (g := g) ≫
        (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ coreflexiveEqι (f := f) (g := g)) =
      coreflexiveD₁ (f := f) (g := g) := by
  have h := Fork.IsLimit.lift_ι
    (isLimitMapFork (u := f) (v := g)
      (tensorLeft (coreflexiveEq (f := f) (g := g))))
    (t := Fork.ofι (f := (tensorLeft (coreflexiveEq (f := f) (g := g))).map f)
      (g := (tensorLeft (coreflexiveEq (f := f) (g := g))).map g)
      (coreflexiveD₁ (f := f) (g := g)) (by
        rw [tensorLeft_map_eq (coreflexiveEq (f := f) (g := g)),
          tensorLeft_map_eq (coreflexiveEq (f := f) (g := g))]
        exact coreflexiveD₁_comp_id_tensor (f := f) (g := g)))
  have h' : coreflexiveD₂ (f := f) (g := g) ≫
      (tensorLeft (coreflexiveEq (f := f) (g := g))).map
        (coreflexiveEqι (f := f) (g := g)) =
          coreflexiveD₁ (f := f) (g := g) := by
    simpa only [coreflexiveD₂, Fork.ι_ofι] using h
  rw [tensorLeft_map_eq (coreflexiveEq (f := f) (g := g))] at h'
  exact h'

/-- The composite of `coreflexiveD₂` with `e ⊗ e` is `d`. -/
lemma coreflexiveD₂_comp_tensor :
    coreflexiveD₂ (f := f) (g := g) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) =
      coreflexiveD (f := f) (g := g) := by
  have h : coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g) =
      (𝟙 (coreflexiveEq (f := f) (g := g)) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ≫
        (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 X) := by
    rw [tensorHom_comp_tensorHom]
    simp
  rw [h, ← Category.assoc, coreflexiveD₂_spec, coreflexiveD₁_spec]

end SecondFactor


section TripleMono

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
variable {X Y : V} {f g : X ⟶ Y} [IsCoreflexivePair f g]
variable [HasEqualizer f g] [TensorPreservesCoreflexiveEqualizers V]

/-- The pair `(f ⊗ 𝟙 Z, g ⊗ 𝟙 Z)` is coreflexive, in the form produced by `tensorRight`. -/
instance isCoreflexivePair_tensorRight_map (Z : V) :
    IsCoreflexivePair ((tensorRight Z).map f) ((tensorRight Z).map g) := by
  rw [tensorRight_map_eq Z, tensorRight_map_eq Z]
  infer_instance

/-- The pair `(𝟙 Z ⊗ f, 𝟙 Z ⊗ g)` is coreflexive, in the form produced by `tensorLeft`. -/
instance isCoreflexivePair_tensorLeft_map (Z : V) :
    IsCoreflexivePair ((tensorLeft Z).map f) ((tensorLeft Z).map g) := by
  rw [tensorLeft_map_eq Z, tensorLeft_map_eq Z]
  infer_instance

/-- `e ⊗ e` is a monomorphism. -/
lemma mono_coreflexiveEqι_tensor :
    Mono (coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) := by
  have h1 : Mono (coreflexiveEqι (f := f) (g := g) ⊗ₘ
      (𝟙 (coreflexiveEq (f := f) (g := g)))) := by
    have h := Fork.IsLimit.mono
      (isLimitMapFork (u := f) (v := g) (tensorRight (coreflexiveEq (f := f) (g := g))))
    have h' : Mono ((tensorRight (coreflexiveEq (f := f) (g := g))).map
        (coreflexiveEqι (f := f) (g := g))) := by
      simpa only [Fork.ι_ofι] using h
    rwa [tensorRight_map_eq (coreflexiveEq (f := f) (g := g))] at h'
  have h2 : Mono ((𝟙 X) ⊗ₘ coreflexiveEqι (f := f) (g := g)) := by
    have h := Fork.IsLimit.mono (isLimitMapFork (u := f) (v := g) (tensorLeft X))
    have h' : Mono ((tensorLeft X).map (coreflexiveEqι (f := f) (g := g))) := by
      simpa only [Fork.ι_ofι] using h
    rwa [tensorLeft_map_eq X] at h'
  have h : coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g) =
      (coreflexiveEqι (f := f) (g := g) ⊗ₘ 𝟙 (coreflexiveEq (f := f) (g := g))) ≫
        (𝟙 X ⊗ₘ coreflexiveEqι (f := f) (g := g)) := by
    rw [tensorHom_comp_tensorHom]
    simp
  rw [h]
  infer_instance

/-- `(e ⊗ 𝟙 E) ⊗ 𝟙 E` is a monomorphism. -/
lemma mono_coreflexiveEqι_tensor_id_tensor :
    Mono ((coreflexiveEqι (f := f) (g := g) ⊗ₘ
      𝟙 (coreflexiveEq (f := f) (g := g))) ⊗ₘ 𝟙 (coreflexiveEq (f := f) (g := g))) := by
  have hmono := mono_map_fork_ι
    (isLimitMapFork (u := f) (v := g) (tensorRight (coreflexiveEq (f := f) (g := g))))
    (tensorRight (coreflexiveEq (f := f) (g := g)))
  simpa only [Fork.ι_ofι, tensorRight_map_eq (coreflexiveEq (f := f) (g := g))] using hmono

/-- `(𝟙 X ⊗ e) ⊗ 𝟙 E` is a monomorphism. -/
lemma mono_id_tensor_coreflexiveEqι_tensor :
    Mono (((𝟙 X) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
      𝟙 (coreflexiveEq (f := f) (g := g))) := by
  have hmono := mono_map_fork_ι
    (isLimitMapFork (u := f) (v := g) (tensorLeft X))
    (tensorRight (coreflexiveEq (f := f) (g := g)))
  simpa only [Fork.ι_ofι, tensorLeft_map_eq X,
    tensorRight_map_eq (coreflexiveEq (f := f) (g := g))] using hmono

/-- `𝟙 (X ⊗ X) ⊗ e` is a monomorphism. -/
lemma mono_id_tensor_coreflexiveEqι :
    Mono ((𝟙 (X ⊗ X)) ⊗ₘ coreflexiveEqι (f := f) (g := g)) := by
  have hmono := Fork.IsLimit.mono
    (isLimitMapFork (u := f) (v := g) (tensorLeft (X ⊗ X)))
  simpa only [Fork.ι_ofι, tensorLeft_map_eq (X ⊗ X)] using hmono

/-- `(e ⊗ e) ⊗ 𝟙 E` is a monomorphism. -/
lemma mono_coreflexiveEqι_tensor_tensor_id :
    Mono ((coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
      𝟙 (coreflexiveEq (f := f) (g := g))) := by
  have hA1 := mono_coreflexiveEqι_tensor_id_tensor (f := f) (g := g)
  have hA2 := mono_id_tensor_coreflexiveEqι_tensor (f := f) (g := g)
  have h : coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g) =
      (coreflexiveEqι (f := f) (g := g) ⊗ₘ
          𝟙 (coreflexiveEq (f := f) (g := g))) ≫
        (𝟙 X ⊗ₘ coreflexiveEqι (f := f) (g := g)) := by
    rw [tensorHom_comp_tensorHom]
    simp
  have heq : (coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
      𝟙 (coreflexiveEq (f := f) (g := g)) =
      ((coreflexiveEqι (f := f) (g := g) ⊗ₘ
          𝟙 (coreflexiveEq (f := f) (g := g))) ⊗ₘ
          𝟙 (coreflexiveEq (f := f) (g := g))) ≫
        ((𝟙 X ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
          𝟙 (coreflexiveEq (f := f) (g := g))) := by
    rw [h]
    simp only [tensorHom_id]
    rw [comp_whiskerRight]
  rw [heq]
  infer_instance

/-- `(e ⊗ e) ⊗ e` is a monomorphism. -/
lemma mono_coreflexiveEqι_tensor_tensor :
    Mono ((coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
      coreflexiveEqι (f := f) (g := g)) := by
  have hA := mono_coreflexiveEqι_tensor_tensor_id (f := f) (g := g)
  have hB := mono_id_tensor_coreflexiveEqι (f := f) (g := g)
  have heq : (coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
      coreflexiveEqι (f := f) (g := g) =
      ((coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
          𝟙 (coreflexiveEq (f := f) (g := g))) ≫
        (𝟙 (X ⊗ X) ⊗ₘ coreflexiveEqι (f := f) (g := g)) := by
    rw [tensorHom_def, tensorHom_id, ← id_tensorHom]
  rw [heq]
  infer_instance

/-- `e ⊗ (e ⊗ e)` is a monomorphism. -/
lemma mono_coreflexiveEqι_tensor_tensor' :
    Mono (coreflexiveEqι (f := f) (g := g) ⊗ₘ
      (coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g))) := by
  have h := mono_coreflexiveEqι_tensor_tensor (f := f) (g := g)
  have heq : coreflexiveEqι (f := f) (g := g) ⊗ₘ
      (coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) =
      (α_ (coreflexiveEq (f := f) (g := g)) (coreflexiveEq (f := f) (g := g))
          (coreflexiveEq (f := f) (g := g))).inv ≫
        ((coreflexiveEqι (f := f) (g := g) ⊗ₘ coreflexiveEqι (f := f) (g := g)) ⊗ₘ
          coreflexiveEqι (f := f) (g := g)) ≫
        (α_ X X X).hom := by
    rw [associator_naturality]
    simp
  rw [heq]
  infer_instance

end TripleMono


section ComonoidStructure

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V]
variable {X Y : V} [ComonObj X] [ComonObj Y]
variable {f g : X ⟶ Y} [IsComonHom f] [IsComonHom g] [IsCoreflexivePair f g]
variable [HasEqualizer f g] [TensorPreservesCoreflexiveEqualizers V]

/-- The counit law for the equalizer comultiplication. -/
lemma coreflexiveD₂_counit_comul :
    coreflexiveD₂ (f := f) (g := g) ≫
      ((coreflexiveEqι (f := f) (g := g) ≫ ε[X]) ▷ coreflexiveEq (f := f) (g := g)) =
        (λ_ (coreflexiveEq (f := f) (g := g))).inv := by
  set E : V := coreflexiveEq (f := f) (g := g)
  set e' : E ⟶ X := coreflexiveEqι (f := f) (g := g)
  have hcounit : Δ[X] ≫ (ε[X] ⊗ₘ 𝟙 X) ≫ (λ_ X).hom = 𝟙 X := by
    rw [tensorHom_id, ← Category.assoc, ComonObj.counit_comul]
    simp
  have hε : ((e' ≫ ε[X]) ▷ E) ≫ (𝟙_ V ◁ e') = (e' ⊗ₘ e') ≫ (ε[X] ⊗ₘ 𝟙 X) := by
    rw [← tensorHom_id (e' ≫ ε[X]) E, ← id_tensorHom]
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp, tensorHom_comp_tensorHom]
  have hkey : ((coreflexiveD₂ (f := f) (g := g) ≫ ((e' ≫ ε[X]) ▷ E)) ≫
      (λ_ E).hom) ≫ e' = e' := by
    calc ((coreflexiveD₂ (f := f) (g := g) ≫ ((e' ≫ ε[X]) ▷ E)) ≫
          (λ_ E).hom) ≫ e'
        = ((coreflexiveD₂ (f := f) (g := g) ≫ ((e' ≫ ε[X]) ▷ E)) ≫
            ((𝟙_ V ◁ e') ≫ (λ_ X).hom)) := by
            rw [leftUnitor_naturality]
            simp only [Category.assoc]
      _ = (coreflexiveD₂ (f := f) (g := g) ≫
            (((e' ≫ ε[X]) ▷ E) ≫ (𝟙_ V ◁ e'))) ≫ (λ_ X).hom := by
            simp only [Category.assoc]
      _ = (coreflexiveD₂ (f := f) (g := g) ≫
            ((e' ⊗ₘ e') ≫ (ε[X] ⊗ₘ 𝟙 X))) ≫ (λ_ X).hom := by rw [hε]
      _ = ((coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ e')) ≫
            (ε[X] ⊗ₘ 𝟙 X)) ≫ (λ_ X).hom := by simp only [Category.assoc]
      _ = (e' ≫ (Δ[X] ≫ (ε[X] ⊗ₘ 𝟙 X) ≫ (λ_ X).hom)) := by
            rw [coreflexiveD₂_comp_tensor, coreflexiveD]
            simp only [e', Category.assoc]
      _ = e' := by rw [hcounit, Category.comp_id]
  have h1 : (coreflexiveD₂ (f := f) (g := g) ≫ ((e' ≫ ε[X]) ▷ E)) ≫
      (λ_ E).hom = 𝟙 E := by
    apply (cancel_mono e').mp
    rw [Category.id_comp]
    exact hkey
  exact (Iso.comp_hom_eq_id (λ_ E)).mp h1


/-- Left-hand side of `coreflexiveD₂_comul_assoc` composed with `e' ⊗ (e' ⊗ e')`. -/
private lemma coreflexiveD₂_comul_assoc_lhs :
    let E : V := coreflexiveEq (f := f) (g := g)
    let e' : E ⟶ X := coreflexiveEqι (f := f) (g := g)
    (coreflexiveD₂ (f := f) (g := g) ≫ (E ◁ coreflexiveD₂ (f := f) (g := g))) ≫
        (e' ⊗ₘ (e' ⊗ₘ e')) = (e' ≫ Δ[X]) ≫ (𝟙 X ⊗ₘ Δ[X]) := by
  intro E e'
  calc (coreflexiveD₂ (f := f) (g := g) ≫ (E ◁ coreflexiveD₂ (f := f) (g := g))) ≫
        (e' ⊗ₘ (e' ⊗ₘ e'))
      = coreflexiveD₂ (f := f) (g := g) ≫
          ((E ◁ coreflexiveD₂ (f := f) (g := g)) ≫ (e' ⊗ₘ (e' ⊗ₘ e'))) := Category.assoc _ _ _
    _ = coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ coreflexiveD (f := f) (g := g)) := by
          congr 1
          rw [← id_tensorHom, tensorHom_comp_tensorHom]
          simp only [Category.id_comp]
          rw [coreflexiveD₂_comp_tensor]
    _ = coreflexiveD₂ (f := f) (g := g) ≫ ((e' ⊗ₘ e') ≫ (𝟙 X ⊗ₘ Δ[X])) := by
          congr 1; rw [coreflexiveD, tensorHom_comp_tensorHom]; simp [e']
    _ = (coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ e')) ≫ (𝟙 X ⊗ₘ Δ[X]) := by
          simp only [Category.assoc]
    _ = (e' ≫ Δ[X]) ≫ (𝟙 X ⊗ₘ Δ[X]) := by rw [coreflexiveD₂_comp_tensor, coreflexiveD]

/-- Right-hand side of `coreflexiveD₂_comul_assoc` composed with `e' ⊗ (e' ⊗ e')`. -/
private lemma coreflexiveD₂_comul_assoc_rhs :
    let E : V := coreflexiveEq (f := f) (g := g)
    let e' : E ⟶ X := coreflexiveEqι (f := f) (g := g)
    (coreflexiveD₂ (f := f) (g := g) ≫
          (coreflexiveD₂ (f := f) (g := g) ▷ E) ≫ (α_ E E E).hom) ≫
        (e' ⊗ₘ (e' ⊗ₘ e')) = (e' ≫ Δ[X]) ≫ (Δ[X] ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom := by
  intro E e'
  calc (coreflexiveD₂ (f := f) (g := g) ≫ (coreflexiveD₂ (f := f) (g := g) ▷ E) ≫
        (α_ E E E).hom) ≫ (e' ⊗ₘ (e' ⊗ₘ e'))
      = coreflexiveD₂ (f := f) (g := g) ≫
          ((coreflexiveD₂ (f := f) (g := g) ▷ E) ≫
            ((α_ E E E).hom ≫ (e' ⊗ₘ (e' ⊗ₘ e')))) := by simp only [Category.assoc]
    _ = coreflexiveD₂ (f := f) (g := g) ≫
          (((coreflexiveD₂ (f := f) (g := g) ▷ E) ≫ ((e' ⊗ₘ e') ⊗ₘ e')) ≫
            (α_ X X X).hom) := by rw [← associator_naturality]; simp only [Category.assoc]
    _ = coreflexiveD₂ (f := f) (g := g) ≫
          ((coreflexiveD (f := f) (g := g) ⊗ₘ e') ≫ (α_ X X X).hom) := by
          congr 1
          rw [← tensorHom_id (coreflexiveD₂ (f := f) (g := g)) E, tensorHom_comp_tensorHom]
          simp only [Category.id_comp]
          rw [coreflexiveD₂_comp_tensor]
    _ = coreflexiveD₂ (f := f) (g := g) ≫
          (((e' ⊗ₘ e') ≫ (Δ[X] ⊗ₘ 𝟙 X)) ≫ (α_ X X X).hom) := by
          congr 1; rw [coreflexiveD, tensorHom_comp_tensorHom]; simp [e']
    _ = (coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ e')) ≫
          (Δ[X] ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom := by simp only [Category.assoc]
    _ = (e' ≫ Δ[X]) ≫ (Δ[X] ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom := by
          rw [coreflexiveD₂_comp_tensor, coreflexiveD]

/-- The coassociativity law for the equalizer comultiplication. -/
lemma coreflexiveD₂_comul_assoc :
    coreflexiveD₂ (f := f) (g := g) ≫
      (coreflexiveEq (f := f) (g := g) ◁ coreflexiveD₂ (f := f) (g := g)) =
        coreflexiveD₂ (f := f) (g := g) ≫
          (coreflexiveD₂ (f := f) (g := g) ▷ coreflexiveEq (f := f) (g := g)) ≫
            (α_ (coreflexiveEq (f := f) (g := g)) (coreflexiveEq (f := f) (g := g))
              (coreflexiveEq (f := f) (g := g))).hom := by
  set e' : coreflexiveEq (f := f) (g := g) ⟶ X := coreflexiveEqι (f := f) (g := g)
  have hmono : Mono (e' ⊗ₘ (e' ⊗ₘ e')) :=
    mono_coreflexiveEqι_tensor_tensor' (f := f) (g := g)
  apply (cancel_mono (e' ⊗ₘ (e' ⊗ₘ e'))).mp
  have hcoassoc : Δ[X] ≫ (𝟙 X ⊗ₘ Δ[X]) =
      Δ[X] ≫ (Δ[X] ⊗ₘ 𝟙 X) ≫ (α_ X X X).hom := by
    rw [id_tensorHom, tensorHom_id]
    exact ComonObj.comul_assoc X
  rw [coreflexiveD₂_comul_assoc_lhs, coreflexiveD₂_comul_assoc_rhs]
  simp only [Category.assoc]
  exact congrArg (fun t => e' ≫ t) hcoassoc

/-- The counit law for the equalizer comultiplication, on the other side. -/
lemma coreflexiveD₂_comul_counit :
    coreflexiveD₂ (f := f) (g := g) ≫
      (coreflexiveEq (f := f) (g := g) ◁ (coreflexiveEqι (f := f) (g := g) ≫ ε[X])) =
        (ρ_ (coreflexiveEq (f := f) (g := g))).inv := by
  set E : V := coreflexiveEq (f := f) (g := g)
  set e' : E ⟶ X := coreflexiveEqι (f := f) (g := g)
  have hcounit : Δ[X] ≫ (𝟙 X ⊗ₘ ε[X]) ≫ (ρ_ X).hom = 𝟙 X := by
    rw [id_tensorHom, ← Category.assoc, ComonObj.comul_counit]
    simp
  have hε : (E ◁ (e' ≫ ε[X])) ≫ (e' ▷ 𝟙_ V) = (e' ⊗ₘ e') ≫ (𝟙 X ⊗ₘ ε[X]) := by
    rw [← id_tensorHom, ← tensorHom_id e' (𝟙_ V)]
    rw [tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp, tensorHom_comp_tensorHom]
  have hkey : ((coreflexiveD₂ (f := f) (g := g) ≫ (E ◁ (e' ≫ ε[X]))) ≫
      (ρ_ E).hom) ≫ e' = e' := by
    calc ((coreflexiveD₂ (f := f) (g := g) ≫ (E ◁ (e' ≫ ε[X]))) ≫
          (ρ_ E).hom) ≫ e'
        = ((coreflexiveD₂ (f := f) (g := g) ≫ (E ◁ (e' ≫ ε[X]))) ≫
            ((e' ▷ 𝟙_ V) ≫ (ρ_ X).hom)) := by
            rw [rightUnitor_naturality]
            simp only [Category.assoc]
      _ = (coreflexiveD₂ (f := f) (g := g) ≫
            ((E ◁ (e' ≫ ε[X])) ≫ (e' ▷ 𝟙_ V))) ≫ (ρ_ X).hom := by
            simp only [Category.assoc]
      _ = (coreflexiveD₂ (f := f) (g := g) ≫
            ((e' ⊗ₘ e') ≫ (𝟙 X ⊗ₘ ε[X]))) ≫ (ρ_ X).hom := by rw [hε]
      _ = ((coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ e')) ≫
            (𝟙 X ⊗ₘ ε[X])) ≫ (ρ_ X).hom := by simp only [Category.assoc]
      _ = (e' ≫ (Δ[X] ≫ (𝟙 X ⊗ₘ ε[X]) ≫ (ρ_ X).hom)) := by
            rw [coreflexiveD₂_comp_tensor, coreflexiveD]
            simp only [e', Category.assoc]
      _ = e' := by rw [hcounit, Category.comp_id]
  have h1 : (coreflexiveD₂ (f := f) (g := g) ≫ (E ◁ (e' ≫ ε[X]))) ≫
      (ρ_ E).hom = 𝟙 E := by
    apply (cancel_mono e').mp
    rw [Category.id_comp]
    exact hkey
  exact (Iso.comp_hom_eq_id (ρ_ E)).mp h1

/-- The comonoid structure on the equalizer of a coreflexive pair of comonoids. -/
noncomputable instance coreflexiveComonObj : ComonObj (coreflexiveEq (f := f) (g := g)) where
  counit := coreflexiveEqι (f := f) (g := g) ≫ ε[X]
  comul := coreflexiveD₂ (f := f) (g := g)
  counit_comul := coreflexiveD₂_counit_comul (f := f) (g := g)
  comul_counit := coreflexiveD₂_comul_counit (f := f) (g := g)
  comul_assoc := coreflexiveD₂_comul_assoc (f := f) (g := g)

/-- The equalizer map is a morphism of comonoids. -/
instance isComonHom_coreflexiveEqι :
    IsComonHom (coreflexiveEqι (f := f) (g := g)) where
  hom_counit := rfl
  hom_comul := (coreflexiveD₂_comp_tensor (f := f) (g := g)).symm

/-- The equalizer comonoid is cocommutative when the source is. -/
instance isCommComonObj_coreflexiveEq [BraidedCategory V] [IsCommComonObj X] :
    IsCommComonObj (coreflexiveEq (f := f) (g := g)) where
  comul_comm := by
    set E : V := coreflexiveEq (f := f) (g := g)
    set e' : E ⟶ X := coreflexiveEqι (f := f) (g := g)
    have hmono : Mono (e' ⊗ₘ e') := mono_coreflexiveEqι_tensor (f := f) (g := g)
    apply (cancel_mono (e' ⊗ₘ e')).mp
    calc (coreflexiveD₂ (f := f) (g := g) ≫ (β_ E E).hom) ≫ (e' ⊗ₘ e')
        = coreflexiveD₂ (f := f) (g := g) ≫ ((β_ E E).hom ≫ (e' ⊗ₘ e')) :=
            Category.assoc _ _ _
      _ = coreflexiveD₂ (f := f) (g := g) ≫ ((e' ⊗ₘ e') ≫ (β_ X X).hom) := by
            rw [← BraidedCategory.braiding_naturality]
      _ = (coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ e')) ≫ (β_ X X).hom :=
            (Category.assoc _ _ _).symm
      _ = (e' ≫ Δ[X]) ≫ (β_ X X).hom := by rw [coreflexiveD₂_comp_tensor, coreflexiveD]
      _ = e' ≫ (Δ[X] ≫ (β_ X X).hom) := Category.assoc _ _ _
      _ = e' ≫ Δ[X] := by rw [IsCommComonObj.comul_comm]
      _ = coreflexiveD (f := f) (g := g) := by rw [coreflexiveD]
      _ = coreflexiveD₂ (f := f) (g := g) ≫ (e' ⊗ₘ e') := by
            rw [coreflexiveD₂_comp_tensor]

end ComonoidStructure

end UlmerBialgebras
