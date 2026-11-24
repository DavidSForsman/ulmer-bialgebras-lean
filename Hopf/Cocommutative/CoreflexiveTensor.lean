module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Coreflexive equalizers and the tensor product

Let `C` be a monoidal category in which tensoring on either side preserves the equalizers of
coreflexive pairs.  This file proves the dual of
`Foundations/CategoryTheory/Monoidal/ReflexiveTensor.lean`:
the tensor square of a coreflexive equalizer is again an equalizer.

If `u, v : M ⇉ N` is a coreflexive pair with equalizer `e : E ⟶ M`, then `e ⊗ₘ e` is an
equalizer of `u ⊗ₘ u` and `v ⊗ₘ v`.

This is the key computation behind the construction of coreflexive equalizers of *comonoid*
objects — for `C = ModuleCat k` with `k` a field, the construction of finite limits in the
category of cocommutative coalgebras.

## Main results

* `UlmerBialgebras.PreservesCoreflexiveEq` — the property of preserving equalizers of coreflexive
  pairs;
* `UlmerBialgebras.CoreflexiveTensor.isLimitWhiskerRight`,
  `UlmerBialgebras.CoreflexiveTensor.isLimitWhiskerLeft` — whiskering a coreflexive equalizer with a
  fixed object again gives an equalizer;
* `UlmerBialgebras.CoreflexiveTensor.isLimitTensorHom` — `e ⊗ₘ e` is an equalizer of `u ⊗ₘ u`,
  `v ⊗ₘ v`;
* `UlmerBialgebras.CoreflexiveTensor.mono_tensorHom`,
  `UlmerBialgebras.CoreflexiveTensor.mono_tensorHom_tensorHom` — the resulting monomorphisms, used
  to check the comonoid axioms on the equalizer.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.16 (dual form)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace UlmerBialgebras

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor **preserves coreflexive equalizers** if it preserves the equalizer of every
coreflexive pair. -/
class PreservesCoreflexiveEq (F : A ⥤ B) : Prop where
  preserves : ∀ ⦃X Y : A⦄ (u v : X ⟶ Y), IsCoreflexivePair u v → PreservesLimit (parallelPair u v) F

/-- A functor preserving all equalizers preserves coreflexive equalizers. -/
lemma preservesCoreflexiveEq_of_preservesLimitsOfShape (F : A ⥤ B)
    [PreservesLimitsOfShape WalkingParallelPair F] : PreservesCoreflexiveEq F :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Functors preserve coreflexive pairs. -/
lemma isCoreflexivePair_map (F : A ⥤ B) {X Y : A} {u v : X ⟶ Y} (h : IsCoreflexivePair u v) :
    IsCoreflexivePair (F.map u) (F.map v) := by
  obtain ⟨s, hu, hv⟩ := h.common_retraction'
  exact .mk' (F.map s) (by rw [← F.map_comp, hu, F.map_id]) (by rw [← F.map_comp, hv, F.map_id])

namespace CoreflexiveTensor

variable {C : Type u} [Category.{v} C]

/-- An equalizer is a monomorphism. -/
lemma mono_of_isLimitFork {X Y Z : C} {f g : Y ⟶ Z} {h : X ⟶ Y} {w : h ≫ f = h ≫ g}
    (hc : IsLimit (Fork.ofι h w)) : Mono h :=
  ⟨fun _ _ e => Fork.IsLimit.hom_ext hc e⟩

variable [MonoidalCategory C]

section

variable {M N E : C} {u v : M ⟶ N} (hr : IsCoreflexivePair u v) {e : E ⟶ M}

include hr in
/-- The tensor square of a coreflexive pair, `u ⊗ₘ u` and `v ⊗ₘ v`, is again coreflexive. -/
lemma isCoreflexivePair_tensorHom : IsCoreflexivePair (u ⊗ₘ u) (v ⊗ₘ v) := by
  obtain ⟨s, hu, hv⟩ := hr.common_retraction'
  exact .mk' (s ⊗ₘ s) (by rw [tensorHom_comp_tensorHom, hu, tensorHom_id, id_whiskerRight])
    (by rw [tensorHom_comp_tensorHom, hv, tensorHom_id, id_whiskerRight])

/-- If `e ≫ u = e ≫ v`, then `(e ⊗ e) ≫ (u ⊗ u) = (e ⊗ e) ≫ (v ⊗ v)`. -/
lemma tensorHom_comp_tensorHom_eq (hw : e ≫ u = e ≫ v) :
    (e ⊗ₘ e) ≫ (u ⊗ₘ u) = (e ⊗ₘ e) ≫ (v ⊗ₘ v) := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hw]

end

section

variable {M N E : C} {u v : M ⟶ N} (hr : IsCoreflexivePair u v) {e : E ⟶ M}
  {w : e ≫ u = e ≫ v} (he : IsLimit (Fork.ofι e w))
  [∀ Z : C, PreservesCoreflexiveEq (tensorRight Z)]

include hr he

/-- Whiskering a coreflexive equalizer on the right by a fixed object gives an equalizer. -/
noncomputable def isLimitWhiskerRight (Z : C) :
    IsLimit (Fork.ofι (e ▷ Z) (show (e ▷ Z) ≫ (u ▷ Z) = (e ▷ Z) ≫ (v ▷ Z) by
      rw [← comp_whiskerRight, ← comp_whiskerRight, w])) := by
  haveI : PreservesLimit (parallelPair u v) (tensorRight Z) :=
    PreservesCoreflexiveEq.preserves u v hr
  exact isLimitForkMapOfIsLimit (tensorRight Z) w he

/-- `e ▷ Z` is a monomorphism, being an equalizer. -/
lemma mono_whiskerRight (Z : C) : Mono (e ▷ Z) :=
  mono_of_isLimitFork (isLimitWhiskerRight hr he Z)

variable [∀ Z : C, PreservesCoreflexiveEq (tensorLeft Z)]

/-- Whiskering a coreflexive equalizer on the left by a fixed object gives an equalizer. -/
noncomputable def isLimitWhiskerLeft (Z : C) :
    IsLimit (Fork.ofι (Z ◁ e) (show (Z ◁ e) ≫ (Z ◁ u) = (Z ◁ e) ≫ (Z ◁ v) by
      rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w])) := by
  haveI : PreservesLimit (parallelPair u v) (tensorLeft Z) :=
    PreservesCoreflexiveEq.preserves u v hr
  exact isLimitForkMapOfIsLimit (tensorLeft Z) w he

omit [∀ Z : C, PreservesCoreflexiveEq (tensorRight Z)] in
/-- `Z ◁ e` is a monomorphism, being an equalizer. -/
lemma mono_whiskerLeft (Z : C) : Mono (Z ◁ e) :=
  mono_of_isLimitFork (isLimitWhiskerLeft hr he Z)

/-- The tensor square `e ⊗ e` of a coreflexive equalizer is a monomorphism. -/
lemma mono_tensorHom : Mono (e ⊗ₘ e) := by
  rw [MonoidalCategory.tensorHom_def]
  have := mono_whiskerRight hr he E
  have := mono_whiskerLeft hr he M
  exact mono_comp _ _

/-- The universal property of `e ⊗ₘ e` as an equalizer of `u ⊗ₘ u` and `v ⊗ₘ v`. -/
lemma existsUnique_lift_tensorHom {Z : C} (t : Z ⟶ M ⊗ M)
    (ht : t ≫ (u ⊗ₘ u) = t ≫ (v ⊗ₘ v)) : ∃! r : Z ⟶ E ⊗ E, r ≫ (e ⊗ₘ e) = t := by
  obtain ⟨s, hsu, hsv⟩ := hr.common_retraction'
  have h₁ := isLimitWhiskerLeft hr he M
  have h₂ := isLimitWhiskerRight (E := E) hr he E
  have hmonoN : Mono (N ◁ e) := mono_whiskerLeft hr he N
  have hmono : Mono (e ⊗ₘ e) := mono_tensorHom hr he
  -- the two ways of collapsing one leg of the tensor square
  have eu₁ : (u ⊗ₘ u) ≫ (s ▷ N) = M ◁ u := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, hsu, Category.comp_id, id_tensorHom]
  have ev₁ : (v ⊗ₘ v) ≫ (s ▷ N) = M ◁ v := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, hsv, Category.comp_id, id_tensorHom]
  have eu₂ : (u ⊗ₘ u) ≫ (N ◁ s) = u ▷ M := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, hsu, Category.comp_id, tensorHom_id]
  have ev₂ : (v ⊗ₘ v) ≫ (N ◁ s) = v ▷ M := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, hsv, Category.comp_id, tensorHom_id]
  have heq₁ : t ≫ (M ◁ u) = t ≫ (M ◁ v) := by
    rw [← eu₁, ← ev₁, ← Category.assoc, ← Category.assoc, ht]
  obtain ⟨t₁, ht₁⟩ := Fork.IsLimit.lift' h₁ t heq₁
  simp only [Fork.ι_ofι] at ht₁
  have heq₂ : t₁ ≫ (u ▷ E) = t₁ ≫ (v ▷ E) := by
    rw [← cancel_mono (N ◁ e)]
    rw [Category.assoc, Category.assoc, ← whisker_exchange, ← whisker_exchange,
      ← Category.assoc, ← Category.assoc, ht₁, ← eu₂, ← ev₂, ← Category.assoc,
      ← Category.assoc, ht]
  obtain ⟨t₂, ht₂⟩ := Fork.IsLimit.lift' h₂ t₁ heq₂
  simp only [Fork.ι_ofι] at ht₂
  refine ⟨t₂, ?_, fun r hr' => ?_⟩
  · change t₂ ≫ (e ⊗ₘ e) = t
    rw [MonoidalCategory.tensorHom_def, ← Category.assoc, ht₂, ht₁]
  · rw [← cancel_mono (e ⊗ₘ e), hr', MonoidalCategory.tensorHom_def, ← Category.assoc, ht₂, ht₁]

/-- **Coreflexive equalizers are preserved by the tensor square.**  If `e` is the equalizer of a
coreflexive pair `u, v`, then `e ⊗ₘ e` is the equalizer of `u ⊗ₘ u` and `v ⊗ₘ v`. -/
noncomputable def isLimitTensorHom :
    IsLimit (Fork.ofι (e ⊗ₘ e) (tensorHom_comp_tensorHom_eq w)) :=
  Fork.IsLimit.mk _
    (fun t => (existsUnique_lift_tensorHom hr he t.ι (Fork.condition t)).choose)
    (fun t => (existsUnique_lift_tensorHom hr he t.ι (Fork.condition t)).choose_spec.1)
    (fun t m hm => (existsUnique_lift_tensorHom hr he t.ι (Fork.condition t)).choose_spec.2 m hm)

/-- The tensor cube `e ⊗ e ⊗ e` of a coreflexive equalizer is a monomorphism. -/
lemma mono_tensorHom_tensorHom : Mono (e ⊗ₘ e ⊗ₘ e) := by
  rw [MonoidalCategory.tensorHom_def]
  have := mono_whiskerRight hr he (E ⊗ E)
  have := mono_whiskerLeft (isCoreflexivePair_tensorHom hr) (isLimitTensorHom hr he) M
  exact mono_comp _ _

end

end CoreflexiveTensor

end UlmerBialgebras
