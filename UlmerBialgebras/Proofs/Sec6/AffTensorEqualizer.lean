module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Foundations.RingTheory.VonNeumannRegularFlat

/-!
# Tensoring preserves equalizers of commutative algebras over an absolutely flat base

The base is a commutative ring over which every module is flat (`AllFlat`): fields and von
Neumann regular rings. The proof only uses flatness of `Z`.

This is the left exactness of the tensor product over a von Neumann regular ring used in
Lemma 6.10 and Corollary 6.11 of the paper (case `A = Mod_R^op`).

## Main results

* `AffineGroupSchemes.AllFlat`: the class of commutative rings over which every module is flat.
* `AffineGroupSchemes.AllFlat.of_vnr`: a von Neumann regular commutative ring satisfies `AllFlat`.
* `AffineGroupSchemes.TensorEqualizer.tensorEqualizerEquiv`: the algebra isomorphism
  `Z ⊗ eq(f, g) ≃ₐ[k] eq(Z ⊗ f, Z ⊗ g)`.
* `AffineGroupSchemes.TensorEqualizer.preservesLimitsOfShape_walkingParallelPair_tensorLeft`:
  `Z ⊗ -` preserves equalizers in `CommAlgCat k`.
* `AffineGroupSchemes.TensorEqualizer.preservesColimitsOfShape_walkingParallelPair_op`: `W ⊗ -`
  preserves coequalizers in `(CommAlgCat k)ᵒᵖ`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.10 and Corollary 6.11
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative
  Algebra*][atiyah_introduction_1969], Chapter 2, Exercise 27
-/

@[expose] public section

universe u v

open CategoryTheory Limits TensorProduct MonoidalCategory Opposite

namespace AffineGroupSchemes

/-- Every module over the base ring is flat. -/
class AllFlat (k : Type u) [CommRing k] : Prop where
  flat : ∀ (M : Type u) [AddCommGroup M] [Module k M], Module.Flat k M

/-- A von Neumann regular commutative ring is absolutely flat: every module over it is flat. -/
theorem AllFlat.of_vnr (k : Type u) [CommRing k] (hk : IsVonNeumannRegular k) : AllFlat k :=
  ⟨fun M _ _ => IsVonNeumannRegular.flat hk M⟩

namespace TensorEqualizer

/-! ## A general remark on reflexive coequalizers -/

/-! ## Equalizers of commutative algebras -/

section Algebra

variable {k Z A B : Type u} [CommRing k] [CommRing Z] [CommRing A] [CommRing B]
  [Algebra k Z] [Algebra k A] [Algebra k B]

variable (Z) (f g : A →ₐ[k] B)

/-- The difference of two algebra maps, as a linear map. -/
noncomputable abbrev dif : A →ₗ[k] B := f.toLinearMap - g.toLinearMap

/-- The sequence `eq(f, g) ↪ A --(f - g)--> B` of `k`-modules is exact. -/
lemma exact_val : Function.Exact ⇑((AlgHom.equalizer f g).val.toLinearMap) ⇑(dif f g) := by
  intro a
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]
  exact ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨e, rfl⟩; exact e.2⟩

/-- The algebra map `Z ⊗ φ` agrees pointwise with the linear map `lTensor Z φ`. -/
lemma map_apply_eq_lTensor (φ : A →ₐ[k] B) (t : Z ⊗[k] A) :
    Algebra.TensorProduct.map (AlgHom.id k Z) φ t = LinearMap.lTensor Z φ.toLinearMap t := by
  have h : (Algebra.TensorProduct.map (AlgHom.id k Z) φ).toLinearMap
      = LinearMap.lTensor Z φ.toLinearMap := by ext x; simp
  exact congr($h t)

/-- The algebra map `Z ⊗ eq(f, g) → Z ⊗ A` agrees pointwise with `lTensor` of the inclusion. -/
lemma mapval_apply_eq_lTensor (s : Z ⊗[k] (AlgHom.equalizer f g)) :
    Algebra.TensorProduct.map (AlgHom.id k Z) (AlgHom.equalizer f g).val s
      = LinearMap.lTensor Z ((AlgHom.equalizer f g).val.toLinearMap) s := by
  have h : (Algebra.TensorProduct.map (AlgHom.id k Z) (AlgHom.equalizer f g).val).toLinearMap
      = LinearMap.lTensor Z ((AlgHom.equalizer f g).val.toLinearMap) := by ext x; simp
  exact congr($h s)

variable [AllFlat k]

/-- The sequence `Z ⊗ eq(f, g) → Z ⊗ A --Z ⊗ (f - g)--> Z ⊗ B` is exact, by flatness of `Z`. -/
lemma exact_tensor :
    Function.Exact ⇑(LinearMap.lTensor Z ((AlgHom.equalizer f g).val.toLinearMap))
      ⇑(LinearMap.lTensor Z (dif f g)) :=
  haveI := AffineGroupSchemes.AllFlat.flat (k := k) Z
  Module.Flat.lTensor_exact Z (exact_val f g)

/-- Tensoring the inclusion of the equalizer subalgebra stays injective. -/
lemma injective_map_val :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k Z) (AlgHom.equalizer f g).val) := by
  have := AffineGroupSchemes.AllFlat.flat (k := k) Z
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap
    (M := Z) ((AlgHom.equalizer f g).val.toLinearMap) Subtype.val_injective
  intro x y hxy
  exact hinj (by rw [← mapval_apply_eq_lTensor, ← mapval_apply_eq_lTensor]; exact hxy)

/-- The range of the tensored inclusion is the equalizer of the tensored maps. -/
lemma range_map_val :
    AlgHom.range (Algebra.TensorProduct.map (AlgHom.id k Z) (AlgHom.equalizer f g).val)
      = AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id k Z) f)
          (Algebra.TensorProduct.map (AlgHom.id k Z) g) := by
  ext t
  simp only [AlgHom.mem_range, AlgHom.mem_equalizer]
  have hE := exact_tensor Z f g t
  rw [LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero] at hE
  rw [map_apply_eq_lTensor, map_apply_eq_lTensor, hE]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, by rw [← mapval_apply_eq_lTensor]; exact hs⟩,
    fun ⟨s, hs⟩ => ⟨s, by rw [mapval_apply_eq_lTensor]; exact hs⟩⟩

/-- The comparison algebra isomorphism `Z ⊗ eq(f, g) ≅ eq(Z ⊗ f, Z ⊗ g)`. -/
noncomputable def tensorEqualizerEquiv :
    (Z ⊗[k] (AlgHom.equalizer f g)) ≃ₐ[k]
      (AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id k Z) f)
        (Algebra.TensorProduct.map (AlgHom.id k Z) g)) := by
  refine AlgEquiv.ofBijective
    ((Algebra.TensorProduct.map (AlgHom.id k Z) (AlgHom.equalizer f g).val).codRestrict _
      (fun x => ?_)) ⟨?_, ?_⟩
  · rw [← range_map_val Z f g]; exact ⟨x, rfl⟩
  · intro x y hxy
    exact injective_map_val Z f g (congr(($(hxy)).val))
  · rintro ⟨t, ht⟩
    rw [← range_map_val Z f g] at ht
    obtain ⟨s, hs⟩ := ht
    exact ⟨s, Subtype.ext hs⟩

end Algebra

/-! ## Equalizers in `CommAlgCat` -/

section Cat

variable {k : Type u} [CommRing k] [AllFlat k]

/-- The equalizer fork of two morphisms of commutative algebras. -/
noncomputable def equalizerFork {A B : CommAlgCat.{u} k} (f g : A ⟶ B) : Fork f g :=
  Fork.ofι (P := CommAlgCat.of k (AlgHom.equalizer f.hom g.hom))
    (CommAlgCat.ofHom (AlgHom.equalizer f.hom g.hom).val) (by ext x; exact x.2)

/-- The equalizer subalgebra really is the equalizer in `CommAlgCat k`. -/
noncomputable def isLimitEqualizerFork {A B : CommAlgCat.{u} k} (f g : A ⟶ B) :
    IsLimit (equalizerFork f g) := by
  refine Fork.IsLimit.mk _ (fun s => CommAlgCat.ofHom
    ((s.ι.hom).codRestrict (AlgHom.equalizer f.hom g.hom) (fun x => ?_))) ?_ ?_
  · exact congr(($(s.condition)).hom x)
  · intro s; ext x; rfl
  · intro s m hm; ext x
    exact Subtype.ext (congr(($(hm)).hom x))

variable (Z : CommAlgCat.{u} k)

/-- Tensoring with `Z` sends the equalizer fork to the equalizer fork. -/
noncomputable def mapEqualizerForkIso {A B : CommAlgCat.{u} k} (f g : A ⟶ B) :
    Fork.ofι ((tensorLeft Z).map (equalizerFork f g).ι)
        (by simp only [← Functor.map_comp]; rw [Fork.condition]) ≅
      equalizerFork ((tensorLeft Z).map f) ((tensorLeft Z).map g) :=
  Fork.ext (CommAlgCat.isoMk (tensorEqualizerEquiv Z f.hom g.hom)) rfl

/-- **Tensoring preserves equalizers of commutative algebras.** -/
noncomputable instance preservesLimit_parallelPair_tensorLeft
    {A B : CommAlgCat.{u} k} (f g : A ⟶ B) :
    PreservesLimit (parallelPair f g) (tensorLeft Z) := by
  refine preservesLimit_of_preserves_limit_cone (isLimitEqualizerFork f g) ?_
  refine (isLimitMapConeForkEquiv (tensorLeft Z) (Fork.condition (equalizerFork f g))).symm ?_
  exact IsLimit.ofIsoLimit (isLimitEqualizerFork ((tensorLeft Z).map f) ((tensorLeft Z).map g))
    (mapEqualizerForkIso Z f g).symm

/-- `Z ⊗ -` preserves all equalizers in `CommAlgCat k` (every diagram of shape
    `WalkingParallelPair` is isomorphic to a `parallelPair`). -/
instance preservesLimitsOfShape_walkingParallelPair_tensorLeft :
    PreservesLimitsOfShape WalkingParallelPair (tensorLeft Z) where
  preservesLimit {K} := by
    have : PreservesLimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) (tensorLeft Z) := inferInstance
    exact preservesLimit_of_iso_diagram (tensorLeft Z) (diagramIsoParallelPair K).symm

end Cat

/-! ## The instance for affine schemes -/

section Op

variable {k : Type u} [CommRing k] [AllFlat k]

/-- `Z ⊗ -` preserves limits of shape `WalkingParallelPairᵒᵖ` in `CommAlgCat k`, transported along
    `WalkingParallelPairᵒᵖ ≌ WalkingParallelPair`. -/
instance preservesLimitsOfShape_walkingParallelPairOp (Z : CommAlgCat.{u} k) :
    PreservesLimitsOfShape WalkingParallelPairᵒᵖ (tensorLeft Z) :=
  preservesLimitsOfShape_of_equiv walkingParallelPairOpEquiv _

/-- In affine schemes `(CommAlgCat k)ᵒᵖ`, `W ⊗ -` preserves coequalizers (dual of the preservation
    of equalizers by `W.unop ⊗ -`). -/
instance preservesColimitsOfShape_walkingParallelPair_op (W : (CommAlgCat.{u} k)ᵒᵖ) :
    PreservesColimitsOfShape WalkingParallelPair (tensorLeft W) :=
  preservesColimitsOfShape_op WalkingParallelPair (tensorLeft W.unop)

end Op

end TensorEqualizer
end AffineGroupSchemes
