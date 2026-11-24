module

public import Hopf.Basic.HopfTensorQuotEquiv
public import Foundations.RingTheory.NilpotentFreeCriterion

/-!
# Faithful flatness of Hopf algebras: the case of a nilpotent augmentation ideal

This file completes the "nilpotent" half of Waterhouse's proof of Takeuchi's faithful flatness
theorem (*Introduction to Affine Group Schemes*, §14.2):

> We first treat the extreme case where the augmentation ideal `I` of `A` is nilpotent; in this
> case we will show `B` is actually free over `A`.  Let `N` be the kernel of `F → G`, so
> `k[N] = C = B/IB`.  Then `F × N ≅ F ×_G F` under `(f, n) ↦ (f, nf)`; thus `B ⊗_A B ≅ B ⊗_k C`.
> [...] Choose elements `(xᵢ)` in `B` whose images `[xᵢ]` are a `k`-basis of `C`; we will show the
> `xᵢ` are an `A`-basis of `B`.

The two ingredients are already available:

* `HopfAlgebra.galoisTensorEquiv` (in `Hopf/Basic/HopfTensorQuotEquiv.lean`): the
  isomorphism `B ⊗[A] B ≅ B ⊗[k] C` of left `B`-modules, whence `B ⊗[A] B` is a free `B`-module;
* `Module.Free.free_of_nilpotent` (in `Foundations/RingTheory/NilpotentFreeCriterion.lean`):
  the module-theoretic freeness criterion.

What is added here is the verification of the two hypotheses of the criterion for a lift `(xᵢ)` of
a `k`-basis of `C`:

* `HopfAlgebra.Commutative.span_sup_smul_eq_top`: the `xᵢ` span `B` modulo `A⁺B`;
* `HopfAlgebra.Commutative.ker_tensorMap_le`: if `∑ uⱼ ⊗ xⱼ = 0` in `B ⊗[A] B`, then every `uⱼ` lies
  in `A⁺B` — because `∑ [uⱼ] ⊗ [xⱼ] = 0` in `C ⊗[k] C` and the `[xⱼ]` are a `k`-basis of `C`;

and the resulting theorems

* `HopfAlgebra.Commutative.free_of_nilpotent_augmentation`: `B` is a free `A`-module;
* `HopfAlgebra.Commutative.faithfullyFlat_of_nilpotent_augmentation`: `B` is faithfully flat over
  `A`.

## Main results

* `HopfAlgebra.Commutative.free_of_nilpotent_augmentation`: if `A → B` is injective and the
  augmentation ideal of `A` is nilpotent, then `B` is a free `A`-module.
* `HopfAlgebra.Commutative.faithfullyFlat_of_nilpotent_augmentation`: under the same hypotheses,
  with `B` nontrivial, `B` is faithfully flat over `A`.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Section 14.2
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

section
open Module.Free
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]
  [Algebra A B] [IsScalarTower k A B]

section Basis

variable {J : Type*} (x : J → B) (basisC : Module.Basis J k (QuotAug k A B))
  (hx : ∀ j, mkAug k A B (x j) = basisC j)

include hx

/-- A lift of a `k`-basis of `C = B/A⁺B` spans `B` modulo the augmentation ideal of `A`. -/
lemma span_sup_smul_eq_top :
    Submodule.span A (Set.range x) ⊔ (HopfAlgebra.Commutative.augmentationIdeal k A) •
        (⊤ : Submodule A B)
      = ⊤ := by
  classical
  refine eq_top_iff.mpr fun b _ => ?_
  set r := basisC.repr (mkAug k A B b) with hr
  set v : B := ∑ j ∈ r.support, (algebraMap k B (r j)) * x j with hv
  have hv1 : v ∈ Submodule.span A (Set.range x) := by
    refine Submodule.sum_mem _ fun j _ => ?_
    have hsm : (algebraMap k B (r j)) * x j = (algebraMap k A (r j)) • x j := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k A B]
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmk : mkAug k A B v = mkAug k A B b := by
    rw [hv, map_sum]
    have hterm : ∀ j ∈ r.support,
        mkAug k A B ((algebraMap k B (r j)) * x j) = r j • basisC j := by
      intro j _
      rw [map_mul, hx j, AlgHom.commutes, ← Algebra.smul_def]
    rw [Finset.sum_congr rfl hterm, hr]
    have hrep := basisC.linearCombination_repr (mkAug k A B b)
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrep
    exact hrep
  have hdiff : b - v ∈ (HopfAlgebra.Commutative.augmentationIdeal k A) • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map]
    have h0 : (Ideal.Quotient.mk (augIdealB k A B)) (b - v) = 0 := by
      have hbv : mkAug k A B (b - v) = 0 := by rw [map_sub, hmk, sub_self]
      exact hbv
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  have hb : b = v + (b - v) := by ring
  rw [hb]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hv1) (Submodule.mem_sup_right hdiff)

/-- If `∑ uⱼ ⊗ xⱼ = 0` in `B ⊗[A] B`, then every coefficient `uⱼ` lies in `A⁺B`: indeed the
images satisfy `∑ [uⱼ] ⊗ [xⱼ] = 0` in `C ⊗[k] C`, and the `[xⱼ]` are a `k`-basis of `C`. -/
lemma ker_tensorMap_le :
    LinearMap.ker (Module.Free.tensorMap A x) ≤
      ((HopfAlgebra.Commutative.augmentationIdeal k A).map (algebraMap A B)) •
          (⊤ : Submodule B (J →₀ B)) := by
  classical
  intro u hu
  have hexp : Module.Free.tensorMap A x u = ∑ j ∈ u.support, (u j) ⊗ₜ[A] x j := by
    rw [Module.Free.tensorMap, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hu0 : (∑ j ∈ u.support, (u j) ⊗ₜ[A] x j) = 0 := by
    rw [← hexp]; exact hu
  -- every coefficient dies in `C`
  have hcoeff : ∀ i : J, mkAug k A B (u i) = 0 := by
    intro i
    set φ : (QuotAug k A B ⊗[k] QuotAug k A B) →ₗ[k] QuotAug k A B :=
      (TensorProduct.rid k (QuotAug k A B)) ∘ₗ (LinearMap.lTensor _ (basisC.coord i)) with hφ
    have h0 : φ (quotPairMap k A B (∑ j ∈ u.support, (u j) ⊗ₜ[A] x j)) = 0 := by
      rw [hu0, map_zero, map_zero]
    rw [map_sum, map_sum] at h0
    have hterm : ∀ j ∈ u.support,
        φ (quotPairMap k A B ((u j) ⊗ₜ[A] x j))
          = (if j = i then (1 : k) else 0) • mkAug k A B (u j) := by
      intro j _
      rw [quotPairMap_tmul, hx j, hφ]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases h : j = i <;> simp [h]
    rw [Finset.sum_congr rfl hterm] at h0
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq'] at h0
    by_cases hi : i ∈ u.support
    · simpa [hi] using h0
    · simpa using congrArg (mkAug k A B) (Finsupp.notMem_support_iff.mp hi)
  -- hence `u` lies in `A⁺B · (J →₀ B)`
  have hsingle : ∀ j ∈ u.support,
      Finsupp.single j (u j) ∈
        ((HopfAlgebra.Commutative.augmentationIdeal k A).map (algebraMap A B)) •
            (⊤ : Submodule B (J →₀ B)) := by
    intro j _
    have hmem : u j ∈ (HopfAlgebra.Commutative.augmentationIdeal k A).map (algebraMap A B) := by
      have h0 : (Ideal.Quotient.mk (augIdealB k A B)) (u j) = 0 := hcoeff j
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    have : Finsupp.single j (u j) = (u j) • Finsupp.single j (1 : B) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hmem Submodule.mem_top
  have := Submodule.sum_mem
    (((HopfAlgebra.Commutative.augmentationIdeal k A).map (algebraMap A B)) •
        (⊤ : Submodule B (J →₀ B)))
    hsingle
  have heq : (∑ j ∈ u.support, Finsupp.single j (u j)) = u := Finsupp.sum_single u
  rwa [heq] at this

omit hx in
/-- **Waterhouse §14.2, the nilpotent case** (for a given lift of a basis): if the augmentation
ideal of `A` is nilpotent and `A → B` is injective, then a lift `(xⱼ)` of a `k`-basis of
`C = B/A⁺B` is an `A`-basis of `B`. -/
theorem free_of_nilpotent_augmentation_of_basis
    (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)
    (hinj : Function.Injective (algebraMap A B))
    {n : ℕ} (hI : (HopfAlgebra.Commutative.augmentationIdeal k A) ^ n = ⊥)
    (hx : ∀ j, mkAug k A B (x j) = basisC j) :
    Module.Free A B :=
  letI := projective_tensorProduct f halg
  Module.Free.free_of_nilpotent x (HopfAlgebra.Commutative.augmentationIdeal k A) hI hinj
    (span_sup_smul_eq_top x basisC hx) (ker_tensorMap_le x basisC hx)

end Basis

/-- **Waterhouse §14.2, the nilpotent case.**  Let `A ⊆ B` be commutative Hopf algebras over a
field `k`, with `A → B` injective.  If the augmentation ideal `A⁺` of `A` is nilpotent, then `B`
is a *free* `A`-module. -/
theorem free_of_nilpotent_augmentation (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)
    (hinj : Function.Injective (algebraMap A B))
    {n : ℕ} (hI : (HopfAlgebra.Commutative.augmentationIdeal k A) ^ n = ⊥) :
    Module.Free A B := by
  classical
  set basisC := Module.Basis.ofVectorSpace k (QuotAug k A B) with hbasis
  choose x hx using fun j => mkAug_surjective (basisC j)
  exact free_of_nilpotent_augmentation_of_basis x basisC f halg hinj hI hx

/-- **Waterhouse §14.2, the nilpotent case.**  Under the same hypotheses, `B` is faithfully flat
over `A`.  This is Takeuchi's theorem in the case of a nilpotent augmentation ideal. -/
theorem faithfullyFlat_of_nilpotent_augmentation [Nontrivial B]
    (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)
    (hinj : Function.Injective (algebraMap A B))
    {n : ℕ} (hI : (HopfAlgebra.Commutative.augmentationIdeal k A) ^ n = ⊥) :
    Module.FaithfullyFlat A B :=
  letI := free_of_nilpotent_augmentation f halg hinj hI
  inferInstance

end HopfAlgebra.Commutative
end
