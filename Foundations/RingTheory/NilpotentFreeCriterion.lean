module

public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Foundations.RingTheory.NilpotentNakayama

/-!
# A freeness criterion over a base with nilpotent ideal

This file formalizes the module-theoretic core of the "nilpotent" half of Waterhouse's proof of
Takeuchi's faithful flatness theorem (*Introduction to Affine Group Schemes*, §14.2):

> We first treat the extreme case where the augmentation ideal `I` of `A` is nilpotent; in this
> case we will show `B` is actually free over `A`.  Choose elements `(xᵢ)` in `B` whose images are
> a `k`-basis of `C = B/IB`; we will show the `xᵢ` are an `A`-basis of `B`. [...]

Given a commutative ring `A` with a nilpotent ideal `I`, a commutative `A`-algebra `B` with `A → B`
injective, and a family `x : J → B` such that

* `x` spans `B` modulo `I` (`Submodule.span A (Set.range x) ⊔ I • ⊤ = ⊤`), and
* the `B`-linear map `ψ : (J →₀ B) → B ⊗[A] B`, `eⱼ ↦ 1 ⊗ xⱼ`, has kernel inside `I·(J →₀ B)`,
* `B ⊗[A] B` is projective (e.g. free) as a `B`-module,

the family `x` is an `A`-basis of `B`; in particular `B` is a free, hence faithfully flat,
`A`-module.

The two "Hopf" inputs of Waterhouse's argument enter through the last two hypotheses: for a Hopf
algebra `B` with Hopf subalgebra `A` whose augmentation ideal is nilpotent, `B ⊗[A] B` is
isomorphic as a left `B`-module to `B ⊗[k] (B/A⁺B)`, which is free, and the reduction of `ψ`
modulo `I` is an isomorphism.

## Main results

* `Module.Free.bijective_linearCombination_of_nilpotent`: under these hypotheses the map
  `(J →₀ A) → B` induced by `x` is bijective;
* `Module.Free.basisOfNilpotent`: the family `x` as an `A`-basis of `B`;
* `Module.Free.free_of_nilpotent`: `B` is a free `A`-module.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Section 14.2
-/

@[expose] public section

section
namespace Module.Free

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {J : Type*}

/-- The `B`-linear map `ψ : (J →₀ B) → B ⊗[A] B` sending the `j`-th basis vector to `1 ⊗ xⱼ`. -/
noncomputable def tensorMap (A : Type*) [CommRing A] [Algebra A B] (x : J → B) :
    (J →₀ B) →ₗ[B] B ⊗[A] B :=
  Finsupp.linearCombination B (fun j => (1 : B) ⊗ₜ[A] x j)

/-- The map `tensorMap A x` sends `Finsupp.single j b` to `b ⊗ₜ[A] x j`. -/
@[simp] lemma tensorMap_single (x : J → B) (j : J) (b : B) :
    tensorMap A x (Finsupp.single j b) = b ⊗ₜ[A] x j := by
  simp [tensorMap, TensorProduct.smul_tmul']

variable (x : J → B)

/-- With `x` spanning `B` over `A`, the map `ψ` is surjective. -/
lemma tensorMap_surjective (hx : Submodule.span A (Set.range x) = ⊤) :
    Function.Surjective (tensorMap A x) := by
  have hφ : Function.Surjective (Finsupp.linearCombination A x) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hx]
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b b' =>
    obtain ⟨a, ha⟩ := hφ b'
    refine ⟨Finsupp.mapRange (fun r : A => r • b) (by simp) a, ?_⟩
    rw [tensorMap, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), ← ha,
      Finsupp.linearCombination_apply]
    rw [Finsupp.sum, Finsupp.sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
  | add z w hz hw =>
    obtain ⟨u, hu⟩ := hz
    obtain ⟨v, hv⟩ := hw
    exact ⟨u + v, by rw [map_add, hu, hv]⟩

/-- **The freeness criterion.** Let `I` be an ideal of `A` with `I ^ n = ⊥`, let `A → B` be
injective, let `x` span `B` modulo `I` (`span A (range x) ⊔ I • ⊤ = ⊤`), let `B ⊗[A] B` be a
projective `B`-module, and let the kernel of `tensorMap A x : (J →₀ B) → B ⊗[A] B` lie in
`I • (J →₀ B)`. Then the family `x` is an `A`-basis of `B`: the map `(J →₀ A) → B` induced by `x`
is bijective. -/
theorem bijective_linearCombination_of_nilpotent
    (I : Ideal A) {n : ℕ} (hIn : I ^ n = ⊥)
    (hinj : Function.Injective (algebraMap A B))
    (hspan : Submodule.span A (Set.range x) ⊔ I • (⊤ : Submodule A B) = ⊤)
    [Module.Projective B (B ⊗[A] B)]
    (hker : LinearMap.ker (tensorMap A x) ≤
      (I.map (algebraMap A B)) • (⊤ : Submodule B (J →₀ B))) :
    Function.Bijective (Finsupp.linearCombination A x) := by
  classical
  -- `x` spans `B`, by Nakayama for the nilpotent ideal `I`
  have hspanTop : Submodule.span A (Set.range x) = ⊤ := Submodule.eq_top_of_sup_smul_top hIn _ hspan
  have hφ : Function.Surjective (Finsupp.linearCombination A x) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspanTop]
  refine ⟨?_, hφ⟩
  -- `ψ` is surjective, hence split by projectivity of `B ⊗[A] B`
  have hψsurj : Function.Surjective (tensorMap A x) := tensorMap_surjective x hspanTop
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (tensorMap A x)
    (LinearMap.id : (B ⊗[A] B) →ₗ[B] (B ⊗[A] B)) hψsurj
  have hσ' : ∀ m, tensorMap A x (σ (tensorMap A x m)) = tensorMap A x m := fun m =>
    congr($hσ (tensorMap A x m))
  -- the kernel of `ψ` vanishes
  have hIBn : (I.map (algebraMap A B)) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hIn, Ideal.map_bot]
  have hkerbot : LinearMap.ker (tensorMap A x) = ⊥ :=
    Submodule.ker_eq_bot_of_weak_section hIBn _ σ hσ' hker
  -- the commutative square relating `φ` and `ψ`
  set i : (J →₀ A) →ₗ[A] (J →₀ B) := Finsupp.mapRange.linearMap (Algebra.linearMap A B) with hi
  have hisq : ((tensorMap A x).restrictScalars A) ∘ₗ i =
      (TensorProduct.mk A B B 1) ∘ₗ (Finsupp.linearCombination A x) := by
    refine Finsupp.lhom_ext' fun j => ?_
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, hi,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply,
      LinearMap.coe_restrictScalars, tensorMap_single, Finsupp.linearCombination_single,
      TensorProduct.mk_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hiinj : Function.Injective i := by
    refine Finsupp.mapRange_injective (algebraMap A B) (map_zero _) hinj
  intro l l' hll'
  have h1 : (tensorMap A x) (i l) = (tensorMap A x) (i l') := by
    have e1 := congr($hisq l)
    have e2 := congr($hisq l')
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars] at e1 e2
    rw [e1, e2, hll']
  have : i l = i l' := by
    have : i l - i l' ∈ LinearMap.ker (tensorMap A x) := by
      simp [LinearMap.mem_ker, map_sub, h1]
    rw [hkerbot] at this
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)
  exact hiinj this

/-- Under the hypotheses of `bijective_linearCombination_of_nilpotent`, the family `x` really is
an `A`-basis of `B`. -/
noncomputable def basisOfNilpotent
    (I : Ideal A) {n : ℕ} (hIn : I ^ n = ⊥)
    (hinj : Function.Injective (algebraMap A B))
    (hspan : Submodule.span A (Set.range x) ⊔ I • (⊤ : Submodule A B) = ⊤)
    [Module.Projective B (B ⊗[A] B)]
    (hker : LinearMap.ker (tensorMap A x) ≤
      (I.map (algebraMap A B)) • (⊤ : Submodule B (J →₀ B))) :
    Module.Basis J A B :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination A x)
    (bijective_linearCombination_of_nilpotent x I hIn hinj hspan hker)).symm

/-- Under the hypotheses of `bijective_linearCombination_of_nilpotent`, `B` is a free
`A`-module. -/
theorem free_of_nilpotent
    (I : Ideal A) {n : ℕ} (hIn : I ^ n = ⊥)
    (hinj : Function.Injective (algebraMap A B))
    (hspan : Submodule.span A (Set.range x) ⊔ I • (⊤ : Submodule A B) = ⊤)
    [Module.Projective B (B ⊗[A] B)]
    (hker : LinearMap.ker (tensorMap A x) ≤
      (I.map (algebraMap A B)) • (⊤ : Submodule B (J →₀ B))) :
    Module.Free A B :=
  Module.Free.of_basis (basisOfNilpotent x I hIn hinj hspan hker)

end Module.Free
end
