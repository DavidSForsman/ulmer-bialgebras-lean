module

public import Hopf.Basic.SubHopfAlgebra
public import Hopf.Basic.AntipodeBialgHom
public import Hopf.Commutative.FaithfulFlatness

/-!
# Takeuchi's Theorem 3.1, in the form stated in the paper

Takeuchi's **Theorem 3.1** (commutative case) reads:

> Let `H` be a commutative Hopf algebra over a field `k` and let `K` be a sub-Hopf algebra of `H`.
> Then `H` is a faithfully flat `K`-module.

In this project the theorem is carried as the explicit hypothesis
`HopfAlgebra.InjectiveIsFaithfullyFlat`, phrased for an injective morphism of commutative Hopf
algebras `f : A →ₐc[k] B` (see `Hopf/Commutative/FaithfulFlatness.lean`, where several cases of it
are *proved*: `A = k`, nilpotent augmentation ideal, Artinian local rings, von Neumann regular /
étale Hopf algebras and group algebras).

This file shows that the two formulations are **equivalent**
(`HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_iff_faithfullyFlatOverSubHopf`): the image of a
morphism of Hopf algebras is a sub-Hopf algebra, and conversely a sub-Hopf algebra is the image of
the (injective) inclusion morphism, which is a morphism of Hopf algebras by
`Hopf/Basic/SubHopfAlgebra.lean`.

## Main results

* `HopfAlgebra.Commutative.FaithfullyFlatOverSubHopf`: the proposition that a commutative Hopf
  algebra over a field is faithfully flat over each of its sub-Hopf algebras.
* `HopfAlgebra.Commutative.isSubHopfAlgebra_range`: the range of a morphism of Hopf algebras is a
  sub-Hopf algebra.
* `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_iff_faithfullyFlatOverSubHopf`:
  `InjectiveIsFaithfullyFlat ↔ FaithfullyFlatOverSubHopf`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapter 14
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra
namespace HopfAlgebra.Commutative

universe u

/-- **Takeuchi's Theorem 3.1** [Takeuchi1972] in the formulation of the paper: a commutative Hopf
algebra over a field is faithfully flat over any of its sub-Hopf algebras. -/
def FaithfullyFlatOverSubHopf : Prop :=
  ∀ (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H] (K : Subalgebra k H),
    IsSubHopfAlgebra k K → Module.FaithfullyFlat (↥K) H

section Range

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]
  (f : A →ₐc[k] B)

/-- The image of a morphism of Hopf algebras is a sub-Hopf algebra. -/
instance isSubHopfAlgebra_range : IsSubHopfAlgebra k ((f : A →ₐ[k] B).range) where
  comul_mem := by
    rintro _ ⟨a, rfl⟩
    -- `f` with its codomain restricted to the range, as a submodule
    let r : A →ₗ[k] ((f : A →ₐ[k] B).range).toSubmodule :=
      LinearMap.codRestrict _ (f : A →ₗ[k] B) (fun a => ⟨a, rfl⟩)
    refine ⟨TensorProduct.map r r (comul (R := k) a), ?_⟩
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    exact CoalgHomClass.map_comp_comul_apply f a
  antipode_mem := by
    rintro _ ⟨a, rfl⟩
    exact ⟨antipode k a, by simp⟩

end Range

/-- The two formulations of Takeuchi's faithful flatness theorem agree. -/
theorem injectiveIsFaithfullyFlat_iff_faithfullyFlatOverSubHopf :
    HopfAlgebra.InjectiveIsFaithfullyFlat.{u} ↔ FaithfullyFlatOverSubHopf.{u} := by
  constructor
  · intro hInjFlat k H _ _ _ K hK
    let := hK
    have h := hInjFlat k (↥K) H (subInclusion (K := K)) subInclusion_injective
    have he : algebraOfBialgHom (subInclusion (K := K)) = (inferInstance : Algebra (↥K) H) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rwa [he] at h
  · intro hSub k A B _ _ _ _ _ f hf
    let := algebraOfBialgHom f
    set K : Subalgebra k B := (f : A →ₐ[k] B).range with hKdef
    have hFF : Module.FaithfullyFlat (↥K) B := hSub k B K (isSubHopfAlgebra_range f)
    -- `A ≅ K` as rings, and `A → B` factors as `A ≅ K ↪ B`
    set e : A →+* (↥K) := ((f : A →ₐ[k] B).rangeRestrict : A →+* (↥K)) with he
    have hbij : Function.Bijective e :=
      ⟨fun x y hxy => hf (Subtype.ext_iff.1 hxy), (f : A →ₐ[k] B).rangeRestrict_surjective⟩
    have he_ff : (e : A →+* (↥K)).FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective hbij
    have hK_ff : ((algebraMap (↥K) B) : (↥K) →+* B).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.2 hFF
    have hcomp := RingHom.FaithfullyFlat.stableUnderComposition _ _ he_ff hK_ff
    have hfac : ((algebraMap (↥K) B : (↥K) →+* B).comp e) = (algebraMap A B : A →+* B) := by
      ext a
      rfl
    rw [hfac] at hcomp
    exact RingHom.faithfullyFlat_algebraMap_iff.1 hcomp

end HopfAlgebra.Commutative
end
