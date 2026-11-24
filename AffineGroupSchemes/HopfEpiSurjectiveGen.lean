module

public import Foundations.RingTheory.AmitsurEqualizer
public import AffineGroupSchemes.HopfPushout
public import Foundations.RingTheory.AbsFlatClass
public import AffineGroupSchemes.VonNeumannRegularUnconditional
public import Mathlib.RingTheory.Bialgebra.Hom
public import Hopf.Basic.AntipodeAlgHom
public import Hopf.Basic.AntipodeBialgHom
public import Foundations.CategoryTheory.Factorization.ExtremalMono
public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import AffineGroupSchemes.HopfRegularMono
public import Hopf.Commutative.FaithfulFlatnessUnconditional

/-!
# Surjectivity of injective Hopf epimorphisms

The criterion making an injective categorical epimorphism of Hopf algebras surjective.

## Main results

* `AffineGroupSchemes.HopfGen.Hopf.surjective_of_injective_of_epi`: over an absolutely flat base
  ring, an injective morphism of commutative Hopf algebras that is an epimorphism among commutative
  Hopf algebras is surjective.

## References

* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Section 4
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972]
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Chapters 13–14
-/

@[expose] public section

open TensorProduct Coalgebra Function CategoryTheory Limits

namespace AffineGroupSchemes

open HopfAlgebra
namespace HopfGen

universe u

namespace Hopf

variable {k A B : Type u} [CommRing k] [IsAbsFlat k] [CommRing A] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k B]

/-- An injective morphism of commutative Hopf algebras which is an epimorphism is surjective. -/
theorem surjective_of_injective_of_epi (m : A →ₐc[k] B) (hm : Injective m)
    (hepi : ∀ (T : Type u) (_ : CommRing T) (_ : HopfAlgebra k T) (α β : B →ₐc[k] T),
      (∀ a, α (m a) = β (m a)) → ∀ b, α b = β b) :
    Surjective m := by
  let : Algebra A B := algebraOfBialgHom m
  have : IsScalarTower k A B :=
    .of_algebraMap_eq fun r => ((m : A →ₐ[k] B).commutes r).symm
  have hmm : ∀ a : A, algebraMap A B a = m a := fun _ => rfl
  have : Module.FaithfullyFlat A B :=
    faithfullyFlat_of_injective_of_isVonNeumannRegular_holds IsAbsFlat.isVonNeumannRegular m hm
  let := hopfAlgebraTensor m m hmm hmm
  have hfork : ∀ a : A, (inlBialgHom m m hmm hmm) (m a) = (inrBialgHom m m hmm hmm) (m a) := by
    intro a
    change (m a) ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] (m a)
    rw [← hmm a, Algebra.algebraMap_eq_smul_one, smul_tmul]
  intro b
  have hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b :=
    hepi (B ⊗[A] B) inferInstance inferInstance (inlBialgHom m m hmm hmm)
      (inrBialgHom m m hmm hmm) hfork b
  obtain ⟨a, ha⟩ := Algebra.TensorProduct.mem_range_of_tmul_eq b hb
  exact ⟨a, by rwa [hmm a] at ha⟩

end Hopf


end HopfGen
end AffineGroupSchemes
