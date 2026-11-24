module

public import AffineGroupSchemes.HopfEqualizer

/-!
# Regular monomorphisms of commutative Hopf algebras

Over a field, and granting Takeuchi's faithful flatness theorem, the regular monomorphisms of
commutative Hopf algebras are exactly the injective morphisms:

* `AffineGroupSchemes.CommHopfAlgCat.regularMonoOfInjective`: an injective morphism `m : A → B` is
  the equalizer of the two coprojections `B ⇉ B ⊗[A] B`, hence a regular monomorphism;
* `AffineGroupSchemes.CommHopfAlgCat.injective_of_regularMono`: conversely a regular monomorphism is
  injective — it is an extremal monomorphism, and extremal monomorphisms are injective by the
  surjection/injection factorization system
  (`AffineGroupSchemes.CommHopfAlgCat.injective_of_extremalMono`).

This is the heart of Theorem 3.12 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*.

## Main results

* `AffineGroupSchemes.CommHopfAlgCat.regularMonoOfInjective`: over a field, assuming
  `HopfAlgebra.InjectiveIsFaithfullyFlat`, an injective morphism of commutative Hopf algebras is a
  regular monomorphism.
* `AffineGroupSchemes.CommHopfAlgCat.injective_of_regularMono`: over a field, a regular monomorphism
  of commutative Hopf algebras is injective.

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Chapter 14
-/

@[expose] public section

open TensorProduct Coalgebra Function CategoryTheory Limits

namespace AffineGroupSchemes

open CategoryTheory
open HopfAlgebra

universe u

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

section Injective

variable {A B : CommHopfAlgCat.{u} k} (m : A ⟶ B) (hm : Injective m)

/-- The `A`-algebra structure on `B` given by a morphism `m : A ⟶ B`. -/
noncomputable abbrev algebraOfHom : Algebra A B := algebraOfBialgHom m.hom

include hm in
/-- **An injective morphism of commutative Hopf algebras is a regular monomorphism**: it is the
equalizer of the two coprojections into `B ⊗[A] B`. -/
noncomputable def regularMonoOfInjective (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u}) :
    RegularMono m := by
  letI : Algebra A B := algebraOfHom m
  haveI : IsScalarTower k A B :=
    .of_algebraMap_eq fun r => ((m.hom : A →ₐ[k] B).commutes r).symm
  have hmm : ∀ a : A, algebraMap A B a = m.hom a := fun _ => rfl
  have hid : ∀ a : A, algebraMap A A a = (BialgHom.id k A) a := fun _ => rfl
  letI := hopfAlgebraTensor m.hom m.hom hmm hmm
  exact
    { Z := CommHopfAlgCat.of k (B ⊗[A] B)
      left := CommHopfAlgCat.ofHom (inlBialgHom m.hom m.hom hmm hmm)
      right := CommHopfAlgCat.ofHom (inrBialgHom m.hom m.hom hmm hmm)
      w := fork_condition m.hom (BialgHom.id k A) m.hom hmm (fun _ => rfl) surjective_id
      isLimit := isLimitForkImage m.hom (BialgHom.id k A) m.hom hmm hid hmm (fun _ => rfl) hm
        surjective_id hInjFlat }

end Injective

section Converse

variable {A B : CommHopfAlgCat.{u} k}

/-- **A regular monomorphism of commutative Hopf algebras is injective.** -/
theorem injective_of_regularMono {m : A ⟶ B} (h : RegularMono m) : Injective m :=
  have := h.extremalMono
  injective_of_extremalMono m

end Converse

end CommHopfAlgCat

end AffineGroupSchemes
