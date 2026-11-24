module

public import AffineGroupSchemes.HopfImage
public import Foundations.CategoryTheory.Factorization.ExtremalMono
public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Foundations.CategoryTheory.Exact.SemiAbelian

/-!
# The factorization system of surjections and injections on commutative Hopf algebras

The proof of Theorem 3.12 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*,

lifts the orthogonal factorization system `(E, M)` of surjections and injections from
commutative `k`-algebras to commutative Hopf `k`-algebras.  This file records that step in the
bundled category:

* `AffineGroupSchemes.exists_hopfAlgebra_image_factorization` (in
  `AffineGroupSchemes/HopfImage.lean`) provides the factorization of a morphism of commutative Hopf
  algebras as a surjection followed by an injection;
* `AffineGroupSchemes.CommHopfAlgCat.hasSurjectiveInjectiveFactorization` packages it as an instance
  of `ConcreteCategory.HasSurjectiveInjectiveFactorization`;
* `AffineGroupSchemes.CommHopfAlgCat.injective_of_extremalMono`: every extremal monomorphism of
  commutative Hopf algebras is injective, by orthogonality against the surjections.

## Main results

* `AffineGroupSchemes.CommHopfAlgCat.hasSurjectiveInjectiveFactorization`: every morphism of
  commutative Hopf `k`-algebras factors as a surjection followed by an injection (`k` a field).
* `AffineGroupSchemes.CommHopfAlgCat.injective_of_extremalMono`: every extremal monomorphism of
  commutative Hopf `k`-algebras is injective (`k` a field).

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra Function CategoryTheory

universe v u

namespace AffineGroupSchemes

open CategoryTheory

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- **Image factorization in the bundled category.** Every morphism of commutative Hopf
`k`-algebras factors as a surjection followed by an injection. -/
instance hasSurjectiveInjectiveFactorization :
    ConcreteCategory.HasSurjectiveInjectiveFactorization (CommHopfAlgCat.{v} k) where
  nonempty_mapFactorizationData {A B} f := by
    obtain ⟨S, _, _, e, m, he, hm, hfac⟩ := exists_hopfAlgebra_image_factorization f.hom
    exact ⟨{ Z := CommHopfAlgCat.of k S
             i := CommHopfAlgCat.ofHom e
             p := CommHopfAlgCat.ofHom m
             fac := by ext a; exact hfac a
             hi := he
             hp := hm }⟩

/-- Every extremal monomorphism of commutative Hopf `k`-algebras is injective.  This is the
last step of the proof of Theorem 3.12: "as every surjection is an epimorphism, we have by
orthogonality that every extremal monomorphism is in `M'`". -/
theorem injective_of_extremalMono {A B : CommHopfAlgCat.{v} k} (f : A ⟶ B)
    [ExtremalMono f] : Function.Injective f :=
  mem_of_extremalMono (W₁ := MorphismProperty.surjective (CommHopfAlgCat.{v} k))
    (W₂ := MorphismProperty.injective (CommHopfAlgCat.{v} k))
    (fun _ _ g hg => ConcreteCategory.epi_of_surjective g hg) f

end CommHopfAlgCat

end AffineGroupSchemes
