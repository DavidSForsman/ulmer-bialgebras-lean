module

public import Hopf.Graded.GrSubHopf
public import Hopf.Graded.HopfGradedFree

/-!
# A homogeneous basis of the associated graded Hopf algebra over its graded sub-Hopf algebra

Combining the graded structures of `Hopf/Graded/GrSubGrading.lean` and `Hopf/Graded/GrSubHopf.lean`
with `HopfAlgebra.Commutative.exists_homogeneous_basis_of_subHopfAlgebra` gives a homogeneous basis
of the associated graded Hopf algebra `S.Gr` over `gr A`.

## Main results

* `HopfAlgebra.Graded.HopfSplit.exists_homogeneous_basis_grSub`: for a subalgebra `A` stable under
  the projections, the comultiplication and the antipode and containing `1`, `S.Gr` has a basis over
  `S.grSub A` consisting of homogeneous elements.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] {S : HopfSplit k H}
  {A : Subalgebra k H}

/-- **A homogeneous basis of `S.Gr` over `gr A`.** -/
theorem exists_homogeneous_basis_grSub (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) (h1A : (1 : H) ∈ A)
    (hcomulA : ∀ a ∈ A, comul (R := k) a ∈ LinearMap.range (TensorProduct.map
      (Subalgebra.toSubmodule A).subtype (Subalgebra.toSubmodule A).subtype))
    (hantiA : ∀ a ∈ A, antipode k a ∈ A) :
    ∃ (ι : Type u) (d : ι → ℕ) (B : Module.Basis ι ↥(S.grSub A hprA h1A) S.Gr),
      ∀ i, B i ∈ S.grPiece (d i) := by
  have : GradedAlgebra (grAGrading hprA h1A) := gradedAlgebraGrA hprA h1A
  have : SetLike.GradedSMul (grAGrading hprA h1A) S.grPiece := gradedSMul_grAGrading hprA h1A
  exact HopfAlgebra.Commutative.exists_homogeneous_basis_of_subHopfAlgebra k S.Gr
    (S.grSub A hprA h1A) (isSubHopfAlgebra_grSub hprA h1A hcomulA hantiA)
    (grAGrading hprA h1A) S.grPiece (grAGrading_zero_scalar hprA h1A)

end HopfSplit

end HopfAlgebra.Graded
