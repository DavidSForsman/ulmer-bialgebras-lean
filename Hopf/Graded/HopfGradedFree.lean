module

public import Hopf.Graded.FlatFree
public import Hopf.Commutative.FaithfulFlatnessUnconditional

/-!
# Graded freeness over a graded sub-Hopf algebra (commutative case)

This file combines two results of the project:

* Takeuchi's theorem (`HopfAlgebra.Commutative.faithfullyFlat_subHopfAlgebra`): a commutative Hopf
  algebra over a field is faithfully flat over any of its sub-Hopf algebras;
* graded Nakayama (`HopfAlgebra.Graded.Free.exists_homogeneous_basis`): a flat graded module over a
  connected graded algebra has a homogeneous basis.

Together they give **step 2 of Sweedler's freeness theorem**: a connected graded commutative Hopf
algebra is *graded free* over a graded sub-Hopf algebra
(`HopfAlgebra.Commutative.exists_homogeneous_basis_of_subHopfAlgebra`).

The grading data is taken as input here: `𝒜` is a connected `ℕ`-grading of the sub-Hopf algebra
`K` and `ℳ` an `ℕ`-grading of `H` compatible with it.  In the intended application `H` and `K`
are the associated graded algebras of the coradical filtrations of an irreducible cocommutative
Hopf algebra `H₁` and of a sub-Hopf algebra of it (which are commutative by
`Coalgebra.Coradical.comm_oneFiltration_le`), and the gradings are the tautological ones.

## Main results

* `HopfAlgebra.Commutative.exists_homogeneous_basis_of_subHopfAlgebra`: for a sub-Hopf algebra `K`
  of a commutative Hopf algebra `H` over a field, a grading `𝒜` of `K` with scalar degree-zero part
  and a compatible grading `ℳ` of `H`, `H` has a basis over `K` consisting of homogeneous elements.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapters 13–14
* [J. W. Milnor, J. C. Moore, *On the structure of Hopf algebras*][Milnor-Moore]
-/

@[expose] public section

universe u

section
open HopfAlgebra
namespace HopfAlgebra.Commutative


/-- **A connected graded commutative Hopf algebra is graded free over a graded sub-Hopf
algebra.**  Precisely: let `K` be a sub-Hopf algebra of a commutative Hopf `k`-algebra `H`,
let `𝒜` be a connected `ℕ`-grading of `K` as a `k`-algebra and `ℳ` an `ℕ`-grading of `H` as a
`k`-module with `𝒜 i · ℳ j ⊆ ℳ (i + j)`.  Then `H` has a basis over `K` consisting of
homogeneous elements. -/
theorem exists_homogeneous_basis_of_subHopfAlgebra
    (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) (hK : IsSubHopfAlgebra k K)
    (𝒜 : ℕ → Submodule k (↥K)) (ℳ : ℕ → Submodule k H)
    [GradedAlgebra 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k (↥K) c) :
    ∃ (ι : Type u) (d : ι → ℕ) (B : Module.Basis ι (↥K) H), ∀ i, B i ∈ ℳ (d i) := by
  have : Module.FaithfullyFlat (↥K) H
      := HopfAlgebra.Commutative.faithfullyFlat_subHopfAlgebra k H K hK
  have : Module.Flat (↥K) H := inferInstance
  exact HopfAlgebra.Graded.Free.exists_homogeneous_basis 𝒜 ℳ h0

end HopfAlgebra.Commutative
end
