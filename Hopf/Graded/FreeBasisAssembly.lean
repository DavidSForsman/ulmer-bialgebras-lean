module

public import Hopf.Graded.FreeBasisFromGraded
public import Hopf.Graded.CoradicalSplit
public import Hopf.Graded.GrHomBasis

/-!
# Existence of Sweedler bases over a sub-Hopf algebra

Assembling the pieces:

* `HopfAlgebra.Graded.exists_hopfSplit_oneFiltration` — the coradical filtration of the irreducible
  component of the unit of a cocommutative Hopf algebra underlies a split filtered Hopf algebra
  whose projections preserve a prescribed subalgebra `A`;
* `HopfAlgebra.Graded.HopfSplit.exists_homogeneous_basis_grSub` — the associated graded Hopf algebra
  `Gr` has a homogeneous basis over the associated graded subalgebra `gr A` (Takeuchi's theorem for
  commutative Hopf algebras plus graded Nakayama);
* `Hopf/Graded/FreeBasisFromGraded.lean` — such a homogeneous basis lifts to a
  Sweedler basis of the filtration.

This gives `HopfAlgebra.Graded.hasGradedFreeBasis_of_subHopfAlgebra`: **any sub-Hopf algebra `A` of
a cocommutative Hopf algebra `H` admits a Sweedler basis of the coradical filtration of `H₁`.**

## Main results

* `HopfAlgebra.Graded.hasGradedFreeBasis_of_subHopfAlgebra`: a subalgebra `A` of a cocommutative
  Hopf algebra over a field which is stable under the comultiplication and the antipode has a
  Sweedler basis.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical HopfAlgebra
open Module.FilteredFree HopfAlgebra.Commutative.Cocomm
open HopfAlgebra.Commutative.Cocomm

namespace HopfAlgebra.Graded

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- **A sub-Hopf algebra of a cocommutative Hopf algebra admits a Sweedler basis.**  The
hypotheses `hcomulA`, `hantiA` say that the subalgebra `A` is stable under the comultiplication
and the antipode, i.e. that it is a sub-Hopf algebra. -/
theorem hasGradedFreeBasis_of_subHopfAlgebra (A : Subalgebra k H)
    (hcomulA : ∀ a ∈ A, comul (R := k) a ∈ LinearMap.range (TensorProduct.map
      (Subalgebra.toSubmodule A).subtype (Subalgebra.toSubmodule A).subtype))
    (hantiA : ∀ a ∈ A, antipode k a ∈ A) :
    HasGradedFreeBasis A := by
  obtain ⟨S, hSF, hpr⟩ :=
    exists_hopfSplit_oneFiltration (Subalgebra.toSubmodule A) A.one_mem
  have hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A := fun n a ha =>
    (Subalgebra.mem_toSubmodule A).1 (hpr n a ((Subalgebra.mem_toSubmodule A).2 ha))
  obtain ⟨ι, d, B, hB⟩ :=
    HopfSplit.exists_homogeneous_basis_grSub hprA A.one_mem hcomulA hantiA
  refine ⟨ι, HopfSplit.sbElt B, d, ?_, ?_, ?_, ?_⟩ <;> rw [← hSF]
  · exact fun j => HopfSplit.sbElt_mem_F B hB j
  · exact fun n => HopfSplit.span_le B hB n
  · exact HopfSplit.gradedIndependent_zero B hB
  · exact HopfSplit.gradedIndependent_step B hB

end HopfAlgebra.Graded
