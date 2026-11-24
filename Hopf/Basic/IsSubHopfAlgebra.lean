module

public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Sub-Hopf algebras

A subalgebra `K` of a Hopf algebra `H` is a **sub-Hopf algebra** if it is closed under the
comultiplication, `Δ K ⊆ K ⊗ K`, and under the antipode. This is the one notion of the project,
used both for commutative Hopf algebras (Takeuchi's correspondence) and for cocommutative ones
(Newman's correspondence).

## Main results

* `HopfAlgebra.IsSubHopfAlgebra`: the class of sub-Hopf algebras.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

namespace HopfAlgebra

variable {k H : Type*} [CommSemiring k] [Semiring H] [HopfAlgebra k H]

variable (k) in
/-- A **sub-Hopf algebra** of `H`: a subalgebra closed under the comultiplication and the
antipode. -/
class IsSubHopfAlgebra (K : Subalgebra k H) : Prop where
  /-- `K` is a subcoalgebra: `Δ K ⊆ K ⊗ K`. -/
  comul_mem : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
    LinearMap.range (TensorProduct.map K.toSubmodule.subtype K.toSubmodule.subtype)
  /-- `K` is closed under the antipode. -/
  antipode_mem : ∀ x ∈ K, antipode k x ∈ K

end HopfAlgebra
