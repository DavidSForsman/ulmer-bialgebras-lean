module

public import Hopf.Commutative.AugSpan

/-!
# Unconditional cases of the surjectivity half of Takeuchi's Theorem 4.3

The surjectivity half of Takeuchi's Theorem 4.3 — every normal Hopf ideal `I` of a commutative
Hopf algebra `H` over a field satisfies `I = K(I)⁺H` — is the proposition
`HopfAlgebra.Commutative.NormalHopfIdealEqAugSpan`, proved in general in
`Hopf/Commutative/AugSpanUnconditional.lean`.  Its two extreme instances are
the zero ideal and the augmentation ideal `H⁺`, which correspond respectively to the two extreme
sub-Hopf algebras `k · 1` and `H`.

This file records the auxiliary fact that `⊤` is a sub-Hopf algebra of `H`
(`HopfAlgebra.Commutative.isSubHopfAlgebra_top`).

## Main results

* `HopfAlgebra.Commutative.isSubHopfAlgebra_top`: `⊤` is a sub-Hopf algebra of `H`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 4.3
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra
namespace HopfAlgebra.Commutative

variable {k H : Type*} [Field k] [CommRing H] [HopfAlgebra k H]

/-! ### The two extreme sub-Hopf algebras -/

/-- `H` is a sub-Hopf algebra of itself. -/
instance isSubHopfAlgebra_top : IsSubHopfAlgebra k (⊤ : Subalgebra k H) where
  comul_mem := by
    intro x _
    have h : Function.Surjective ((⊤ : Subalgebra k H).toSubmodule.subtype) := fun y =>
      ⟨⟨y, Submodule.mem_top⟩, rfl⟩
    have hsurj : Function.Surjective
        (TensorProduct.map (⊤ : Subalgebra k H).toSubmodule.subtype
          (⊤ : Subalgebra k H).toSubmodule.subtype) := by
      apply TensorProduct.map_surjective <;> exact h
    exact hsurj (comul (R := k) x)
  antipode_mem := by
    intro x _
    exact Algebra.mem_top

/-! ### The zero ideal -/

/-! ### The augmentation ideal -/

/-! ### Consequences: the two extreme ideals are normal Hopf ideals -/

end HopfAlgebra.Commutative
end
