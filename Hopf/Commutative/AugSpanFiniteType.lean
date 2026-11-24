module

public import Hopf.Commutative.HopfIdealComap
public import Hopf.Commutative.CharacterFunctional
public import Hopf.Basic.HopfLocallyFinite

/-!
# Reduction of Takeuchi's Theorem 4.3 to finitely generated Hopf algebras

A commutative Hopf algebra over a field is the directed union of its finitely generated sub-Hopf
algebras (`HopfAlgebra.LocallyFinite.exists_fg_isSubHopfAlgebra`), and the surjectivity half of
Takeuchi's Theorem 4.3 — every normal Hopf ideal `I` satisfies `I = K(I)⁺H` — is a statement about
one element of `I` at a time. Restricting `I` to a finitely generated sub-Hopf algebra `A ⊆ H` gives
a normal Hopf ideal `f⁻¹(I)` of `A` (`HopfAlgebra.Commutative.isNormalHopfIdeal_comapIdeal`), whose
coinvariants are carried into those of `I`; so the statement for `H` follows from the statement for
the finitely generated `A`.

Combined with `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_of_isAlgClosed_of_finiteType` this
proves the surjectivity half of Theorem 4.3 for an **arbitrary** commutative Hopf algebra over an
algebraically closed field.

## Main results

* `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_of_finiteType`: the reduction to the finitely
  generated case;
* `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_of_isAlgClosed`: the surjectivity half of
  Theorem 4.3 over an algebraically closed field.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 4.3
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **Reduction of the surjectivity half of Takeuchi's Theorem 4.3 to the finitely generated
case**: if every normal Hopf ideal of every finitely generated commutative Hopf algebra over `k`
is of the form `K⁺A`, the same holds for an arbitrary commutative Hopf algebra over `k`. -/
theorem normalHopfIdealEqAugSpan_of_finiteType
    (hfg : ∀ (A : Type u) [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A],
      NormalHopfIdealEqAugSpan k A) :
    NormalHopfIdealEqAugSpan k H := by
  classical
  intro I hI
  refine le_antisymm ?_ (augIdeal_coinv_le I)
  intro y hy
  obtain ⟨A₀, hA₀sub, hA₀ft, hmem⟩ :=
    HopfAlgebra.LocallyFinite.exists_fg_isSubHopfAlgebra (k := k) ({y} : Finset H)
  have := hA₀sub
  have := hA₀ft
  have hyA : y ∈ A₀ := hmem y (Finset.mem_singleton_self y)
  set f : (↥A₀) →ₐc[k] H := subInclusion with hf
  have hfinj : Function.Injective f := subInclusion_injective
  have hJ : IsNormalHopfIdeal k (comapIdeal f I) := isNormalHopfIdeal_comapIdeal f I hfinj hI
  have hy' : (⟨y, hyA⟩ : ↥A₀) ∈ comapIdeal f I := hy
  rw [hfg (↥A₀) (comapIdeal f I) hJ] at hy'
  have hmain := augIdeal_coinv_comapIdeal_le f I hy'
  simpa [hf] using hmain

/-- **The surjectivity half of Takeuchi's Theorem 4.3 over an algebraically closed field**: every
normal Hopf ideal `I` of a commutative Hopf algebra `H` over an algebraically closed field
satisfies `I = K(I)⁺H`. -/
theorem normalHopfIdealEqAugSpan_of_isAlgClosed [IsAlgClosed k] : NormalHopfIdealEqAugSpan k H :=
  normalHopfIdealEqAugSpan_of_finiteType
    (fun A _ _ _ => normalHopfIdealEqAugSpan_of_isAlgClosed_of_finiteType (k := k) (H := A))

end HopfAlgebra.Commutative
end
