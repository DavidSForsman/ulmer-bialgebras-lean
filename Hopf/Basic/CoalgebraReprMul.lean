module

public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Products of Sweedler representations

Auxiliary Sweedler-calculus lemmas used in the proof of Takeuchi's faithful flatness theorem.

* `Coalgebra.Repr.mul`: from representations `Δx = ∑ xᵢ' ⊗ xᵢ''` and `Δy = ∑ yⱼ' ⊗ yⱼ''` in a
  bialgebra one gets the representation `Δ(xy) = ∑ xᵢ'yⱼ' ⊗ xᵢ''yⱼ''` (now in Mathlib, re-exported
  through the import);
* `Coalgebra.sum_smul_counit`: the counit law in the form `∑ ε(xᵢ'') • xᵢ' = x`.

## Main results

* `Coalgebra.sum_smul_counit`: for a representation `r` of `Δ a`,
  `∑ i ∈ r.index, ε (r.right i) • r.left i = a`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter I
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

namespace Coalgebra

open _root_.TensorProduct

variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

-- `Coalgebra.Repr.mul` (with the `@[simps]` lemmas `mul_index`, `mul_left`, `mul_right`) is now
-- provided by Mathlib in `Mathlib.RingTheory.Bialgebra.TensorProduct`; an own copy would clash.

variable {a : A}

/-- The counit law `∑ ε(a₍₂₎) • a₍₁₎ = a`. -/
lemma sum_smul_counit {ι : Type*} (r : Repr R a ι) :
    ∑ i ∈ r.index, (counit (R := R) (r.right i)) • r.left i = a := by
  simpa only [map_sum, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.lsmul_apply,
    one_smul] using congr(TensorProduct.lift ((LinearMap.lsmul R A).flip)
      $(sum_tmul_counit_eq (R := R) r))

end Coalgebra
