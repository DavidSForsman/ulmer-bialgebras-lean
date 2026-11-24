module

public import Hopf.Coradical.Wedge
public import Hopf.Basic.CoalgebraLocallyFinite

/-!
# Simple subcoalgebras

A simple subcoalgebra is nonzero and has no proper nonzero subcoalgebra. Intersections of
subcoalgebras are again subcoalgebras.

## Main results

* `Coalgebra.Coradical.isSubcoalgebra_inf`: the intersection of two subcoalgebras is a subcoalgebra.
* `Coalgebra.Coradical.IsSimpleSubcoalgebra`: a nonzero subcoalgebra `W` such that every
  subcoalgebra `V ≤ W` is `⊥` or `W`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 2.2.1 and Chapters 8–9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Chapter 5
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- An intersection of two subcoalgebras is a subcoalgebra. -/
theorem isSubcoalgebra_inf {V W : Submodule k C} (hV : IsSubcoalgebra V)
    (hW : IsSubcoalgebra W) : IsSubcoalgebra (V ⊓ W) := by
  rw [isSubcoalgebra_iff]
  intro x hx
  rw [← tens_inf_tens]
  exact ⟨comul_mem_tens hV hx.1, comul_mem_tens hW hx.2⟩

/-- A **simple subcoalgebra** is a nonzero subcoalgebra whose only subcoalgebras are `0` and
itself. -/
def IsSimpleSubcoalgebra (W : Submodule k C) : Prop :=
  IsSubcoalgebra W ∧ W ≠ ⊥ ∧ ∀ V : Submodule k C, V ≤ W → IsSubcoalgebra V → V = ⊥ ∨ V = W

end Coalgebra.Coradical
