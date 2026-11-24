module

public import UlmerBialgebras.Monadicity.HomCatComp
public import UlmerBialgebras.Monadicity.AccTransfer
public import UlmerBialgebras.Basic.PIE
public import UlmerBialgebras.Basic.AccInsEq
public import Foundations.CategoryTheory.Limits.PiColimits
public import UlmerBialgebras.Monadicity.AccCompleteIff
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import UlmerBialgebras.Monadicity.AccAdjoint

/-!
# Relative cocontinuity

An `A`-cocontinuous 1-cell preserves colimits under post-composition from every object
in `A`. Such 1-cells are closed under composition.

## Main results

* `UlmerBialgebras.IsACocontinuousMor`: a 1-cell is `A`-cocontinuous when every post-composition
  functor `K(a, f)`, `a ∈ A`, preserves colimits (the `A`-cocontinuity of Definition 7.2).
* `UlmerBialgebras.IsACocontinuousMor.comp`: `A`-cocontinuous 1-cells are closed under composition.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 7.2, 7.3 and Theorem 7.7
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe t u v w

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## A helper on products of categories -/

/-! ## The definitions -/

/-- A 1-cell `f : c ⟶ d` is **`A`-cocontinuous** when all the post-composition functors
`K(a, f)`, `a ∈ A`, preserve colimits. -/
def IsACocontinuousMor (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → PreservesColimitsOfSize.{t, t} (postcomp a f)

namespace IsACocontinuousMor

variable {A : ObjectProperty Obj}

/-- `A`-cocontinuous 1-cells are closed under composition. -/
theorem comp {c d e : Obj} {f : c ⟶ d} {g : d ⟶ e}
    (hf : IsACocontinuousMor.{t} A f) (hg : IsACocontinuousMor.{t} A g) :
    IsACocontinuousMor.{t} A (f ≫ g) := by
  intro a ha
  have := hf ha
  have := hg ha
  refine ⟨?_⟩
  intro J _
  rw [postcomp_comp₁ a f g]
  infer_instance

end IsACocontinuousMor

end UlmerBialgebras
