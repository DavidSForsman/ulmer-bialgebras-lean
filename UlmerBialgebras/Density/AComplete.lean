module

public import UlmerBialgebras.Monadicity.HomCatComp
public import UlmerBialgebras.Monadicity.AccTransfer
public import UlmerBialgebras.Basic.PIE
public import UlmerBialgebras.Density.ALocPres
public import UlmerBialgebras.Kan.LiftLimits
public import Foundations.CategoryTheory.Limits.PiLimits
public import Foundations.CategoryTheory.Limits.OpTranslate
public import UlmerBialgebras.Monadicity.AccAdjoint

/-!
# Relative continuity

An `A`-continuous 1-cell preserves limits under post-composition from every object in `A`.
Such 1-cells are closed under composition.

## Main results

* `UlmerBialgebras.IsAContinuousMor`: a 1-cell is `A`-continuous when every post-composition functor
  `K(a, f)`, `a ∈ A`, preserves limits (the `A`-continuity of Definition 7.2).
* `UlmerBialgebras.IsAContinuousMor.comp`: `A`-continuous 1-cells are closed under composition.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 7.2, 7.3 and Theorem 7.7
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Corollary 2.47
-/

@[expose] public section

universe t u v w

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## A helper on products of categories -/

/-! ## The definitions -/

/-- A 1-cell `f : c ⟶ d` is **`A`-continuous** when all the post-composition functors
`K(a, f)`, `a ∈ A`, preserve limits. -/
def IsAContinuousMor (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → PreservesLimitsOfSize.{t, t} (postcomp a f)



namespace IsAContinuousMor

variable {A : ObjectProperty Obj}

/-- `A`-continuous 1-cells are closed under composition. -/
theorem comp {c d e : Obj} {f : c ⟶ d} {g : d ⟶ e}
    (hf : IsAContinuousMor.{t} A f) (hg : IsAContinuousMor.{t} A g) :
    IsAContinuousMor.{t} A (f ≫ g) := by
  intro a ha
  have := hf ha
  have := hg ha
  refine ⟨?_⟩
  intro J _
  rw [postcomp_comp₁ a f g]
  infer_instance

end IsAContinuousMor

end UlmerBialgebras
