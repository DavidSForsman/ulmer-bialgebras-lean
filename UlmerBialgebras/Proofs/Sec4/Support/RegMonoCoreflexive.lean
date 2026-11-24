module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public import UlmerBialgebras.Proofs.Sec4.Support.RegMonoWidePullbackPi

/-!
# Coreflexive presentations from cokernel pairs

The regular-mono criterion is the regular-epi kernel-pair criterion in the opposite category.

## Main results

* `UlmerBialgebras.RegMonoWide.regularMonosAreCoreflexiveEqualizers_of_hasCokernelPairs`: in a
  category with cokernel pairs, every regular monomorphism is a coreflexive equalizer.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.18, Example 4.20 (2)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.RegMonoWide

open CategoryTheory Limits

variable {X : Type u} [Category.{v} X]

/-- With cokernel pairs, every regular monomorphism has a coreflexive equalizer presentation,
by the kernel-pair criterion in the opposite category. -/
theorem regularMonosAreCoreflexiveEqualizers_of_hasCokernelPairs
    (h : ∀ ⦃a c : X⦄ (m : a ⟶ c), HasPushout m m) : RegularMonosAreCoreflexiveEqualizers X := by
  apply OpTranslate.regularMonos_coreflexive_iff_op.mpr
  apply OpTranslate.regEpis_reflexive_of_kernelPairs
  intro a b f
  have := h f.unop
  exact (hasPullback_op_iff_hasPushout f.unop f.unop).2 inferInstance

end UlmerBialgebras.RegMonoWide
