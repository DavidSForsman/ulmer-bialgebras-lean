module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Hopf.Basic.HopfFaithfulFlatness

/-!
# Faithfully flat morphisms are pushout-stable injections

The pushout in commutative rings of a faithfully flat morphism `H → G` along any morphism
`H → X` is the tensor product, and the pushout morphism `X → X ⊗[H] G` is injective. This is the
ring-theoretic step of the proof of coregularity (Theorem 3.12 of the paper on affine group
schemes): faithfully flat morphisms, the class `M'` there, are stable under pushout.

## Main results

* `AffineGroupSchemes.injective_algebraMap_pushout`: if `H → G` is faithfully flat, then for every
  `H`-algebra `X` the map `X → X ⊗[H] G` is injective.

## References

* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  3.1
-/

@[expose] public section

namespace AffineGroupSchemes


open TensorProduct

universe u

section Ring

variable (H G X : Type*) [CommRing H] [CommRing G] [CommRing X] [Algebra H G] [Algebra H X]

/-- **Faithfully flat morphisms are pushout-stable injections.** The pushout `X → X ⊗[H] G` of a
faithfully flat morphism `H → G` along an arbitrary morphism `H → X` is injective. -/
theorem injective_algebraMap_pushout [Module.FaithfullyFlat H G] :
    Function.Injective (algebraMap X (X ⊗[H] G)) :=
  FaithfulSMul.algebraMap_injective X (X ⊗[H] G)

end Ring

end AffineGroupSchemes
