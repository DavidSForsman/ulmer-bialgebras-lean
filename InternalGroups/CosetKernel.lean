module

public import Mathlib.Tactic.Group
public import InternalGroups.SubgroupCorrespondence
public import Foundations.CategoryTheory.Factorization.ExactCriterion

/-!
# Effective coset relations

The effectiveness condition for coset relations and the kernel-membership criterion for quotient
objects.

## Main results

* `InternalGroups.QuotObj.mem_kernelSub_inv_mul_iff`: `g⁻¹ * h` lies in the kernel of an
  equivariant quotient `P` if and only if `g ≫ P.q = h ≫ P.q`.
* `InternalGroups.SubGrpObj.IsEffectiveCoset`: the coset relation of a subgroup object `S` is
  effective when the coset pair on `H ⊗ S` is the kernel pair of its coequalizer `H ⟶ H/S`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapters 13–14
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

universe w v₂ v u₂ u

namespace InternalGroups

open UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj Obj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## Elements of the kernel of an equivariant quotient -/

namespace QuotObj

variable [HasEqualizers C] {H : Grp C}

/-- Two generalized elements of `H` have the same image in an equivariant quotient `P`
exactly when their "quotient" `g⁻¹ h` lies in the kernel of `P`. -/
lemma mem_kernelSub_inv_mul_iff (P : QuotObj H) {T : C} (g h : T ⟶ H.X) :
    (P.kernelSub).Mem (g⁻¹ * h) ↔ g ≫ P.q = h ≫ P.q := by
  rw [P.mem_kernelSub]
  constructor
  · intro hgh
    have h1 : (g * (g⁻¹ * h)) ≫ P.q = (g * 1) ≫ P.q := by
      rw [← P.equivariant g (g⁻¹ * h), hgh, P.equivariant g 1]
    rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h1
    exact h1.symm
  · intro hgh
    calc (g⁻¹ * h) ≫ P.q = P.smul g⁻¹ (h ≫ P.q) := (P.equivariant g⁻¹ h).symm
      _ = P.smul g⁻¹ (g ≫ P.q) := by rw [hgh]
      _ = (g⁻¹ * g) ≫ P.q := P.equivariant g⁻¹ g
      _ = (1 : T ⟶ H.X) ≫ P.q := by rw [inv_mul_cancel]

end QuotObj

/-! ## Surjectivity: a regular epimorphic quotient is the quotient by its kernel -/

section Surjectivity

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]
variable {H : Grp C}

end Surjectivity

/-! ## Injectivity: effectiveness of the coset relation -/

namespace SubGrpObj

variable [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]
variable {H : Grp C}

/-- The coset relation of a subgroup object `S` of `H` is **effective** when the coset pair
`(g, z) ↦ g z`, `(g, z) ↦ g` on `H ⊗ S` is the kernel pair of its coequalizer `H ⟶ H/S`.

This is the descent-theoretic input of the injectivity half of Newman's correspondence for
regular epimorphisms; in the Hopf-algebra case it is the faithful flatness of `H` over the
sub-Hopf algebra `S` (Takeuchi [Takeuchi1972]). -/
def IsEffectiveCoset (S : SubGrpObj H) : Prop :=
  IsKernelPair S.quotπ S.cosetMul (fst H.X S.N)

variable [HasFiniteLimits C]

end SubGrpObj

/-! ## Newman's correspondence for regular epimorphisms -/

section HopfIdealCorrespondence

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]

end HopfIdealCorrespondence

/-! ## An example: the trivial subgroup object

The definitions above are not vacuous: the coset relation of the trivial subgroup object is
always effective, because the quotient by it is an isomorphism. -/

section Trivial

variable [HasReflexiveCoequalizers C]

end Trivial

end InternalGroups
