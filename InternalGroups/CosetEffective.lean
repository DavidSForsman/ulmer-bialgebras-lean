module

public import InternalGroups.CosetKernel
public import Mathlib.Order.Antisymmetrization

/-!
# Effective cosets from a kernel–quotient equivalence

Effectiveness of coset relations from the stated equivalence between kernel subobjects and quotient
objects.

The results of this file were announced by the author and will appear in a forthcoming
preprint.

## Main results

* `InternalGroups.SubGrpObj.isEffectiveCoset_of_kernelSub_quot_equiv`: if the kernel of the
  quotient `H ⟶ H/S` is equivalent to the subgroup object `S`, then the coset relation of `S` is
  effective.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [M. Barr, *Exact categories*][Ba]
* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace InternalGroups

open UlmerBialgebras

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {H : Grp C}

/-! ## The maximal subgroup object -/

/-! ## Being the quotient by the left cosets of a subobject -/

namespace IsCosetQuotient

variable {N : C} {n : N ⟶ H.X} {Q : C} {π : H.X ⟶ Q}

end IsCosetQuotient

section Quot

variable [HasReflexiveCoequalizers C]

end Quot

/-! ## Injectivity of the Galois connection is effectiveness of the coset relation -/

namespace SubGrpObj

variable [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]
variable [HasFiniteLimits C]

/-- **Converse of the injectivity criterion.**  If the kernel of the quotient `H ⟶ H/S` is `S`
again, then the coset pair of `S` is the kernel pair of `H ⟶ H/S`, i.e. the coset relation of
`S` is effective. -/
theorem isEffectiveCoset_of_kernelSub_quot_equiv {S : SubGrpObj H}
    (h : ((S.quot).kernelSub).Equiv S) : S.IsEffectiveCoset := by
  classical
  have key : ∀ {T : C} (a b : T ⟶ H.X), a ≫ S.quotπ = b ≫ S.quotπ →
      ∃ w : T ⟶ S.N, b * (w ≫ S.n) = a := by
    intro T a b hab
    have h1 : ((S.quot).kernelSub).Mem (b⁻¹ * a) :=
      ((S.quot).mem_kernelSub_inv_mul_iff b a).2 hab.symm
    have h2 : S.Mem (b⁻¹ * a) := (SubGrpObj.le_iff_mem _ _).1 h.1 _ h1
    obtain ⟨w, hw⟩ := h2
    refine ⟨w, ?_⟩
    rw [hw, ← mul_assoc, mul_inv_cancel, one_mul]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk S.quotπ_condition
    (fun s => lift s.snd (Classical.choose (key s.fst s.snd s.condition)))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · rw [S.lift_cosetMul]
    exact Classical.choose_spec (key s.fst s.snd s.condition)
  · exact lift_fst _ _
  · have hm : lift (m ≫ fst H.X S.N) (m ≫ snd H.X S.N) = m := by
      rw [← comp_lift, lift_fst_snd, Category.comp_id]
    have hcos : (m ≫ fst H.X S.N) * ((m ≫ snd H.X S.N) ≫ S.n) = s.fst := by
      rw [← S.lift_cosetMul, hm]; exact hm₁
    have hspec := Classical.choose_spec (key s.fst s.snd s.condition)
    rw [hm₂] at hcos
    have hn : (m ≫ snd H.X S.N) ≫ S.n
        = Classical.choose (key s.fst s.snd s.condition) ≫ S.n :=
      mul_left_cancel (hcos.trans hspec.symm)
    have : m ≫ snd H.X S.N = Classical.choose (key s.fst s.snd s.condition) :=
      (cancel_mono S.n).1 hn
    rw [← hm, hm₂, this]

end SubGrpObj

/-! ## The correspondence is exactly effectiveness of all coset relations -/

section Iff

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]

end Iff

/-! ## The obstruction: collapsing quotients -/

section Obstruction

variable [HasEqualizers C] [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]

variable [HasFiniteLimits C]

end Obstruction

/-! ## The two posets, and the isomorphism between them -/

section Posets

end Posets

section OrderIso

variable [HasFiniteLimits C] [HasReflexiveCoequalizers C]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]

end OrderIso

end InternalGroups
