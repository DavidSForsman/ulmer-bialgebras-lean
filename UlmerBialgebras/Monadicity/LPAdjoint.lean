module

public import UlmerBialgebras.Monadicity.AccCoWellPowered
public import UlmerBialgebras.Monadicity.ComonPresentable

/-!
# The adjoint functor theorem for locally presentable categories

A colimit-preserving functor out of a locally presentable category is a left adjoint.  This is
the form of the adjoint functor theorem that is actually usable in the setting of internal
algebraic structures: a locally presentable category is cocomplete, co-well-powered, and has a
small strong generator, which are exactly the hypotheses of the special adjoint functor theorem.

* `UlmerBialgebras.isLeftAdjoint_of_preservesColimits_of_isLocallyPresentable` — the theorem.

The three ingredients are already in the development:

* cocompleteness — `UlmerBialgebras.hasColimitsOfSize_of_isLocallyPresentable`;
* co-well-poweredness — `UlmerBialgebras.wellPowered_op_of_isLocallyPresentable`;
* a small strong generator — `IsCardinalLocallyPresentable.iff_exists_isStrongGenerator`, whose
  first component is a small separating family.

## Main results

* `UlmerBialgebras.isLeftAdjoint_of_preservesColimits_of_isLocallyPresentable`: a colimit-preserving
  functor out of a locally presentable category is a left adjoint (Theorem 5.10 (1)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.10 (1)
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe w u u'

open CategoryTheory Limits ObjectProperty

namespace UlmerBialgebras

/-- **The adjoint functor theorem for locally presentable categories** (Theorem 5.10 (1) of
[forsman2026syntactic]): a functor out of a
locally presentable category which preserves all colimits has a right adjoint.

A locally presentable category is cocomplete and co-well-powered, and has a small strong
generator, hence in particular a small separating family; so this is an instance of the special
adjoint functor theorem. -/
theorem isLeftAdjoint_of_preservesColimits_of_isLocallyPresentable
    {C : Type u} [Category.{w} C] [IsLocallyPresentable.{w} C]
    {D : Type u'} [Category.{w} D] (F : C ⥤ D) [PreservesColimitsOfSize.{w, w} F] :
    F.IsLeftAdjoint := by
  obtain ⟨κ, hκ, hC⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  have := hκ
  have := hC
  have : HasColimits C := hasColimitsOfSize_of_isLocallyPresentable C
  have : WellPowered.{w} Cᵒᵖ := wellPowered_op_of_isLocallyPresentable C
  obtain ⟨P, hPs, hP, -⟩ := (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator C κ).1 hC
  have := hPs
  exact isLeftAdjoint_of_preservesColimits_of_isSeparating hP.1 F

end UlmerBialgebras
