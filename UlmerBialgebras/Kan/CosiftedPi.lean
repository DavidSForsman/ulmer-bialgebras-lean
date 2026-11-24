module

public import Foundations.CategoryTheory.Limits.OpTranslate
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import UlmerBialgebras.Kan.Sifted
public import UlmerBialgebras.Kan.SiftedPi

/-!
# The dual of Lemma 4.16: cosifted limits are preserved componentwise

Dually to Lemma 4.16 of *A Syntactic Approach to Ulmer's Bialgebras*, a functor

`F : C₁ × ⋯ × Cₙ ⥤ E`

on a finite product of categories preserves limits of a *cosifted* shape as soon as it
preserves them in each variable separately.

The result is the primal n-ary theorem of `SiftedPi.lean` applied to the opposite functor,
through the equivalence between the opposite of a product and the product of opposites.
The insertion compatibility in `OpTranslate.lean` translates its component hypotheses.

## Main results

* `UlmerBialgebras.preservesLimitsOfShape_pi_of_componentwise`: a functor on a finite product of
  categories preserves limits of a cosifted shape `J` if it preserves them in each variable
  separately (dual form of Lemma 4.16).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.16 (dual form)
* [J. Adámek, J. Rosický, E. M. Vitale,
  *What are sifted colimits?*][AdamekRosickyVitale2010SiftedColimits]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable {ι : Type w} [DecidableEq ι] {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {E : Type*} [Category E]

variable (F : (∀ j, C j) ⥤ E)

/-- **The dual of Lemma 4.16**: a functor on a finite product of categories preserves limits
of a cosifted shape as soon as it preserves them in each variable separately. -/
theorem preservesLimitsOfShape_pi_of_componentwise [IsCosifted J] [Finite ι]
    (h : ∀ (i : ι) (x : ∀ j, C j), PreservesLimitsOfShape J (updateFunctor x i ⋙ F)) :
    PreservesLimitsOfShape J F := by
  let G : (∀ j, (C j)ᵒᵖ) ⥤ Eᵒᵖ := OpTranslate.piOpFrom C ⋙ F.op
  have hG : PreservesColimitsOfShape Jᵒᵖ G := by
    apply preservesColimitsOfShape_pi_of_componentwise
    intro i x
    have := (OpTranslate.preservesLimitsOfShape_iff_op J
      (updateFunctor (fun j => (x j).unop) i ⋙ F)).1 (h i (fun j => (x j).unop))
    change PreservesColimitsOfShape Jᵒᵖ
      (updateFunctor x i ⋙ OpTranslate.piOpFrom C ⋙ F.op)
    rw [← Functor.assoc, OpTranslate.update_op_comp_piOpFrom]
    exact inferInstanceAs (PreservesColimitsOfShape Jᵒᵖ
      (updateFunctor (fun j => (x j).unop) i ⋙ F).op)
  have := hG
  have : PreservesColimitsOfShape Jᵒᵖ (OpTranslate.piOpTo C ⋙ G) := inferInstance
  have : PreservesColimitsOfShape Jᵒᵖ F.op := by
    simpa only [G, ← Functor.assoc, OpTranslate.piOpTo_comp_piOpFrom, Functor.id_comp]
      using (inferInstance : PreservesColimitsOfShape Jᵒᵖ (OpTranslate.piOpTo C ⋙ G))
  exact (OpTranslate.preservesLimitsOfShape_iff_op J F).2 inferInstance

end UlmerBialgebras
