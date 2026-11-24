module

public import UlmerBialgebras.Proofs.Sec4.OpTranslateWide

/-!
# Regular-mono preservation in finite products, by opposite-category duality

For a nontrivial wide-pullback shape, apply the regular-epi result to the product of
opposite categories and transport through `OpTranslate.piOpEquiv`. Componentwise
regular-mono interfaces support the model-level creation argument.

## Main results

* `UlmerBialgebras.RegMonoWide.isRegularMono_eval`: the evaluations of a product of categories
  preserve regular monomorphisms.
* `UlmerBialgebras.RegMonoWide.preservesWidePullbacks_and_regularMonos_pi`: the dual of
  Corollary 4.18: for a finite product of categories in which regular monos are coreflexive
  equalizers, a functor whose partial functors preserve wide pullbacks of regular monos of a
  nontrivial shape preserves such wide pullbacks and regular monomorphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.18, Theorem 4.19, Example 4.20 (2)
-/

@[expose] public section

universe w w' v u v₃ u₃

namespace UlmerBialgebras.RegMonoWide

open CategoryTheory Limits

variable {K : Type w}
variable {ι : Type w'} [decι : DecidableEq ι] {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {E : Type u₃} [Category.{v₃} E]

/-- Componentwise regular monomorphisms. -/
def piRegMono : MorphismProperty (∀ j, C j) := fun _ _ f => ∀ j, IsRegularMono (f j)

omit decι in
/-- Product evaluations preserve regular monomorphisms, by duality. -/
lemma isRegularMono_eval {x y : ∀ j, C j} (f : x ⟶ y) [IsRegularMono f] (j : ι) :
    IsRegularMono (f j) := by
  have := OpTranslate.piEval_preservesLimitsOfShape C WalkingParallelPair j
  exact OpTranslate.isRegularMono_map (Pi.eval C j) f

variable (F : (∀ j, C j) ⥤ E)

/-- Both clauses of the dual Corollary 4.18, obtained from the primal corollary. -/
theorem preservesWidePullbacks_and_regularMonos_pi {K : Type w} [Nontrivial K]
    {ι : Type w'} [DecidableEq ι] [Finite ι] {C : ι → Type u} [∀ i, Category.{v} (C i)]
    {E : Type*} [Category E] (F : (∀ j, C j) ⥤ E)
    (hC : ∀ i, RegularMonosAreCoreflexiveEqualizers (C i))
    (hF : ∀ (i : ι) (x : ∀ j, C j),
      PreservesWidePullbacksIn K (regMono (C i)) (updateFunctor x i ⋙ F)) :
    PreservesWidePullbacksIn K (regMono (∀ j, C j)) F ∧
      ∀ ⦃x y : ∀ i, C i⦄ (f : x ⟶ y), IsRegularMono f → IsRegularMono (F.map f) :=
  OpTranslate.preservesWidePullbacks_and_regularMonos_pi_of_op C F hC hF

end UlmerBialgebras.RegMonoWide
