module

public import UlmerBialgebras.Proofs.Sec4.Sec4
public import UlmerBialgebras.Paper.Sec4DefsRelativelyAlgebraic

/-!
# Relatively algebraic bialgebraic data (Definition 4.9)

## Main results

* `UlmerBialgebras.Paper.def_4_9_algebraic_datum`: for a relatively algebraic datum, `u_B` strictly
  creates right Kan extensions.
* `UlmerBialgebras.Paper.def_4_9_coalgebraic_datum`: for a relatively coalgebraic datum, `u_B`
  strictly creates left Kan extensions.
* `UlmerBialgebras.Paper.def_4_9_theories`: an algebraic (coalgebraic) theory is relatively
  algebraic (relatively coalgebraic) in any model.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 4.9
-/

@[expose] public section

universe u v w uu₁ uu₂ uu₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Datum
variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Relatively algebraic data have their right Kan extensions strictly created. -/
theorem def_4_9_algebraic_datum (B : BialgDatum (Obj := Obj))
    (h : B.IsRelativelyAlgebraic) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) : StrictlyCreatesRightKan k d (B.uB E) := by
  exact cor_4_8_right B E k d (h.1 k _) (h.2 k _)

/-- Relatively coalgebraic data have their left Kan extensions strictly created. -/
theorem def_4_9_coalgebraic_datum (B : BialgDatum (Obj := Obj))
    (h : B.IsRelativelyCoalgebraic) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) : StrictlyCreatesLeftKan k d (B.uB E) := by
  exact cor_4_8_left B E k d (h.1 k _) (h.2 k _)

end Datum

section Theory
variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  [HasChosenInserters.{u, v, w} Obj]
variable {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Obj) (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
  (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- Every algebraic or coalgebraic theory is relatively so in any model. -/
theorem def_4_9_theories :
    (T.IsAlgebraic → Model.IsRelativelyAlgebraic M sg T) ∧
      (T.IsCoalgebraic → Model.IsRelativelyCoalgebraic M sg T) := by
  constructor
  · intro h
    constructor
    · intro I X k d
      apply ((M.Pfn sg).preservesRightKan_lift_iff k d _).2
      intro i
      exact M.preservesRightKan_tm_of_isVar sg _ (h.1 i) k d
    · intro I X k d R hR
      apply (M.Peq sg T).subterminal_push_lift k d _ R
      intro i
      exact subterminal_of_isTerminal ((M.preservesRightKan_tm_of_isVar sg _ (h.2 i) k d R hR).some)
  · intro h
    constructor
    · intro I X k d
      apply ((M.Pfn sg).preservesLeftKan_lift_iff k d _).2
      intro i
      exact M.preservesLeftKan_tm_of_isVar sg _ (h.1 i) k d
    · intro I X k d L hL
      apply (M.Peq sg T).quotientInitial_push_lift k d _ L
      intro i
      exact quotientInitial_of_isInitial
        ((M.preservesLeftKan_tm_of_isVar sg _ (h.2 i) k d L hL).some)

end Theory
end UlmerBialgebras.Paper
