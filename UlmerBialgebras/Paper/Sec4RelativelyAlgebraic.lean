module

public import UlmerBialgebras.Paper.Sec4
public import UlmerBialgebras.Paper.Sec4DefsRelativelyAlgebraic

/-!
# Relatively algebraic bialgebraic data (Definition 4.9)

## Main results

* `UlmerBialgebras.Paper.def_4_9_algebraic_datum`: for a relatively algebraic datum `B`, `u_B`
  strictly creates right Kan extensions.
* `UlmerBialgebras.Paper.def_4_9_coalgebraic_datum`: for a relatively coalgebraic datum `B`, `u_B`
  strictly creates left Kan extensions.
* `UlmerBialgebras.Paper.def_4_9_theories`: an algebraic (resp. coalgebraic) theory is relatively
  algebraic (resp. relatively coalgebraic) in the model `M`.

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
    (k : I ⟶ X) (d : I ⟶ E.pt) : StrictlyCreatesRightKan k d (B.uB E) := sorry

/-- Relatively coalgebraic data have their left Kan extensions strictly created. -/
theorem def_4_9_coalgebraic_datum (B : BialgDatum (Obj := Obj))
    (h : B.IsRelativelyCoalgebraic) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) : StrictlyCreatesLeftKan k d (B.uB E) := sorry

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
      (T.IsCoalgebraic → Model.IsRelativelyCoalgebraic M sg T) := sorry

end Theory
end UlmerBialgebras.Paper
