module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import UlmerBialgebras.Kan.Kan

/-!
# Relatively algebraic bialgebraic data

Definition 4.9 of Forsman, *A Syntactic Approach to Ulmer's Bialgebras*.

## Main results

* `UlmerBialgebras.Paper.BialgDatum.IsRelativelyAlgebraic`: the function coarity preserves right Kan
  extensions and the equational coarity preserves their subterminality (Definition 4.9).
* `UlmerBialgebras.Paper.BialgDatum.IsRelativelyCoalgebraic`: the dual notion (Definition 4.9).
* `UlmerBialgebras.Paper.Model.IsRelativelyAlgebraic`,
  `UlmerBialgebras.Paper.Model.IsRelativelyCoalgebraic`: the same notions for a theory in a model,
  through its induced datum.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 4.9
-/

@[expose] public section

universe u v w uu₁ uu₂ uu₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- A datum is relatively algebraic when its function coarity preserves right Kan
extensions and its equational coarity preserves their subterminality. -/
def BialgDatum.IsRelativelyAlgebraic (B : BialgDatum (Obj := Obj)) : Prop :=
  (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ B.c), PreservesRightKan k d B.g) ∧
  (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ B.c) (R : RightExt k d),
    Nonempty (IsTerminal R) → Subterminal ((RightExt.push k d B.g').obj R))

/-- Dually, a datum is relatively coalgebraic when its function arity preserves left Kan
extensions and its equational arity preserves their quotient initiality. -/
def BialgDatum.IsRelativelyCoalgebraic (B : BialgDatum (Obj := Obj)) : Prop :=
  (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ B.c), PreservesLeftKan k d B.f) ∧
  (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ B.c) (L : LeftExt k d),
    Nonempty (IsInitial L) → QuotientInitial ((LeftExt.push k d B.f').obj L))

/-- A theory is relatively algebraic in a model when its induced datum is. -/
noncomputable def Model.IsRelativelyAlgebraic [HasChosenFinProducts.{u, v, w} Obj]
    [HasChosenInserters.{u, v, w} Obj]
    {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Obj) (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj] : Prop :=
  (modelDatum M sg T).IsRelativelyAlgebraic

/-- A theory is relatively coalgebraic in a model when its induced datum is. -/
noncomputable def Model.IsRelativelyCoalgebraic [HasChosenFinProducts.{u, v, w} Obj]
    [HasChosenInserters.{u, v, w} Obj]
    {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Obj) (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj] : Prop :=
  (modelDatum M sg T).IsRelativelyCoalgebraic

end UlmerBialgebras.Paper
