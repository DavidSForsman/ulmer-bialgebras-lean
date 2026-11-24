module

public import UlmerBialgebras.Proofs.Sec2.Sec2
public import UlmerBialgebras.Proofs.Sec3.Sec3

/-!
# Transporting bialgebraic Kan creation to theory objects

Proposition 3.15 identifies the theory object with an equifier for `modelDatum`. We
transport across its object equality and heterogeneous equality of forgetful 1-cells
once. Product preservation then translates the component hypotheses of Corollary 4.11
to the product-valued hypotheses of Corollary 4.8.

## Main results

* `UlmerBialgebras.Paper.ModelKanRoute.LeftCreation`: the left creation assertion of Corollary 4.11,
  for a variable equifier projection.
* `UlmerBialgebras.Paper.ModelKanRoute.RightCreation`: the right creation assertion.
* `UlmerBialgebras.Paper.ModelKanRoute.left_of_bialgebraic`: strict creation from the product-valued
  hypotheses of Corollary 4.8, for an equifier of `modelDatum`, gives `LeftCreation`.
* `UlmerBialgebras.Paper.ModelKanRoute.right_of_bialgebraic`: the same for `RightCreation`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Proposition
  3.15, Corollaries 4.8 and 4.11
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper.ModelKanRoute

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Transport a property of a 1-cell across equality of its source and `HEq` of the 1-cell. -/
lemma transport_hom_property {p p' s : Obj} {e : p ⟶ s} {e' : p' ⟶ s}
    (hp : p = p') (he : HEq e e') (P : ∀ q : Obj, (q ⟶ s) → Prop)
    (h : P p e) : P p' e' := by
  cases hp
  cases eq_of_heq he
  exact h

variable [HasChosenFinProducts.{u, v, w} Obj]
  [HasChosenInserters.{u, v, w} Obj] {Sg : TwoSig.{u₁, u₂, u₃}}
variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
  (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
  {I X : Obj} (k : I ⟶ X)

/-- The left creation assertion of Corollary 4.11, for a variable equifier projection. -/
def LeftCreation (p : Obj) (e : p ⟶ M.sigObj sg) : Prop :=
  ∀ d : I ⟶ p,
    (∀ f : sg.Fn, PreservesLeftKan k (d ≫ (e ≫ M.u sg)) (M.funArity sg f)) →
    (∀ r : T.Eqn, ∀ L : LeftExt k (d ≫ (e ≫ M.u sg)), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k _ (M.eqnArity sg T r)).obj L)) →
    StrictlyCreatesLeftKan k d (e ≫ M.u sg)

/-- The right creation assertion, for a variable equifier projection. -/
def RightCreation (p : Obj) (e : p ⟶ M.sigObj sg) : Prop :=
  ∀ d : I ⟶ p,
    (∀ f : sg.Fn, PreservesRightKan k (d ≫ (e ≫ M.u sg)) (M.funCoarity sg f)) →
    (∀ r : T.Eqn, ∀ R : RightExt k (d ≫ (e ≫ M.u sg)), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k _ (M.eqnCoarity sg T r)).obj R)) →
    StrictlyCreatesRightKan k d (e ≫ M.u sg)

/-- Componentwise support hypotheses imply the product-valued left hypotheses of 4.8. -/
lemma left_of_bialgebraic (E : Equifier (modelDatum M sg T).α (modelDatum M sg T).β)
    (hcreate : ∀ d : I ⟶ E.pt,
      PreservesLeftKan k (d ≫ (E.e ≫ M.u sg)) (M.domCell sg) →
      (∀ L : LeftExt k (d ≫ (E.e ≫ M.u sg)), Nonempty (IsInitial L) →
        QuotientInitial ((LeftExt.push k _
          ((M.Peq sg T).lift (fun r => M.tm sg (T.dom r)))).obj L)) →
      StrictlyCreatesLeftKan k d (E.e ≫ M.u sg)) :
    LeftCreation M sg T k E.pt E.e := by
  intro d hfn heq
  refine hcreate d ?_ ?_
  · exact ((M.Pfn sg).preservesLeftKan_lift_iff k (d ≫ (E.e ≫ M.u sg)) _).2 hfn
  · intro L hL
    exact (M.Peq sg T).quotientInitial_push_lift k (d ≫ (E.e ≫ M.u sg)) _ L
      (fun r => heq r L hL)

/-- Componentwise support hypotheses imply the product-valued right hypotheses of 4.8. -/
lemma right_of_bialgebraic (E : Equifier (modelDatum M sg T).α (modelDatum M sg T).β)
    (hcreate : ∀ d : I ⟶ E.pt,
      PreservesRightKan k (d ≫ (E.e ≫ M.u sg)) (M.codCell sg) →
      (∀ R : RightExt k (d ≫ (E.e ≫ M.u sg)), Nonempty (IsTerminal R) →
        Subterminal ((RightExt.push k _
          ((M.Peq sg T).lift (fun r => M.tm sg (T.cod r)))).obj R)) →
      StrictlyCreatesRightKan k d (E.e ≫ M.u sg)) :
    RightCreation M sg T k E.pt E.e := by
  intro d hfn heq
  refine hcreate d ?_ ?_
  · exact ((M.Pfn sg).preservesRightKan_lift_iff k (d ≫ (E.e ≫ M.u sg)) _).2 hfn
  · intro R hR
    exact (M.Peq sg T).subterminal_push_lift k (d ≫ (E.e ≫ M.u sg)) _ R
      (fun r => heq r R hR)

end UlmerBialgebras.Paper.ModelKanRoute
