module

public import UlmerBialgebras.Factorization.RepTerm

/-!
# Whiskering a theory's left-hand-side cell

Reassociation of the left-hand-side cell of a model theory under whiskering.

## Main results

* `UlmerBialgebras.Model.whiskerLeft_lhsCell_eq`: a 1-cell into `M^σ` which equifies the two paths
  of every equation of `T` equifies the two 2-cells defining `M^T`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.7,
  Corollary 6.9
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
  (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- A 1-cell into `M^σ` which equifies the two paths of every equation of `T` equifies the
two 2-cells defining `M^T`. -/
theorem whiskerLeft_lhsCell_eq {x : Obj} (k : x ⟶ M.sigObj sg)
    (h : ∀ r : T.Eqn, k ◁ M.pathCell sg (T.lhs r) = k ◁ M.pathCell sg (T.rhs r)) :
    k ◁ M.lhsCell sg T = k ◁ M.rhsCell sg T := by
  refine (M.Peq sg T).cell_ext (fun r => ?_)
  have h2 : k ◁ (M.lhsCell sg T ▷ (M.Peq sg T).π r)
      = k ◁ (M.rhsCell sg T ▷ (M.Peq sg T).π r) := by
    rw [lhsCell, rhsCell, (M.Peq sg T).lift₂_π, (M.Peq sg T).lift₂_π]
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
    rw [h r]
  rw [Bicategory.Strict.whisker_assoc', Bicategory.Strict.whisker_assoc', h2]

variable {E : Type s₃} (j : E → T.Eqn)

section OFS

variable (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
  (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
  (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f)) (M.funCoarity sg f))
  (heqE : ∀ r : T.Eqn, RepPreservesLeft (M.repOFS0 sg S) (S (T.eqty r)) (M.eqnArity sg T r))
  (heqM : ∀ r : T.Eqn, RepPreservesRight (M.repOFS0 sg S) (S (T.eqty r)) (M.eqnCoarity sg T r))

end OFS

end Model

end UlmerBialgebras
