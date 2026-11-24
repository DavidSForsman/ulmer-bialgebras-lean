module

public import UlmerBialgebras.Kan.KanBialgebra
public import UlmerBialgebras.Kan.CoKan
public import UlmerBialgebras.Kan.KanComp
public import UlmerBialgebras.Kan.KanInserter
public import UlmerBialgebras.Kan.KanEquifier

/-!
# Supports and Kan creation for theory objects

Arity and coarity supports are the interpreted terms occurring in function symbols and
equations. Product projections and product lifts supply the preservation conditions for
interpreted terms.

Corollary 4.11 follows from the common bialgebraic creation result of Corollary 4.8,
applied to the conjugated theory equifier of Proposition 3.15. The checked paper-level
proofs in `UlmerBialgebras/Proofs/Sec4/Sec4.lean` explicitly use that proposition and its
object/1-cell
identifications. The right case uses the dual bialgebraic result in `K^co`.

The algebraic, coalgebraic and term-preservation consequences (Corollary 4.12) reuse this
common proof.

## Main results

* `UlmerBialgebras.Model.funArity`, `UlmerBialgebras.Model.funCoarity`,
  `UlmerBialgebras.Model.eqnArity`, `UlmerBialgebras.Model.eqnCoarity`: the arity and coarity
  supports (Definition 3.16).
* `UlmerBialgebras.Model.thy_strictlyCreates_leftKan`,
  `UlmerBialgebras.Model.thy_strictlyCreates_rightKan`: Corollary 4.11 for the forgetful 1-cell
  `M^T → M₀`.
* `UlmerBialgebras.Model.thy_strictlyCreates_rightKan_of_algebraic`,
  `UlmerBialgebras.Model.thy_strictlyCreates_leftKan_of_coalgebraic`: for an algebraic (coalgebraic)
  theory, the forgetful 1-cell strictly creates all right (left) Kan extensions.
* `UlmerBialgebras.Model.thy_strictlyCreates_leftKan_of_fn`,
  `UlmerBialgebras.Model.thy_strictlyCreates_rightKan_of_fn`: if every `M(B)` preserves left (right)
  Kan extensions along `k`, the forgetful 1-cell strictly creates them (Corollary 4.12 and
  its dual).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Proposition 3.15, Definition 3.16, Corollaries 4.8, 4.11 and 4.12
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras], 3.3 and 3.4
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-! ## Arity and coarity supports -/

/-- Definition 3.16: the **function arity support** `M(t₁)` of a `σ`-function symbol. -/
def funArity (f : sg.Fn) : (M.P0 sg).pt ⟶ M.obj (sg.fnty f) := M.tm sg (sg.fndom f)

/-- Definition 3.16: the **function coarity support** `M(t₂)` of a `σ`-function symbol. -/
def funCoarity (f : sg.Fn) : (M.P0 sg).pt ⟶ M.obj (sg.fnty f) := M.tm sg (sg.fncod f)

/-- Definition 3.16: the **equational arity support** `M(t₁')` of an equation. -/
def eqnArity (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) (r : T.Eqn) :
    (M.P0 sg).pt ⟶ M.obj (T.eqty r) :=
  M.tm sg (T.dom r)

/-- Definition 3.16: the **equational coarity support** `M(t₂')` of an equation. -/
def eqnCoarity (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) (r : T.Eqn) :
    (M.P0 sg).pt ⟶ M.obj (T.eqty r) :=
  M.tm sg (T.cod r)

/-! ## Term 1-cells and Kan extensions -/

/-- The interpretation of an application term `B(args)` is the tuple of the interpretations
of the arguments followed by the interpretation `M.fn B` of the function symbol. -/
@[simp] lemma tm_app {B : Sg.Fun} (args : ∀ i, sg.CTrm (Sg.art B i)) :
    M.tm sg (Trm.app B args) = (M.P B).lift (fun i => M.tm sg (args i)) ≫ M.fn B := rfl

/-- A term which is a sort is interpreted by a product projection, hence preserves all left
Kan extensions. -/
lemma preservesLeftKan_tm_of_isVar {cc : Sg.Cat} (t : sg.CTrm cc) (ht : t.IsVar) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ (M.P0 sg).pt) : PreservesLeftKan k d (M.tm sg t) := by
  cases t with
  | var s => exact Product.preserves_leftKan (M.P0 sg) k d s
  | app B args => exact ht.elim

/-- A term which is a sort is interpreted by a product projection, hence preserves all right
Kan extensions. -/
lemma preservesRightKan_tm_of_isVar {cc : Sg.Cat} (t : sg.CTrm cc) (ht : t.IsVar) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ (M.P0 sg).pt) : PreservesRightKan k d (M.tm sg t) := by
  cases t with
  | var s =>
      exact (Co.preservesLeftKan_iff k d ((M.P0 sg).π s)).1
        ((Co.product (M.P0 sg)).preserves_leftKan (Co.hom k) (Co.hom d) s)
  | app B args => exact ht.elim

/-! ## Kan preservation by interpreted terms -/

/-- Corollary 4.12 (first part): if every functor symbol is interpreted by a 1-cell preserving
left Kan extensions along `k`, then so is every term. -/
theorem tm_preserves_leftKan {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesLeftKan k d (M.fn B))
    {cc : Sg.Cat} (t : sg.CTrm cc) (d : I ⟶ (M.P0 sg).pt) :
    PreservesLeftKan k d (M.tm sg t) := by
  induction t with
  | var s => exact Product.preserves_leftKan (M.P0 sg) k d s
  | app B args ih =>
      rw [tm_app]
      exact preservesLeftKan_comp
        (Product.preservesLeftKan_lift (M.P B) k d _ (fun i => ih i)) (hB B _)

/-- The dual of Corollary 4.12 (first part) for right Kan extensions. -/
theorem tm_preserves_rightKan {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesRightKan k d (M.fn B))
    {cc : Sg.Cat} (t : sg.CTrm cc) (d : I ⟶ (M.P0 sg).pt) :
    PreservesRightKan k d (M.tm sg t) := by
  induction t with
  | var s =>
      exact (Co.preservesLeftKan_iff k d ((M.P0 sg).π s)).1
        ((Co.product (M.P0 sg)).preserves_leftKan (Co.hom k) (Co.hom d) s)
  | app B args ih =>
      rw [tm_app]
      exact preservesRightKan_comp
        (Product.preservesRightKan_lift (M.P B) k d _ (fun i => ih i)) (hB B _)

/-! ## Kan creation for theory objects -/

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]
variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- The equational supports evaluated in `M^σ` are the base supports after `u`. -/
lemma u_lift_tm (h : ∀ r : T.Eqn, sg.CTrm (T.eqty r)) :
    M.u sg ≫ (M.Peq sg T).lift (fun r => M.tm sg (h r)) =
      (M.Peq sg T).lift (fun r => M.sigTm sg (h r)) := by
  rw [(M.Peq sg T).comp_lift]
  exact congrArg _ (funext fun r => (M.sigTm_eq sg (h r)).symm)

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- The forgetful 1-cell `u : M^T → M₀`. -/
abbrev thyForget : M.thyObj sg T ⟶ (M.P0 sg).pt := M.e sg T ≫ M.u sg

/-- The theory equifier expressed with the base supports, as in Proposition 3.15. -/
noncomputable def theoryKanEquifier : Equifier
    (eqToHom (M.u_lift_tm sg T T.dom) ≫ M.lhsCell sg T ≫
      eqToHom (M.u_lift_tm sg T T.cod).symm)
    (eqToHom (M.u_lift_tm sg T T.dom) ≫ M.rhsCell sg T ≫
      eqToHom (M.u_lift_tm sg T T.cod).symm) :=
  Paper.Equifier.conj (M.thyEquif sg T) (M.u_lift_tm sg T T.dom)
    (M.u_lift_tm sg T T.cod).symm

/-- **Corollary 4.11** ([forsman2026syntactic]), left half: the forgetful 1-cell `M^T → M₀`
strictly creates those left Kan extensions which the function arity supports preserve and
whose quotient initiality the equational arity supports preserve. -/
theorem thy_strictlyCreates_leftKan {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T)
    (hfn : ∀ f : sg.Fn, PreservesLeftKan k (d ≫ M.thyForget sg T) (M.funArity sg f))
    (heq : ∀ r : T.Eqn, ∀ L : LeftExt k (d ≫ M.thyForget sg T), Nonempty (Limits.IsInitial L) →
      QuotientInitial ((LeftExt.push k _ (M.eqnArity sg T r)).obj L)) :
    StrictlyCreatesLeftKan k d (M.thyForget sg T) := by
  refine Inserter.strictlyCreates_leftKan_equifier (M.sigIns sg)
    (M.theoryKanEquifier sg T) k d ?_ ?_
  · exact ((M.Pfn sg).preservesLeftKan_lift_iff k (d ≫ M.thyForget sg T) _).2 hfn
  · intro L hL
    exact (M.Peq sg T).quotientInitial_push_lift k (d ≫ M.thyForget sg T) _ L
      (fun r => heq r L hL)

/-- Corollary 4.11, right half: the dual statement for right Kan extensions. -/
theorem thy_strictlyCreates_rightKan {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T)
    (hfn : ∀ f : sg.Fn, PreservesRightKan k (d ≫ M.thyForget sg T) (M.funCoarity sg f))
    (heq : ∀ r : T.Eqn, ∀ L : RightExt k (d ≫ M.thyForget sg T), Nonempty (Limits.IsTerminal L) →
      Subterminal ((RightExt.push k _ (M.eqnCoarity sg T r)).obj L)) :
    StrictlyCreatesRightKan k d (M.thyForget sg T) := by
  refine Inserter.strictlyCreates_rightKan_equifier (M.sigIns sg)
    (M.theoryKanEquifier sg T) k d ?_ ?_
  · exact ((M.Pfn sg).preservesRightKan_lift_iff k (d ≫ M.thyForget sg T) _).2 hfn
  · intro R hR
    exact (M.Peq sg T).subterminal_push_lift k (d ≫ M.thyForget sg T) _ R
      (fun r => heq r R hR)

/-- Consequence of Corollary 4.11 (see the text following it): if `T` is algebraic, the
forgetful 1-cell strictly creates all right Kan extensions. -/
theorem thy_strictlyCreates_rightKan_of_algebraic (halg : T.IsAlgebraic) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesRightKan k d (M.thyForget sg T) := by
  refine M.thy_strictlyCreates_rightKan sg T k d
    (fun f => M.preservesRightKan_tm_of_isVar sg _ (halg.1 f) k _) (fun r L hL => ?_)
  exact subterminal_of_isTerminal
    ((M.preservesRightKan_tm_of_isVar sg _ (halg.2 r) k _ L hL).some)

/-- Consequence of Corollary 4.11 (see the text following it): if `T` is coalgebraic, the
forgetful 1-cell strictly creates all left Kan extensions. -/
theorem thy_strictlyCreates_leftKan_of_coalgebraic (hcoalg : T.IsCoalgebraic) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan k d (M.thyForget sg T) := by
  refine M.thy_strictlyCreates_leftKan sg T k d
    (fun f => M.preservesLeftKan_tm_of_isVar sg _ (hcoalg.1 f) k _) (fun r L hL => ?_)
  exact quotientInitial_of_isInitial
    ((M.preservesLeftKan_tm_of_isVar sg _ (hcoalg.2 r) k _ L hL).some)

/-- Corollary 4.12, second part: if every functor symbol preserves left Kan extensions along
`k`, then the forgetful 1-cell `u : M^T → M₀` strictly creates all left Kan extensions
along `k`. -/
theorem thy_strictlyCreates_leftKan_of_fn {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesLeftKan k d (M.fn B))
    (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan k d (M.thyForget sg T) := by
  refine M.thy_strictlyCreates_leftKan sg T k d
    (fun f => M.tm_preserves_leftKan sg k hB _ _) (fun r L hL => ?_)
  exact quotientInitial_of_isInitial ((M.tm_preserves_leftKan sg k hB _ _ L hL).some)

/-- The dual of Corollary 4.12, second part: if every functor symbol preserves right Kan
extensions along `k`, then the forgetful 1-cell `u : M^T → M₀` strictly creates all right
Kan extensions along `k`. -/
theorem thy_strictlyCreates_rightKan_of_fn {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesRightKan k d (M.fn B))
    (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesRightKan k d (M.thyForget sg T) := by
  refine M.thy_strictlyCreates_rightKan sg T k d
    (fun f => M.tm_preserves_rightKan sg k hB _ _) (fun r L hL => ?_)
  exact subterminal_of_isTerminal ((M.tm_preserves_rightKan sg k hB _ _ L hL).some)

end Model

end UlmerBialgebras
