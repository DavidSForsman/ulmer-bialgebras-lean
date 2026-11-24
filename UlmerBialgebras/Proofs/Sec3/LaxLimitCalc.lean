module

public import UlmerBialgebras.Examples.LaxPathCalc
public import UlmerBialgebras.Paper.Sec3DefsLaxLimit
public import UlmerBialgebras.Models.CatCells
public import UlmerBialgebras.Proofs.Sec3.TwoFunctorOplaxModel

/-!
# Evaluating the canonical paths of the lax-limit theories

The equations of the lax-limit theory `T_Lax` (`UlmerBialgebras.LaxEx.theory`) are built from the
canonical paths `f_t : t → s_c` (`UlmerBialgebras.LaxEx.termPath`). These use the functorial image
`B(p₁, …, pₙ)` of a family of paths (`UlmerBialgebras.OneSig.pathApp`), obtained by changing one
argument at a time. This file evaluates these paths in a model.

## Main results

* `UlmerBialgebras.LaxEx.pathCellAlg_pathApp`: in any model, `B(p₁, …, pₙ)` evaluates
  to the image under the functor symbol (`UlmerBialgebras.PreModel.appCell`) of the evaluations of
  the `pᵢ`.
* `UlmerBialgebras.Paper.LaxLimit.Internal.pathCell_termPath`: hence `f_{B(t₁,…,tₙ)}` evaluates to
  the image of the `f_{tᵢ}` followed by the function symbol `f_B`.
* `UlmerBialgebras.Paper.LaxLimit.Internal.semAt`: for a model in `CAT`, the component of `f_t` at
  an object of `M^σ`, by recursion on `t` (`Internal.pathCell_termPath_app_eq`).
* `UlmerBialgebras.Paper.LaxLimit.Internal.mem_thy_iff_semAt`: the defining condition of `M^{T_Lax}`
  in these terms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 3.14
  and Examples 3.20 (4)
* [R. Street, *Limits indexed by category-valued 2-functors*][streetLimitsIndexedCategoryvalued1976]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Paper.LaxLimit.Internal

open CategoryTheory

/-! ## Paths in an arbitrary model -/

section General

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [PIEComplete.{0, u, v, w} Obj]
variable {Sg : TwoSig}

/-- Path evaluation in a model `M` sends concatenation `p.comp q` to the composite of 2-cells. -/
lemma pathCell_comp (M : Model Sg Obj) (sg : OneSig Sg) {c : Sg.Cat} {t t' t'' : sg.CTrm c}
    (p : sg.Path t t') (q : sg.Path t' t'') :
    M.pathCell sg (p.comp q) = M.pathCell sg p ≫ M.pathCell sg q :=
  by simp only [Model.pathCell_eq_pathCellOf]; exact LaxEx.pathCellAlg_comp M sg _ _ p q

/-- The canonical path `f_s : s → s` of a sort (a variable) evaluates to the identity. -/
lemma pathCell_termPath_var (M : Model Sg Obj) (c : Sg.Cat) :
    M.pathCell (LaxEx.oneSig Sg) (LaxEx.termPath (Trm.var c)) = 𝟙 _ :=
  by rw [Model.pathCell_eq_pathCellOf]; exact LaxEx.pathCellAlg_termPath_var M _ _ c

/-- **The canonical path of `B(t₁, …, tₙ)`** evaluates to the image under `B` of the
canonical paths of the `tᵢ`, followed by the function symbol `f_B`. -/
theorem pathCell_termPath (M : Model Sg Obj) (B : Sg.Fun)
    (ts : ∀ i, (LaxEx.oneSig Sg).CTrm (Sg.art B i)) :
    M.pathCell (LaxEx.oneSig Sg) (LaxEx.termPath (Trm.app B ts)) =
      M.appCell B (fun i => M.pathCell (LaxEx.oneSig Sg) (LaxEx.termPath (ts i))) ≫
        M.arrCell (LaxEx.oneSig Sg) (OneSig.Arr.fn (sg := LaxEx.oneSig Sg) B) :=
  by
    simp only [Model.pathCell_eq_pathCellOf, Model.arrCell_eq_arrCellOf]
    exact LaxEx.pathCellAlg_termPath M _ _ B ts

end General

/-! ## Components in `CAT` -/

section Cat

variable {Sg : TwoSig}

/-- In `CAT`, the component at `z` of the image `M(B)(γ)` is `M(B)` applied to the components
    `(γᵢ)_z`. -/
lemma appCell_app (M : Model Sg Cat.{v, max u v}) (B : Sg.Fun) {x : Cat.{v, max u v}}
    {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) (z : x) :
    (M.appCell B γ).toNatTrans.app z =
      (M.fn B).toFunctor.map (X := fun i => (g i).toFunctor.obj z) (Y := fun i => (g'
          i).toFunctor.obj z)
        (fun i => (γ i).toNatTrans.app z) := by
  have h : ((M.P B).lift₂ (fun i => eqToHom ((M.P B).lift_π g i) ≫ γ i ≫
      eqToHom ((M.P B).lift_π g' i).symm)).toNatTrans.app z = (fun i => (γ i).toNatTrans.app z)
          := by
    funext i
    simp only [cat_finProd_lift_obj, cat_finProd_lift₂_app, Cat.Hom.comp_toFunctor,
      Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj,
      cat_finProd_π_obj, eqToHom_app]
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [PreModel.appCell, Cat.whiskerRight_app]
  exact (M.fn B).toFunctor.congr_map h

/-- In `CAT`, the arrow of the function symbol `f_B` of `σ_Lax` evaluates at `z ∈ M^σ` to the
    structure cell `Ins.cell z B`. -/
lemma arrCell_fn_app (M : Model Sg Cat.{v, max u v}) (B : Sg.Fun)
    (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) :
    (M.arrCell (LaxEx.oneSig Sg) (OneSig.Arr.fn (sg := LaxEx.oneSig Sg) B)).toNatTrans.app z =
      Ins.cell z B := by
  rw [Model.arrCell_fn]
  simp only [id_eq, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerRight_toNatTrans, NatTrans.comp_app, Functor.comp_obj, cat_prod_π_obj, eqToHom_app,
    Functor.whiskerRight_app, cat_prod_π_map]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The component at an object `z` of `M^σ` of the evaluation of the canonical path `f_t`,
by recursion on the term `t`. -/
def semAt (M : Model Sg Cat.{v, max u v}) (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) :
    ∀ {c : Sg.Cat} (t : (LaxEx.oneSig Sg).CTrm c),
      (M.sigTm (LaxEx.oneSig Sg) t).toFunctor.obj z ⟶ Ins.pt z c
  | _, .var _ => 𝟙 _
  | _, .app B ts =>
      (M.fn B).toFunctor.map (X := fun i => (M.sigTm (LaxEx.oneSig Sg) (ts i)).toFunctor.obj z)
          (Y := fun i => (M.sigTm (LaxEx.oneSig Sg) (Trm.var (Sg.art B i))).toFunctor.obj z)
          (fun i => semAt M z (ts i)) ≫
        Ins.cell z B

/-- In `CAT`, the canonical path `f_t` evaluates at `z ∈ M^σ` to `semAt M z t`. -/
lemma pathCell_termPath_app_eq (M : Model Sg Cat.{v, max u v}) {c : Sg.Cat}
    (t : (LaxEx.oneSig Sg).CTrm c) (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) :
    (M.pathCell (LaxEx.oneSig Sg) (LaxEx.termPath t)).toNatTrans.app z = semAt M z t := by
  induction t with
  | var c => rw [pathCell_termPath_var]; rfl
  | app B ts ih =>
    rw [pathCell_termPath]
    rw [Cat.Hom₂.comp_app]
    rw [appCell_app, arrCell_fn_app]
    simp only [semAt, ih]
    rfl

/-- In `CAT`, the `r`-component at `z` of the 2-cell of left-hand sides of `T` is the evaluation
    at `z` of the path `lhs r`. -/
lemma lhsCell_app (M : Model Sg Cat.{v, max u v}) (sg : OneSig Sg) (T : Theory sg)
    (z : (M.sigObj sg : Type (max u v))) (r : T.Eqn) :
    (M.lhsCell sg T).toNatTrans.app z r = (M.pathCell sg (T.lhs r)).toNatTrans.app z := by
  rw [Model.lhsCell, cat_lift₂_app]
  exact NatTrans.congr_app
    (Cat.Hom₂.ext_iff.mp ((Category.id_comp _).trans (Category.comp_id _))) z

/-- In `CAT`, the `r`-component at `z` of the 2-cell of right-hand sides of `T` is the evaluation
    at `z` of the path `rhs r`. -/
lemma rhsCell_app (M : Model Sg Cat.{v, max u v}) (sg : OneSig Sg) (T : Theory sg)
    (z : (M.sigObj sg : Type (max u v))) (r : T.Eqn) :
    (M.rhsCell sg T).toNatTrans.app z r = (M.pathCell sg (T.rhs r)).toNatTrans.app z := by
  rw [Model.rhsCell, cat_lift₂_app]
  exact NatTrans.congr_app
    (Cat.Hom₂.ext_iff.mp ((Category.id_comp _).trans (Category.comp_id _))) z

/-- In `CAT`, the left-hand side of the `T_Lax` equation of `α : t₁ → t₂` evaluates at `z` to
    the component of `α_{s̄}` followed by `semAt M z (t₂(s̄))`. -/
lemma pathCell_lhs_app (M : Model Sg Cat.{v, max u v}) (a : Sg.Tr)
    (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) :
    (M.pathCell (LaxEx.oneSig Sg) ((LaxEx.theory Sg).lhs a)).toNatTrans.app z =
      (M.arrCell (LaxEx.oneSig Sg)
          (OneSig.Arr.tr (sg := LaxEx.oneSig Sg) a (LaxEx.subS Sg a))).toNatTrans.app z ≫
        semAt M z ((Sg.trtgt a).subst (LaxEx.subS Sg a)) := by
  simp only [LaxEx.theory, pathCell_comp, Model.pathCell_cons, Model.pathCell_nil,
    Category.comp_id, Cat.Hom₂.comp_app, pathCell_termPath_app_eq]
  rfl

/-- In `CAT`, the right-hand side of the `T_Lax` equation of `α : t₁ → t₂` evaluates at `z` to
    `semAt M z (t₁(s̄))`. -/
lemma pathCell_rhs_app (M : Model Sg Cat.{v, max u v}) (a : Sg.Tr)
    (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) :
    (M.pathCell (LaxEx.oneSig Sg) ((LaxEx.theory Sg).rhs a)).toNatTrans.app z =
      semAt M z ((Sg.trsrc a).subst (LaxEx.subS Sg a)) :=
  pathCell_termPath_app_eq M ((Sg.trsrc a).subst (LaxEx.subS Sg a)) z

set_option maxHeartbeats 400000 in
-- Elaborating the statement unfolds the chosen products of `catPIEComplete` many times.
/-- **The defining condition of `M^{T_Lax}`**, for a model in `CAT`: for every transformation
symbol `α : t₁ → t₂`, the component of `α_{s̄}` followed by `f_{t₂(s̄)}` is `f_{t₁(s̄)}`. -/
theorem mem_thy_iff_semAt (M : Model Sg Cat.{v, max u v})
    (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) :
    (M.lhsCell (LaxEx.oneSig Sg) (LaxEx.theory Sg)).toNatTrans.app z =
        (M.rhsCell (LaxEx.oneSig Sg) (LaxEx.theory Sg)).toNatTrans.app z ↔
      ∀ a : Sg.Tr,
        (M.arrCell (LaxEx.oneSig Sg)
            (OneSig.Arr.tr (sg := LaxEx.oneSig Sg) a (LaxEx.subS Sg a))).toNatTrans.app z ≫
            semAt M z ((Sg.trtgt a).subst (LaxEx.subS Sg a)) =
          semAt M z ((Sg.trsrc a).subst (LaxEx.subS Sg a)) := by
  refine funext_iff.trans (forall_congr' fun a => ?_)
  rw [lhsCell_app, rhsCell_app]
  exact Iff.of_eq (congrArg₂ _ (pathCell_lhs_app M a z) (pathCell_rhs_app M a z))

end Cat

end UlmerBialgebras.Paper.LaxLimit.Internal
