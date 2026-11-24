module

public import Mathlib.Data.ZMod.Defs
public import UlmerBialgebras.Examples.MonModel
public import UlmerBialgebras.Models.CatCells

/-!
# Computing `M^σ` and `M^T` for the theory of monoids

For a monoidal category `C`, viewed as a `Σ_Mon`-model `M` in `CAT` (`MonModel.lean`), this
file computes the object of operations `M^σ` and the evaluation of the arrows and paths of
the term graph occurring in the theory of monoids:

* an object of `M^σ` is a triple `(x, m : x ⊗ x ⟶ x, e : 𝟙_ C ⟶ x)` (`UlmerBialgebras.MonEx.ob`,
  `UlmerBialgebras.MonEx.mul`, `UlmerBialgebras.MonEx.one`);
* the arrows `µ`, `u`, `µ□s`, `s□µ`, `s□u`, `u□s`, `α_{s,s,s}`, `ρ_s`, `λ_s` of the term
  graph evaluate at such an object to `m`, `e`, `m ▷ x`, `x ◁ m`, `x ◁ e`, `e ▷ x`, the
  associator and the unitors;
* consequently the defining condition of `M^T` at `(x, m, e)` is exactly the conjunction of
  the three monoid axioms (`UlmerBialgebras.MonEx.mem_thy_iff`).

## Main results

* `UlmerBialgebras.MonEx.ob`, `UlmerBialgebras.MonEx.mul`, `UlmerBialgebras.MonEx.one`: the
  components `(x, m, e)` of an object of `M^σ`.
* `UlmerBialgebras.MonEx.mem_thy_iff`: an object `(x, m, e)` of `M^σ` satisfies the defining
  condition of `M^T` (Definition 3.14) iff `m` is associative and `e` is a two-sided unit for `m`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (1)
-/

@[expose] public section


universe v u

namespace UlmerBialgebras

namespace MonEx

open CategoryTheory MonoidalCategory

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]

/-- The objects of `M^σ`: pointed magmas of `C`. -/
abbrev SigObj (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] : Type (max u v) :=
  ((monModel C).sigObj oneSig : Type (max u v))

/-- The underlying object of a pointed magma. -/
def ob (z : SigObj C) : C := Ins.pt z ()

/-- The multiplication of a pointed magma. -/
def mul (z : SigObj C) : ob z ⊗ ob z ⟶ ob z := Ins.cell z FnSym.mul

/-- The unit of a pointed magma. -/
def one (z : SigObj C) : 𝟙_ C ⟶ ob z := Ins.cell z FnSym.one

/-- The functor symbol `□` is interpreted in `monModel C` by `tensFunctor C`. -/
lemma monModel_fn_tens : ((monModel C).fn FunSym.tens).toFunctor = tensFunctor C := rfl

/-- The inserter's structural cell evaluates to the corresponding operation. -/
@[simp] lemma sigIns_φ_app (z : SigObj C) (f : FnSym) :
    ((monModel C).sigIns oneSig).φ.toNatTrans.app z f = Ins.cell z f := rfl

/-! ## The term 1-cells on objects -/
/-- The term `s` is interpreted at `z` by the underlying object `X`. -/
@[simp] lemma sigTm_obj_sTm (z : SigObj C) : ((monModel C).sigTm oneSig sTm).toFunctor.obj z = ob z
    := rfl

/-- The term `s ⊗ s` is interpreted at `z` by `X ⊗ X`. -/
@[simp] lemma sigTm_obj_tensSS (z : SigObj C) :
    ((monModel C).sigTm oneSig (tens sTm sTm)).toFunctor.obj z = ob z ⊗ ob z := rfl

/-- The term `(s ⊗ s) ⊗ s` is interpreted at `z` by `(X ⊗ X) ⊗ X`. -/
@[simp] lemma sigTm_obj_tensSSS (z : SigObj C) :
    ((monModel C).sigTm oneSig (tens (tens sTm sTm) sTm)).toFunctor.obj z = (ob z ⊗ ob z) ⊗ ob z :=
        rfl

/-- The term `s ⊗ (s ⊗ s)` is interpreted at `z` by `X ⊗ (X ⊗ X)`. -/
@[simp] lemma sigTm_obj_tensS_SS (z : SigObj C) :
    ((monModel C).sigTm oneSig (tens sTm (tens sTm sTm))).toFunctor.obj z = ob z ⊗ (ob z ⊗ ob z) :=
        rfl

/-- The term `s ⊗ I` is interpreted at `z` by `X ⊗ 𝟙_ C`. -/
@[simp] lemma sigTm_obj_tensSI (z : SigObj C) :
    ((monModel C).sigTm oneSig (tens sTm unitT)).toFunctor.obj z = ob z ⊗ 𝟙_ C := rfl

/-- The term `I ⊗ s` is interpreted at `z` by `𝟙_ C ⊗ X`. -/
@[simp] lemma sigTm_obj_tensIS (z : SigObj C) :
    ((monModel C).sigTm oneSig (tens unitT sTm)).toFunctor.obj z = 𝟙_ C ⊗ ob z := rfl

/-- The term `I` is interpreted at `z` by the unit `𝟙_ C`. -/
@[simp] lemma sigTm_obj_unitT (z : SigObj C) :
    ((monModel C).sigTm oneSig unitT).toFunctor.obj z = 𝟙_ C := rfl


/-! ## The arrows of the term graph on objects -/

/-- The arrow of the multiplication symbol is interpreted at `z` by `mul z`. -/
@[simp] lemma arrCell_fn_mul_app (z : SigObj C) :
    ((monModel C).arrCell oneSig (OneSig.Arr.fn (sg := oneSig) FnSym.mul)).toNatTrans.app z = mul z
        := by
  rw [Model.arrCell_fn]
  simp only [sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ Ins.cell z FnSym.mul ≫ 𝟙 _ = _
  simp [mul]

/-- The arrow of the unit symbol is interpreted at `z` by `one z`. -/
@[simp] lemma arrCell_fn_one_app (z : SigObj C) :
    ((monModel C).arrCell oneSig (OneSig.Arr.fn (sg := oneSig) FnSym.one)).toNatTrans.app z = one z
        := by
  rw [Model.arrCell_fn]
  simp only [sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ Ins.cell z FnSym.one ≫ 𝟙 _ = _
  simp [one]

/-- The arrow `µ□s` is interpreted at `z` by `mul z ▷ X`. -/
@[simp] lemma arrCell_mulTensS_app (z : SigObj C) :
    ((monModel C).arrCell oneSig mulTensS).toNatTrans.app z = MonoidalCategory.whiskerRight (mul z)
        (ob z) := by
  rw [mulTensS]
  refine (congrArg (fun α : (monModel C).sigTm oneSig (tens (tens sTm sTm) sTm) ⟶
      (monModel C).sigTm oneSig (tens sTm sTm) => α.toNatTrans.app z)
    (Model.arrCell_app (monModel C) oneSig FunSym.tens 0 _ _ _ _)).trans ?_
  dsimp only [PreModel.appCell]
  rw [Cat.whiskerRight_app]
  change (tensFunctor C).map _ = _
  simp only [tensFunctor, cat_finProd_lift₂_app, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, eqToHom_app, dite_true, cast_eq]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  rw [arrCell_fn_mul_app]
  change (𝟙 (ob z ⊗ ob z) ≫ mul z ≫ 𝟙 (ob z)) ⊗ₘ (𝟙 (ob z) ≫ 𝟙 (ob z) ≫ 𝟙 (ob z)) = _
  simp only [Category.id_comp, Category.comp_id, MonoidalCategory.tensorHom_id]

/-- The arrow `s□µ` is interpreted at `z` by `X ◁ mul z`. -/
@[simp] lemma arrCell_sTensMul_app (z : SigObj C) :
    ((monModel C).arrCell oneSig sTensMul).toNatTrans.app z = MonoidalCategory.whiskerLeft (ob z)
        (mul z) := by
  rw [sTensMul]
  refine (congrArg (fun α : (monModel C).sigTm oneSig (tens sTm (tens sTm sTm)) ⟶
      (monModel C).sigTm oneSig (tens sTm sTm) => α.toNatTrans.app z)
    (Model.arrCell_app (monModel C) oneSig FunSym.tens 1 _ _ _ _)).trans ?_
  dsimp only [PreModel.appCell]
  rw [Cat.whiskerRight_app]
  change (tensFunctor C).map _ = _
  simp only [tensFunctor, cat_finProd_lift₂_app, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, eqToHom_app, dite_true, cast_eq]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [arrCell_fn_mul_app]
  change (𝟙 (ob z) ≫ 𝟙 (ob z) ≫ 𝟙 (ob z)) ⊗ₘ (𝟙 (ob z ⊗ ob z) ≫ mul z ≫ 𝟙 (ob z)) = _
  simp only [Category.id_comp, Category.comp_id, MonoidalCategory.id_tensorHom]

/-- The arrow `s□u` is interpreted at `z` by `X ◁ one z`. -/
@[simp] lemma arrCell_sTensOne_app (z : SigObj C) :
    ((monModel C).arrCell oneSig sTensOne).toNatTrans.app z = MonoidalCategory.whiskerLeft (ob z)
        (one z) := by
  rw [sTensOne]
  refine (congrArg (fun α : (monModel C).sigTm oneSig (tens sTm unitT) ⟶
      (monModel C).sigTm oneSig (tens sTm sTm) => α.toNatTrans.app z)
    (Model.arrCell_app (monModel C) oneSig FunSym.tens 1 _ _ _ _)).trans ?_
  dsimp only [PreModel.appCell]
  rw [Cat.whiskerRight_app]
  change (tensFunctor C).map _ = _
  simp only [tensFunctor, cat_finProd_lift₂_app, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, eqToHom_app, dite_true, cast_eq]
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [arrCell_fn_one_app]
  change (𝟙 (ob z) ≫ 𝟙 (ob z) ≫ 𝟙 (ob z)) ⊗ₘ (𝟙 (𝟙_ C) ≫ one z ≫ 𝟙 (ob z)) = _
  simp only [Category.id_comp, Category.comp_id, MonoidalCategory.id_tensorHom]

/-- The arrow `u□s` is interpreted at `z` by `one z ▷ X`. -/
@[simp] lemma arrCell_oneTensS_app (z : SigObj C) :
    ((monModel C).arrCell oneSig oneTensS).toNatTrans.app z = MonoidalCategory.whiskerRight (one z)
        (ob z) := by
  rw [oneTensS]
  refine (congrArg (fun α : (monModel C).sigTm oneSig (tens unitT sTm) ⟶
      (monModel C).sigTm oneSig (tens sTm sTm) => α.toNatTrans.app z)
    (Model.arrCell_app (monModel C) oneSig FunSym.tens 0 _ _ _ _)).trans ?_
  dsimp only [PreModel.appCell]
  rw [Cat.whiskerRight_app]
  change (tensFunctor C).map _ = _
  simp only [tensFunctor, cat_finProd_lift₂_app, Cat.Hom.toNatTrans_comp,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, eqToHom_app, dite_true, cast_eq]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  rw [arrCell_fn_one_app]
  change (𝟙 (𝟙_ C) ≫ one z ≫ 𝟙 (ob z)) ⊗ₘ (𝟙 (ob z) ≫ 𝟙 (ob z) ≫ 𝟙 (ob z)) = _
  simp only [Category.id_comp, Category.comp_id, MonoidalCategory.tensorHom_id]

/-- The associativity arrow is interpreted at `z` by the associator `α_ X X X`. -/
@[simp] lemma arrCell_assocArr_app (z : SigObj C) :
    ((monModel C).arrCell oneSig assocArr).toNatTrans.app z = (α_ (ob z) (ob z) (ob z)).hom := by
  rw [assocArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    Functor.whiskerLeft_app]
  simp only [Fin.isValue, PreModel.interp_app, Cat.Hom.comp_toFunctor, Functor.comp_obj]
  change 𝟙 _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ (α_ (ob z) (ob z) (ob z)).hom ≫ 𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The right unitor arrow `ρ_s` is interpreted at `z` by the right unitor `ρ_ X`. -/
@[simp] lemma arrCell_runitArr_app (z : SigObj C) :
    ((monModel C).arrCell oneSig runitArr).toNatTrans.app z = (ρ_ (ob z)).hom := by
  rw [runitArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    Functor.whiskerLeft_app]
  simp only [sigTm_obj_sTm, Fin.isValue, subst_var, PreModel.interp_app, Cat.Hom.comp_toFunctor,
    Functor.comp_obj, PreModel.interp_var, cat_finProd_π_obj]
  change 𝟙 _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ (ρ_ (ob z)).hom ≫ 𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The left unitor arrow `λ_s` is interpreted at `z` by the left unitor `λ_ X`. -/
@[simp] lemma arrCell_lunitArr_app (z : SigObj C) :
    ((monModel C).arrCell oneSig lunitArr).toNatTrans.app z = (λ_ (ob z)).hom := by
  rw [lunitArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    Functor.whiskerLeft_app]
  simp only [sigTm_obj_sTm, Fin.isValue, subst_var, PreModel.interp_app, Cat.Hom.comp_toFunctor,
    Functor.comp_obj, PreModel.interp_var, cat_finProd_π_obj]
  change 𝟙 _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ (λ_ (ob z)).hom ≫ 𝟙 _) ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-! ## The defining condition of `M^T` -/

/-- The two paths of an equation of `T_Mon`, evaluated at a pointed magma. -/
lemma lhsCell_app (z : SigObj C) (r : EqnSym) :
    ((monModel C).lhsCell oneSig monTheory).toNatTrans.app z r =
      ((monModel C).pathCell oneSig (monTheory.lhs r)).toNatTrans.app z := by
  rw [Model.lhsCell]
  refine (cat_lift₂_app _ z r).trans ?_
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, eqToHom_app]
  change 𝟙 (((monModel C).sigTm oneSig (monTheory.dom r)).toFunctor.obj z) ≫
    ((monModel C).pathCell oneSig (monTheory.lhs r)).toNatTrans.app z ≫ 𝟙 _ = _
  simp only [Category.id_comp]
  exact Category.comp_id _

/-- The right-hand 2-cell of the theory at `z` and equation `r` is the interpretation of
the path `monTheory.rhs r`. -/
lemma rhsCell_app (z : SigObj C) (r : EqnSym) :
    ((monModel C).rhsCell oneSig monTheory).toNatTrans.app z r =
      ((monModel C).pathCell oneSig (monTheory.rhs r)).toNatTrans.app z := by
  rw [Model.rhsCell]
  refine (cat_lift₂_app _ z r).trans ?_
  simp only [Cat.Hom.toNatTrans_comp, Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, eqToHom_app]
  change 𝟙 (((monModel C).sigTm oneSig (monTheory.dom r)).toFunctor.obj z) ≫
    ((monModel C).pathCell oneSig (monTheory.rhs r)).toNatTrans.app z ≫ 𝟙 _ = _
  simp only [Category.id_comp]
  exact Category.comp_id _

/-- **The defining condition of `M^T`**: a pointed magma of `C` is a `T_Mon`-bialgebra
exactly when it satisfies the three monoid axioms. -/
lemma mem_thy_iff (z : SigObj C) :
    ((monModel C).lhsCell oneSig monTheory).toNatTrans.app z
        = ((monModel C).rhsCell oneSig monTheory).toNatTrans.app z ↔
      ((MonoidalCategory.whiskerRight (mul z) (ob z)) ≫ mul z
          = (α_ (ob z) (ob z) (ob z)).hom ≫ (MonoidalCategory.whiskerLeft (ob z) (mul z)) ≫ mul z ∧
        (MonoidalCategory.whiskerLeft (ob z) (one z)) ≫ mul z = (ρ_ (ob z)).hom ∧
        (MonoidalCategory.whiskerRight (one z) (ob z)) ≫ mul z = (λ_ (ob z)).hom) := by
  -- At each equation `r`, both cells are the interpretations of its two paths, and the arrow
  -- lemmas above compute these to the two sides of a monoid axiom.
  constructor
  · intro h
    replace h (r : EqnSym) : ((monModel C).lhsCell oneSig monTheory).toNatTrans.app z r =
        ((monModel C).rhsCell oneSig monTheory).toNatTrans.app z r := congr($h r)
    refine ⟨?_, ?_, ?_⟩
    · have := h EqnSym.assoc
      rw [lhsCell_app, rhsCell_app] at this
      simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom.toNatTrans_comp,
        NatTrans.comp_app, arrCell_mulTensS_app, arrCell_fn_mul_app, arrCell_assocArr_app,
        arrCell_sTensMul_app, Category.comp_id] at this
      exact this
    · have := h EqnSym.mulOne
      rw [lhsCell_app, rhsCell_app] at this
      simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom.toNatTrans_comp,
        NatTrans.comp_app, arrCell_sTensOne_app, arrCell_fn_mul_app, arrCell_runitArr_app,
        Category.comp_id] at this
      exact this
    · have := h EqnSym.oneMul
      rw [lhsCell_app, rhsCell_app] at this
      simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom.toNatTrans_comp,
        NatTrans.comp_app, arrCell_oneTensS_app, arrCell_fn_mul_app, arrCell_lunitArr_app,
        Category.comp_id] at this
      exact this
  · rintro ⟨h1, h2, h3⟩
    funext (r : EqnSym)
    rw [lhsCell_app, rhsCell_app]
    cases r
    · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom.toNatTrans_comp,
        NatTrans.comp_app, arrCell_mulTensS_app, arrCell_fn_mul_app, arrCell_assocArr_app,
        arrCell_sTensMul_app, Category.comp_id]
      exact h1
    · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom.toNatTrans_comp,
        NatTrans.comp_app, arrCell_sTensOne_app, arrCell_fn_mul_app, arrCell_runitArr_app,
        Category.comp_id]
      exact h2
    · simp only [monTheory, Model.pathCell_cons, Model.pathCell_nil, Cat.Hom.toNatTrans_comp,
        NatTrans.comp_app, arrCell_oneTensS_app, arrCell_fn_mul_app, arrCell_lunitArr_app,
        Category.comp_id]
      exact h3

end MonEx

end UlmerBialgebras
