module

public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import Mathlib.Data.ZMod.Defs
public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import UlmerBialgebras.Models.CatCells
public import UlmerBialgebras.Proofs.Sec3.CategoryIso

/-!
# `M^{T_Hopf}` is the category of Hopf monoids

For a braided monoidal category `C` and its Hopf model `M`
(`UlmerBialgebras.Paper.HopfModel.hopfModel C`), this file computes the object of operations `M^σ`
and the object of bialgebras `M^{T_Hopf}`:

* an object of `M^σ` is an object `x` of `C` with morphisms `µ : x ⊗ x ⟶ x`, `u : 𝟙_ C ⟶ x`,
  `δ : x ⟶ x ⊗ x`, `ε : x ⟶ 𝟙_ C` and `S : x ⟶ x` (`Internal.ob`, `Internal.mul`, …);
* the arrows and paths of the term graph occurring in `T_Hopf` evaluate to the corresponding
  composites of these morphisms with whiskerings, associators, unitors and the interchange
  law `tensorμ` (`Internal.pathCell_leftPath_app`, `Internal.pathCell_tensPath_app`, …);
* consequently the defining condition of `M^{T_Hopf}` is the conjunction of the twelve
  axioms of a Hopf monoid (`Internal.mem_thy_iff`), and the comparison functor
  `M^{T_Hopf} ⥤ Hopf C` has a strict inverse `Internal.inverseFunctor` and commutes with the
  forgetful functors to `C`
  (`Internal.comparison_comp_inverseFunctor`, `Internal.inverseFunctor_comp_comparison`,
  `Internal.comparison_comp_hopfForget`).

## Main results

* `UlmerBialgebras.Paper.HopfModel.Internal.mem_thy_iff`: an object of `M^σ` satisfies the defining
  condition of `M^{T_Hopf}` iff it satisfies `Internal.Axioms`, the axioms of a Hopf monoid.
* `UlmerBialgebras.Paper.HopfModel.Internal.comparison`: the comparison functor
  `M^{T_Hopf} ⥤ Hopf C`.
* `UlmerBialgebras.Paper.HopfModel.Internal.inverseFunctor`: a functor `Hopf C ⥤ M^{T_Hopf}`.
* `UlmerBialgebras.Paper.HopfModel.Internal.comparison_comp_inverseFunctor`:
  `comparison C ⋙ inverseFunctor C = 𝟭 _`; `Internal.inverseFunctor_comp_comparison` is the
  other composite.
* `UlmerBialgebras.Paper.HopfModel.Internal.comparison_comp_hopfForget`: the comparison functor
  commutes with the forgetful functors to `C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 3.13 and 3.14, Examples 3.20 (2)
-/

@[expose] public section


universe v u

namespace UlmerBialgebras.Paper.HopfModel.Internal

open CategoryTheory MonoidalCategory

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-! ## The objects of `M^σ` -/

variable (C) in
/-- The objects of `M^σ` for the Hopf model. -/
abbrev SigObj : Type (max u v) := ((hopfModel C).sigObj HopfEx.oneSig : Type (max u v))

/-- The underlying object of an object of `M^σ`. -/
def ob (z : SigObj C) : C := Ins.pt z ()

/-- The multiplication of an object of `M^σ`. -/
def mul (z : SigObj C) : ob z ⊗ ob z ⟶ ob z := Ins.cell z HopfEx.FnSym.mul

/-- The unit of an object of `M^σ`. -/
def one (z : SigObj C) : 𝟙_ C ⟶ ob z := Ins.cell z HopfEx.FnSym.one

/-- The comultiplication of an object of `M^σ`. -/
def comul (z : SigObj C) : ob z ⟶ ob z ⊗ ob z := Ins.cell z HopfEx.FnSym.comul

/-- The counit of an object of `M^σ`. -/
def counit (z : SigObj C) : ob z ⟶ 𝟙_ C := Ins.cell z HopfEx.FnSym.counit

/-- The antipode of an object of `M^σ`. -/
def antipode (z : SigObj C) : ob z ⟶ ob z := Ins.cell z HopfEx.FnSym.antipode

/-- The Hopf model interprets the functor symbol `□` as the tensor functor `(p₀, p₁) ↦ p₀ ⊗ p₁`. -/
lemma hopfModel_fn_tens : (hopfModel C).fn HopfEx.FunSym.tens = (MonEx.tensFunctor C).toCatHom :=
    rfl

/-! The objects of `C` interpreting the closed terms at an object of `M^σ`. -/
/-- The sort `s` evaluates at `z ∈ M^σ` to the underlying object `ob z`. -/
@[simp] lemma sigTm_obj_sTm (z : SigObj C) :
    ((hopfModel C).sigTm HopfEx.oneSig HopfEx.sTm).toFunctor.obj z = ob z := rfl

/-- The term `a □ b` evaluates at `z ∈ M^σ` to the tensor product of the values of `a`, `b`. -/
@[simp] lemma sigTm_obj_tn (z : SigObj C) (a b : HopfEx.CTm) :
    ((hopfModel C).sigTm HopfEx.oneSig (HopfEx.tn a b)).toFunctor.obj z =
      MonoidalCategory.tensorObj (C := C) (((hopfModel C).sigTm HopfEx.oneSig a).toFunctor.obj z)
        (((hopfModel C).sigTm HopfEx.oneSig b).toFunctor.obj z) := rfl

/-- The term `I` evaluates at `z ∈ M^σ` to the unit object `𝟙_ C`. -/
@[simp] lemma sigTm_obj_un (z : SigObj C) :
    ((hopfModel C).sigTm HopfEx.oneSig (HopfEx.un : HopfEx.CTm)).toFunctor.obj z = 𝟙_ C := rfl

/-- The model's transformation cells are `hopfCell`. -/
@[simp] lemma hopfModel_tr (a : HopfEx.TrSym) : (hopfModel C).tr a = hopfCell C a := rfl

/-- The structure map of `z ∈ M^σ` at a function symbol `f` is the cell `Ins.cell z f`. -/
@[simp] lemma sigIns_φ_app (z : SigObj C) (f : HopfEx.FnSym) :
    ((hopfModel C).sigIns HopfEx.oneSig).φ.toNatTrans.app z f = Ins.cell z f := rfl


/-! ## The arrows of the term graph -/

/-- The arrow of the function symbol `µ` evaluates at `z ∈ M^σ` to `mul z`. -/
@[simp] lemma arrCell_fnArr_mul_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.fnArr HopfEx.FnSym.mul)).toNatTrans.app z = mul z
        := by
  rw [HopfEx.fnArr, Model.arrCell_fn]
  simp only [mul, sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ z.cell HopfEx.FnSym.mul ≫ 𝟙 _ = _
  simp

/-- The arrow of the function symbol `u` evaluates at `z ∈ M^σ` to `one z`. -/
@[simp] lemma arrCell_fnArr_one_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.fnArr HopfEx.FnSym.one)).toNatTrans.app z = one z
        := by
  rw [HopfEx.fnArr, Model.arrCell_fn]
  simp only [one, sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ z.cell HopfEx.FnSym.one ≫ 𝟙 _ = _
  simp

/-- The arrow of the function symbol `δ` evaluates at `z ∈ M^σ` to `comul z`. -/
@[simp] lemma arrCell_fnArr_comul_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.fnArr HopfEx.FnSym.comul)).toNatTrans.app z =
      comul z := by
  rw [HopfEx.fnArr, Model.arrCell_fn]
  simp only [comul, sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ z.cell HopfEx.FnSym.comul ≫ 𝟙 _ = _
  simp

/-- The arrow of the function symbol `ε` evaluates at `z ∈ M^σ` to `counit z`. -/
@[simp] lemma arrCell_fnArr_counit_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.fnArr HopfEx.FnSym.counit)).toNatTrans.app z =
      counit z := by
  rw [HopfEx.fnArr, Model.arrCell_fn]
  simp only [counit, sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ z.cell HopfEx.FnSym.counit ≫ 𝟙 _ = _
  simp

/-- The arrow of the function symbol `S` evaluates at `z ∈ M^σ` to `antipode z`. -/
@[simp] lemma arrCell_fnArr_antipode_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.fnArr HopfEx.FnSym.antipode)).toNatTrans.app z =
      antipode z := by
  rw [HopfEx.fnArr, Model.arrCell_fn]
  simp only [antipode, sigTm_obj_sTm, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerRight_toNatTrans, NatTrans.comp_app,
    Functor.comp_obj, cat_prod_π_obj, eqToHom_app, Functor.whiskerRight_app, cat_prod_π_map,
    sigIns_φ_app]
  change 𝟙 _ ≫ z.cell HopfEx.FnSym.antipode ≫ 𝟙 _ = _
  simp

/-- The arrow `g □ b` evaluates to `g ▷ b`. -/
@[simp] lemma arrCell_leftArr_app {a a' : HopfEx.CTm} (b : HopfEx.CTm)
    (g : HopfEx.oneSig.Arr a a') (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.leftArr b g)).toNatTrans.app z =
      MonoidalCategory.whiskerRight (C := C) (((hopfModel C).arrCell HopfEx.oneSig
          g).toNatTrans.app z)
        (((hopfModel C).sigTm HopfEx.oneSig b).toFunctor.obj z) := by
  have h := (hopfModel C).arrCell_app HopfEx.oneSig HopfEx.FunSym.tens 0
    ![a, b] ![a', b] (fun j hj => by fin_cases j <;> simp_all) g
  refine (congrArg (fun η => η.toNatTrans.app z) h).trans ?_
  let f : (show C from ((hopfModel C).sigTm HopfEx.oneSig a).toFunctor.obj z) ⟶
      (show C from ((hopfModel C).sigTm HopfEx.oneSig a').toFunctor.obj z) :=
    ((hopfModel C).arrCell HopfEx.oneSig g).toNatTrans.app z
  let Y : C := ((hopfModel C).sigTm HopfEx.oneSig b).toFunctor.obj z
  change ((𝟙 _ ≫ f ≫ 𝟙 _) ⊗ₘ (𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y)) = f ▷ Y
  simp only [Category.id_comp, Category.comp_id, tensorHom_id]

/-- The arrow `a □ g` evaluates to `a ◁ g`. -/
@[simp] lemma arrCell_rightArr_app (a : HopfEx.CTm) {b b' : HopfEx.CTm}
    (g : HopfEx.oneSig.Arr b b') (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.rightArr a g)).toNatTrans.app z =
      MonoidalCategory.whiskerLeft (C := C) (((hopfModel C).sigTm HopfEx.oneSig a).toFunctor.obj z)
        (((hopfModel C).arrCell HopfEx.oneSig g).toNatTrans.app z) := by
  have h := (hopfModel C).arrCell_app HopfEx.oneSig HopfEx.FunSym.tens 1
    ![a, b] ![a, b'] (fun j hj => by fin_cases j <;> simp_all) g
  refine (congrArg (fun η => η.toNatTrans.app z) h).trans ?_
  let f : (show C from ((hopfModel C).sigTm HopfEx.oneSig b).toFunctor.obj z) ⟶
      (show C from ((hopfModel C).sigTm HopfEx.oneSig b').toFunctor.obj z) :=
    ((hopfModel C).arrCell HopfEx.oneSig g).toNatTrans.app z
  let X : C := ((hopfModel C).sigTm HopfEx.oneSig a).toFunctor.obj z
  change ((𝟙 X ≫ 𝟙 X ≫ 𝟙 X) ⊗ₘ (𝟙 _ ≫ f ≫ 𝟙 _)) = X ◁ f
  simp only [Category.id_comp, Category.comp_id, id_tensorHom]

/-- The associativity arrow `(s □ s) □ s → s □ (s □ s)` evaluates to the associator `α_`. -/
@[simp] lemma arrCell_assocArr_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig
        (HopfEx.assocArr HopfEx.sTm HopfEx.sTm HopfEx.sTm)).toNatTrans.app z =
      (α_ (ob z) (ob z) (ob z)).hom := by
  rw [HopfEx.assocArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [hopfModel, hopfCell, MonEx.ev, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    PreModel.interp_app,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp,
    Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans, Cat.whiskerLeft_toNatTrans,
    NatTrans.comp_app, Functor.comp_obj, eqToHom_app, Functor.whiskerLeft_app]
  change 𝟙 _ ≫ (α_ (ob z) (ob z) (ob z)).hom ≫ 𝟙 _ = _
  simp

/-- A left unit arrow evaluates to the left unitor of the evaluated term. -/
lemma arrCell_lunitArr_app (t : HopfEx.CTm) (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.lunitArr t)).toNatTrans.app z =
      (λ_ (show C from ((hopfModel C).sigTm HopfEx.oneSig t).toFunctor.obj z)).hom := by
  rw [HopfEx.lunitArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Cat.Hom₂.comp_app,
    Cat.eqToHom_app, Cat.whiskerLeft_app]
  let X : C := ((hopfModel C).sigTm HopfEx.oneSig t).toFunctor.obj z
  change 𝟙 _ ≫ (λ_ X).hom ≫ 𝟙 _ = (λ_ X).hom
  simp only [Category.id_comp, Category.comp_id]

/-- The left unit arrow `I □ s → s` evaluates to the left unitor `λ_ (ob z)`. -/
@[simp] lemma arrCell_lunitArr_sTm_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.lunitArr HopfEx.sTm)).toNatTrans.app z =
      (λ_ (ob z)).hom :=
  arrCell_lunitArr_app HopfEx.sTm z

/-- The left unit arrow `I □ I → I` evaluates to the left unitor `λ_ (𝟙_ C)`. -/
@[simp] lemma arrCell_lunitArr_un_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.lunitArr HopfEx.un)).toNatTrans.app z =
      (λ_ (𝟙_ C)).hom :=
  arrCell_lunitArr_app HopfEx.un z

/-- A right unit arrow evaluates to the inverse right unitor of the evaluated term. -/
lemma arrCell_runitArr_app (t : HopfEx.CTm) (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.runitArr t)).toNatTrans.app z =
      (ρ_ (show C from ((hopfModel C).sigTm HopfEx.oneSig t).toFunctor.obj z)).inv := by
  rw [HopfEx.runitArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Cat.Hom₂.comp_app,
    Cat.eqToHom_app, Cat.whiskerLeft_app]
  let X : C := ((hopfModel C).sigTm HopfEx.oneSig t).toFunctor.obj z
  change 𝟙 _ ≫ (ρ_ X).inv ≫ 𝟙 _ = (ρ_ X).inv
  simp only [Category.id_comp, Category.comp_id]

/-- The right unit arrow `s → s □ I` evaluates to the inverse right unitor `(ρ_ (ob z)).inv`. -/
@[simp] lemma arrCell_runitArr_sTm_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.runitArr HopfEx.sTm)).toNatTrans.app z =
      (ρ_ (ob z)).inv :=
  arrCell_runitArr_app HopfEx.sTm z

/-- The right unit arrow `I → I □ I` evaluates to `(ρ_ (𝟙_ C)).inv`. -/
@[simp] lemma arrCell_runitArr_un_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig (HopfEx.runitArr HopfEx.un)).toNatTrans.app z =
      (ρ_ (𝟙_ C)).inv :=
  arrCell_runitArr_app HopfEx.un z

/-- The interchange arrow `(s □ s) □ (s □ s) → (s □ s) □ (s □ s)` evaluates to `tensorμ`. -/
@[simp] lemma arrCell_chiArr_app (z : SigObj C) :
    ((hopfModel C).arrCell HopfEx.oneSig
        (HopfEx.chiArr HopfEx.sTm HopfEx.sTm HopfEx.sTm HopfEx.sTm)).toNatTrans.app z =
      tensorμ (ob z) (ob z) (ob z) (ob z) := by
  rw [HopfEx.chiArr, Model.arrCell_transport, Model.arrCell_tr, Model.trAt]
  simp only [hopfModel, hopfCell, MonEx.ev, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    PreModel.interp_app, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    Functor.whiskerLeft_app]
  change 𝟙 _ ≫ tensorμ (ob z) (ob z) (ob z) (ob z) ≫ 𝟙 _ = _
  simp

/-! ## The paths of the term graph -/

/-- Path evaluation sends concatenation of paths to vertical composition of 2-cells. -/
@[simp] lemma pathCell_comp {t t' t'' : HopfEx.CTm} (p : HopfEx.oneSig.Path t t')
    (q : HopfEx.oneSig.Path t' t'') :
    (hopfModel C).pathCell HopfEx.oneSig (p.comp q) =
      (hopfModel C).pathCell HopfEx.oneSig p ≫ (hopfModel C).pathCell HopfEx.oneSig q := by
  induction p with
  | nil t => simp [OneSig.Path.comp]
  | cons g p ih => simp [OneSig.Path.comp, ih]

/-- A one-arrow path evaluates to the 2-cell of that arrow. -/
@[simp] lemma pathCell_arrPath {t t' : HopfEx.CTm} (g : HopfEx.oneSig.Arr t t') :
    (hopfModel C).pathCell HopfEx.oneSig (HopfEx.arrPath g) =
      (hopfModel C).arrCell HopfEx.oneSig g := by
  simp [HopfEx.arrPath]

/-- The path `µ` evaluates at `z ∈ M^σ` to `mul z`. -/
@[simp] lemma pathCell_mulP_app (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig HopfEx.mulP).toNatTrans.app z = mul z := by
  simpa only [HopfEx.mulP, pathCell_arrPath] using arrCell_fnArr_mul_app (C := C) z

/-- The path `u` evaluates at `z ∈ M^σ` to `one z`. -/
@[simp] lemma pathCell_oneP_app (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig HopfEx.oneP).toNatTrans.app z = one z := by
  simpa only [HopfEx.oneP, pathCell_arrPath] using arrCell_fnArr_one_app (C := C) z

/-- The path `δ` evaluates at `z ∈ M^σ` to `comul z`. -/
@[simp] lemma pathCell_comulP_app (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig HopfEx.comulP).toNatTrans.app z = comul z := by
  simpa only [HopfEx.comulP, pathCell_arrPath] using arrCell_fnArr_comul_app (C := C) z

/-- The path `ε` evaluates at `z ∈ M^σ` to `counit z`. -/
@[simp] lemma pathCell_counitP_app (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig HopfEx.counitP).toNatTrans.app z = counit z := by
  simpa only [HopfEx.counitP, pathCell_arrPath] using arrCell_fnArr_counit_app (C := C) z

/-- The path `S` evaluates at `z ∈ M^σ` to `antipode z`. -/
@[simp] lemma pathCell_antipodeP_app (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig HopfEx.antipodeP).toNatTrans.app z = antipode z := by
  simp [HopfEx.antipodeP]

/-- The path `p □ b` evaluates to `p ▷ b`. -/
@[simp] lemma pathCell_leftPath_app (b : HopfEx.CTm) {a t : HopfEx.CTm}
    (p : HopfEx.oneSig.Path a t) (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.leftPath b p)).toNatTrans.app z =
      MonoidalCategory.whiskerRight (C := C) (((hopfModel C).pathCell HopfEx.oneSig
          p).toNatTrans.app z)
        (((hopfModel C).sigTm HopfEx.oneSig b).toFunctor.obj z) := by
  induction p with
  | nil t => simp [HopfEx.leftPath]; rfl
  | cons g p ih => simp [HopfEx.leftPath, ih]; rfl

/-- The path `a □ p` evaluates to `a ◁ p`. -/
@[simp] lemma pathCell_rightPath_app (a : HopfEx.CTm) {b t : HopfEx.CTm}
    (p : HopfEx.oneSig.Path b t) (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.rightPath a p)).toNatTrans.app z =
      MonoidalCategory.whiskerLeft (C := C) (((hopfModel C).sigTm HopfEx.oneSig a).toFunctor.obj z)
        (((hopfModel C).pathCell HopfEx.oneSig p).toNatTrans.app z) := by
  induction p with
  | nil t => simp [HopfEx.rightPath]; rfl
  | cons g p ih => simp [HopfEx.rightPath, ih]; rfl

/-- The path `p □ q` evaluates to `(p ▷ b) ≫ (a' ◁ q)`. -/
@[simp] lemma pathCell_tensPath_app {a a' b b' : HopfEx.CTm} (p : HopfEx.oneSig.Path a a')
    (q : HopfEx.oneSig.Path b b') (z : SigObj C) :
    ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.tensPath p q)).toNatTrans.app z =
      MonoidalCategory.whiskerRight (C := C) (((hopfModel C).pathCell HopfEx.oneSig
          p).toNatTrans.app z)
          (((hopfModel C).sigTm HopfEx.oneSig b).toFunctor.obj z) ≫
        MonoidalCategory.whiskerLeft (C := C) (((hopfModel C).sigTm HopfEx.oneSig a').toFunctor.obj
            z)
          (((hopfModel C).pathCell HopfEx.oneSig q).toNatTrans.app z) := by
  simp [HopfEx.tensPath]; rfl

/-! ## The defining condition of `M^T` -/

/-- The `r`-component at `z` of the 2-cell of left-hand sides of `T_Hopf` is the evaluation
    at `z` of the path `lhs r`. -/
lemma lhsCell_app (z : SigObj C) (r : HopfEx.EqnSym) :
    ((hopfModel C).lhsCell HopfEx.oneSig HopfEx.theory).toNatTrans.app z r =
      ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.theory.lhs r)).toNatTrans.app z := by
  let p := ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.theory.lhs r)).toNatTrans.app z
  change 𝟙 _ ≫ p ≫ 𝟙 _ = p
  simp only [Category.id_comp, Category.comp_id]

/-- The `r`-component at `z` of the 2-cell of right-hand sides of `T_Hopf` is the evaluation
    at `z` of the path `rhs r`. -/
lemma rhsCell_app (z : SigObj C) (r : HopfEx.EqnSym) :
    ((hopfModel C).rhsCell HopfEx.oneSig HopfEx.theory).toNatTrans.app z r =
      ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.theory.rhs r)).toNatTrans.app z := by
  let p := ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.theory.rhs r)).toNatTrans.app z
  change 𝟙 _ ≫ p ≫ 𝟙 _ = p
  simp only [Category.id_comp, Category.comp_id]

/-- The twelve equations of `T_Hopf`, evaluated at an object of `M^σ`: the axioms of a
Hopf monoid. -/
structure Axioms (z : SigObj C) : Prop where
  mul_assoc : MonoidalCategory.whiskerRight (mul z) (ob z) ≫ mul z =
    (α_ (ob z) (ob z) (ob z)).hom ≫ MonoidalCategory.whiskerLeft (ob z) (mul z) ≫ mul z
  one_mul : MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z = (λ_ (ob z)).hom
  mul_one :
    (ρ_ (ob z)).inv ≫ MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z = 𝟙 (ob z)
  comul_assoc : comul z ≫ MonoidalCategory.whiskerRight (comul z) (ob z) ≫
      (α_ (ob z) (ob z) (ob z)).hom = comul z ≫ MonoidalCategory.whiskerLeft (ob z) (comul z)
  counit_comul :
    comul z ≫ MonoidalCategory.whiskerRight (counit z) (ob z) ≫ (λ_ (ob z)).hom = 𝟙 (ob z)
  comul_counit : comul z ≫ MonoidalCategory.whiskerLeft (ob z) (counit z) = (ρ_ (ob z)).inv
  bialg : MonoidalCategory.whiskerRight (comul z) (ob z) ≫
      MonoidalCategory.whiskerLeft (ob z ⊗ ob z) (comul z) ≫
      tensorμ (ob z) (ob z) (ob z) (ob z) ≫
      MonoidalCategory.whiskerRight (mul z) (ob z ⊗ ob z) ≫
      MonoidalCategory.whiskerLeft (ob z) (mul z) = mul z ≫ comul z
  counit_mul : MonoidalCategory.whiskerRight (counit z) (ob z) ≫
      MonoidalCategory.whiskerLeft (𝟙_ C) (counit z) ≫ (λ_ (𝟙_ C)).hom = mul z ≫ counit z
  one_comul : (ρ_ (𝟙_ C)).inv ≫ MonoidalCategory.whiskerRight (one z) (𝟙_ C) ≫
      MonoidalCategory.whiskerLeft (ob z) (one z) = one z ≫ comul z
  one_counit : one z ≫ counit z = 𝟙 (𝟙_ C)
  antipode_right :
    comul z ≫ MonoidalCategory.whiskerLeft (ob z) (antipode z) ≫ mul z = counit z ≫ one z
  antipode_left :
    comul z ≫ MonoidalCategory.whiskerRight (antipode z) (ob z) ≫ mul z = counit z ≫ one z

/-- **The defining condition of `M^{T_Hopf}`**: an object of `M^σ` is a `T_Hopf`-bialgebra
exactly when it satisfies the axioms of a Hopf monoid.

The two sides of each equation are evaluated by the lemmas above; the objects of `C` that
occur are then those of `Axioms` up to definitional equality. -/
lemma mem_thy_iff (z : SigObj C) :
    ((hopfModel C).lhsCell HopfEx.oneSig HopfEx.theory).toNatTrans.app z =
        ((hopfModel C).rhsCell HopfEx.oneSig HopfEx.theory).toNatTrans.app z ↔ Axioms z := by
  constructor
  · intro h
    have e : ∀ r : HopfEx.EqnSym,
        ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.theory.lhs r)).toNatTrans.app z =
          ((hopfModel C).pathCell HopfEx.oneSig (HopfEx.theory.rhs r)).toNatTrans.app z := by
      intro r
      exact (lhsCell_app z r).symm.trans ((congrFun h r).trans (rhsCell_app z r))
    have e₁ := e HopfEx.EqnSym.assoc
    have e₂ := e HopfEx.EqnSym.lunit
    have e₃ := e HopfEx.EqnSym.runit
    have e₄ := e HopfEx.EqnSym.coassoc
    have e₅ := e HopfEx.EqnSym.lcounit
    have e₆ := e HopfEx.EqnSym.rcounit
    have e₇ := e HopfEx.EqnSym.bialg
    have e₈ := e HopfEx.EqnSym.counitMul
    have e₉ := e HopfEx.EqnSym.unitComul
    have e₁₀ := e HopfEx.EqnSym.counitUnit
    have e₁₁ := e HopfEx.EqnSym.antipodeLeft
    have e₁₂ := e HopfEx.EqnSym.antipodeRight
    simp only [HopfEx.theory, pathCell_comp, Cat.Hom₂.comp_app, Cat.Hom₂.id_app,
      Model.pathCell_nil, pathCell_arrPath, pathCell_leftPath_app,
      pathCell_rightPath_app, pathCell_tensPath_app, pathCell_mulP_app, pathCell_oneP_app,
      pathCell_comulP_app, pathCell_counitP_app, pathCell_antipodeP_app, arrCell_assocArr_app,
      arrCell_lunitArr_sTm_app, arrCell_runitArr_sTm_app, arrCell_chiArr_app, sigTm_obj_sTm]
      at e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂
    rw [arrCell_lunitArr_un_app] at e₈
    rw [arrCell_runitArr_un_app] at e₉
    exact ⟨e₁, e₂, e₃, e₄, e₅, e₆, (Category.assoc _ _ _).symm.trans e₇,
      (Category.assoc _ _ _).symm.trans e₈, e₉, e₁₀, e₁₁, e₁₂⟩
  · intro ax
    refine funext fun r => (lhsCell_app z r).trans (Eq.trans ?_ (rhsCell_app z r).symm)
    cases r <;> simp only [HopfEx.theory, pathCell_comp, Cat.Hom₂.comp_app, Cat.Hom₂.id_app,
      Model.pathCell_nil, pathCell_arrPath, pathCell_leftPath_app,
      pathCell_rightPath_app, pathCell_tensPath_app, pathCell_mulP_app, pathCell_oneP_app,
      pathCell_comulP_app, pathCell_counitP_app, pathCell_antipodeP_app, arrCell_assocArr_app,
      arrCell_lunitArr_sTm_app, arrCell_runitArr_sTm_app, arrCell_chiArr_app, sigTm_obj_sTm]
    · exact ax.mul_assoc
    · exact ax.one_mul
    · exact ax.mul_one
    · exact ax.comul_assoc
    · exact ax.counit_comul
    · exact ax.comul_counit
    · exact (Category.assoc _ _ _).trans ax.bialg
    · rw [arrCell_lunitArr_un_app]
      exact (Category.assoc _ _ _).trans ax.counit_mul
    · rw [arrCell_runitArr_un_app]
      exact ax.one_comul
    · exact ax.one_counit
    · exact ax.antipode_right
    · exact ax.antipode_left

/-! ## Morphisms of `M^σ` -/

/-- The underlying morphism of `C` of a morphism of `M^σ`. -/
def bs {z z' : SigObj C} (f : z ⟶ z') : ob z ⟶ ob z' := f.base ()

/-- `bs` sends identities of `M^σ` to identities of `C`. -/
@[simp] lemma bs_id (z : SigObj C) : bs (𝟙 z) = 𝟙 (ob z) := rfl

/-- `bs` sends composites of `M^σ` to composites of `C`. -/
@[simp] lemma bs_comp {z z' z'' : SigObj C} (f : z ⟶ z') (g : z' ⟶ z'') :
    bs (f ≫ g) = bs f ≫ bs g := rfl

/-- A morphism of `M^σ` is determined by its underlying morphism of `C`. -/
lemma bs_injective {z z' : SigObj C} {f g : z ⟶ z'} (h : bs f = bs g) : f = g := by
  apply Ins.hom_ext
  funext s
  cases s
  exact h

/-- The underlying morphism of a morphism of `M^σ` commutes with the multiplications. -/
lemma bs_mul {z z' : SigObj C} (f : z ⟶ z') : mul z ≫ bs f = (bs f ⊗ₘ bs f) ≫ mul z' :=
  congrFun f.w HopfEx.FnSym.mul

/-- The underlying morphism of a morphism of `M^σ` commutes with the units. -/
lemma bs_one {z z' : SigObj C} (f : z ⟶ z') : one z ≫ bs f = one z' := by
  have h : one z ≫ bs f = 𝟙 (𝟙_ C) ≫ one z' := congrFun f.w HopfEx.FnSym.one
  simpa using h

/-- The underlying morphism of a morphism of `M^σ` commutes with the comultiplications. -/
lemma bs_comul {z z' : SigObj C} (f : z ⟶ z') : bs f ≫ comul z' = comul z ≫ (bs f ⊗ₘ bs f) :=
  (congrFun f.w HopfEx.FnSym.comul).symm

/-- The underlying morphism of a morphism of `M^σ` commutes with the counits. -/
lemma bs_counit {z z' : SigObj C} (f : z ⟶ z') : bs f ≫ counit z' = counit z := by
  have h : counit z ≫ 𝟙 (𝟙_ C) = bs f ≫ counit z' := congrFun f.w HopfEx.FnSym.counit
  simpa using h.symm

/-- A morphism of `M^σ`, built from a morphism of `C` compatible with the five operations. -/
def sigHomMk {z z' : SigObj C} (g : ob z ⟶ ob z')
    (hm : mul z ≫ g = (g ⊗ₘ g) ≫ mul z') (he : one z ≫ g = one z')
    (hc : g ≫ comul z' = comul z ≫ (g ⊗ₘ g)) (hu : g ≫ counit z' = counit z)
    (hs : antipode z ≫ g = g ≫ antipode z') : z ⟶ z' where
  base := fun _ => g
  w := by
    funext f
    cases f
    · exact hm
    · exact he.trans (Category.id_comp _).symm
    · exact hc.symm
    · exact (Category.comp_id _).trans hu.symm
    · exact hs

/-- The underlying morphism of `sigHomMk g …` is `g`. -/
@[simp] lemma bs_sigHomMk {z z' : SigObj C} (g : ob z ⟶ ob z')
    (hm : mul z ≫ g = (g ⊗ₘ g) ≫ mul z') (he : one z ≫ g = one z')
    (hc : g ≫ comul z' = comul z ≫ (g ⊗ₘ g)) (hu : g ≫ counit z' = counit z)
    (hs : antipode z ≫ g = g ≫ antipode z') : bs (sigHomMk g hm he hc hu hs) = g := rfl

/-! ## The objects of `M^T` are Hopf monoids -/

/-- An object of `M^{T_Hopf}` satisfies the twelve Hopf monoid axioms `Axioms`. -/
lemma thy_axioms (t : ThyObj C) : Axioms t.obj := (mem_thy_iff t.obj).1 t.property

/-- The monoid structure of a `T_Hopf`-bialgebra. -/
instance monObj (t : ThyObj C) : MonObj (ob t.obj) where
  one := one t.obj
  mul := mul t.obj
  one_mul := (thy_axioms t).one_mul
  mul_one := by
    have h := (thy_axioms t).mul_one
    rw [Iso.inv_comp_eq, Category.comp_id] at h
    exact h
  mul_assoc := (thy_axioms t).mul_assoc

/-- The comonoid structure of a `T_Hopf`-bialgebra. -/
instance comonObj (t : ThyObj C) : ComonObj (ob t.obj) where
  counit := counit t.obj
  comul := comul t.obj
  counit_comul := by
    have h := (thy_axioms t).counit_comul
    rw [← Category.assoc] at h
    exact (Iso.comp_hom_eq_id _).1 h
  comul_counit := (thy_axioms t).comul_counit
  comul_assoc := (thy_axioms t).comul_assoc.symm

/-- The bimonoid structure of a `T_Hopf`-bialgebra. -/
instance bimonObj (t : ThyObj C) : BimonObj (ob t.obj) where
  toMonObj := monObj t
  toComonObj := comonObj t
  mul_comul := by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Category.assoc]
    exact (thy_axioms t).bialg.symm
  one_comul := by
    have h : one t.obj ≫ comul t.obj = (λ_ (𝟙_ C)).inv ≫ (one t.obj ⊗ₘ one t.obj) := by
      rw [MonoidalCategory.tensorHom_def, MonoidalCategory.unitors_inv_equal]
      exact (thy_axioms t).one_comul.symm
    exact h
  mul_counit := by
    rw [Comon.tensorObj_counit, MonoidalCategory.tensorHom_def, Category.assoc]
    exact (thy_axioms t).counit_mul.symm
  one_counit := (thy_axioms t).one_counit

/-- The Hopf monoid structure of a `T_Hopf`-bialgebra. -/
instance hopfObj (t : ThyObj C) : HopfObj (ob t.obj) where
  toBimonObj := bimonObj t
  antipode := antipode t.obj
  antipode_left := (thy_axioms t).antipode_left
  antipode_right := (thy_axioms t).antipode_right

/-- A `T_Hopf`-bialgebra, as a Hopf monoid of `C`. -/
def toHopf (t : ThyObj C) : Hopf C where
  X := ob t.obj

/-- A morphism of `T_Hopf`-bialgebras, as a morphism of Hopf monoids. -/
def hopfHom {t t' : ThyObj C} (f : t ⟶ t') : toHopf t ⟶ toHopf t' where
  hom := Comon.Hom.mk' (Mon.Hom.mk' (bs f.hom) (bs_one f.hom) (bs_mul f.hom))
    (Mon.Hom.ext (bs_counit f.hom)) (Mon.Hom.ext (bs_comul f.hom))

/-! ## Hopf monoids are objects of `M^T` -/

/-- A Hopf monoid of `C`, as an object of `M^σ`. -/
def ofHopfSig (H : Hopf C) : SigObj C where
  pt := fun _ => H.X
  cell := fun f => match f with
    | HopfEx.FnSym.mul => (MonObj.mul : H.X ⊗ H.X ⟶ H.X)
    | HopfEx.FnSym.one => (MonObj.one : 𝟙_ C ⟶ H.X)
    | HopfEx.FnSym.comul => (ComonObj.comul : H.X ⟶ H.X ⊗ H.X)
    | HopfEx.FnSym.counit => (ComonObj.counit : H.X ⟶ 𝟙_ C)
    | HopfEx.FnSym.antipode => (HopfObj.antipode : H.X ⟶ H.X)

/-- The underlying object of `ofHopfSig H` is `H.X`. -/
@[simp] lemma ob_ofHopfSig (H : Hopf C) : ob (ofHopfSig H) = H.X := rfl

/-- The multiplication of `ofHopfSig H` is that of `H`. -/
@[simp] lemma mul_ofHopfSig (H : Hopf C) :
    mul (ofHopfSig H) = (MonObj.mul : H.X ⊗ H.X ⟶ H.X) := rfl

/-- The unit of `ofHopfSig H` is that of `H`. -/
@[simp] lemma one_ofHopfSig (H : Hopf C) : one (ofHopfSig H) = (MonObj.one : 𝟙_ C ⟶ H.X) := rfl

/-- The comultiplication of `ofHopfSig H` is that of `H`. -/
@[simp] lemma comul_ofHopfSig (H : Hopf C) :
    comul (ofHopfSig H) = (ComonObj.comul : H.X ⟶ H.X ⊗ H.X) := rfl

/-- The counit of `ofHopfSig H` is that of `H`. -/
@[simp] lemma counit_ofHopfSig (H : Hopf C) :
    counit (ofHopfSig H) = (ComonObj.counit : H.X ⟶ 𝟙_ C) := rfl

/-- The antipode of `ofHopfSig H` is that of `H`. -/
@[simp] lemma antipode_ofHopfSig (H : Hopf C) :
    antipode (ofHopfSig H) = (HopfObj.antipode : H.X ⟶ H.X) := rfl

/-- A Hopf monoid satisfies the twelve equations of `T_Hopf`. -/
lemma axioms_ofHopfSig (H : Hopf C) : Axioms (ofHopfSig H) where
  mul_assoc := MonObj.mul_assoc H.X
  one_mul := MonObj.one_mul H.X
  mul_one := by
    rw [Iso.inv_comp_eq, Category.comp_id]
    exact MonObj.mul_one H.X
  comul_assoc := (ComonObj.comul_assoc H.X).symm
  counit_comul := by
    rw [← Category.assoc, Iso.comp_hom_eq_id]
    exact ComonObj.counit_comul H.X
  comul_counit := ComonObj.comul_counit H.X
  bialg := by
    have h := BimonObj.mul_comul H.X
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Category.assoc] at h
    exact h.symm
  counit_mul := by
    have h := Bimon.mul_counit H.X
    rw [MonoidalCategory.tensorHom_def, Category.assoc] at h
    exact h.symm
  one_comul := by
    rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.unitors_inv_equal]
    exact (Bimon.one_comul H.X).symm
  one_counit := BimonObj.one_counit H.X
  antipode_right := HopfObj.antipode_right H.X
  antipode_left := HopfObj.antipode_left H.X

/-- A Hopf monoid of `C`, as an object of `M^{T_Hopf}`. -/
def ofHopf (H : Hopf C) : ThyObj C :=
  ⟨ofHopfSig H, (mem_thy_iff (ofHopfSig H)).2 (axioms_ofHopfSig H)⟩

/-! ## The comparison functor -/

variable (C) in
/-- **The comparison functor** from `M^{T_Hopf}` to the category of Hopf monoids of `C`. -/
def comparison : ThyObj C ⥤ Hopf C where
  obj t := toHopf t
  map f := hopfHom f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor `M^{T_Hopf} ⥤ Hopf C` is faithful. -/
instance : (comparison C).Faithful where
  map_injective {_ _} f g h := by
    apply ObjectProperty.hom_ext
    apply bs_injective
    exact congrArg (fun k => k.hom.hom.hom) h

/-- A morphism of Hopf monoids between the images of two `T_Hopf`-bialgebras, as a morphism of
`T_Hopf`-bialgebras. -/
def homOfHopfHom {t t' : ThyObj C} (g : toHopf t ⟶ toHopf t') : t ⟶ t' :=
  have hm : mul t.obj ≫ g.hom.hom.hom = (g.hom.hom.hom ⊗ₘ g.hom.hom.hom) ≫ mul t'.obj :=
    IsMonHom.mul_hom g.hom.hom.hom
  have he : one t.obj ≫ g.hom.hom.hom = one t'.obj := IsMonHom.one_hom g.hom.hom.hom
  let b : Comon.Hom (toHopf t).toBimon (toHopf t').toBimon := g.hom
  have hc : g.hom.hom.hom ≫ comul t'.obj = comul t.obj ≫ (g.hom.hom.hom ⊗ₘ g.hom.hom.hom) := by
    have h := congrArg Mon.Hom.hom (@IsComonHom.hom_comul (Mon C) inferInstance inferInstance
      _ _ (toHopf t).toBimon.comon (toHopf t').toBimon.comon b.hom b.isComonHom_hom)
    exact h
  have hu : g.hom.hom.hom ≫ counit t'.obj = counit t.obj := by
    have h := congrArg Mon.Hom.hom (@IsComonHom.hom_counit (Mon C) inferInstance inferInstance
      _ _ (toHopf t).toBimon.comon (toHopf t').toBimon.comon b.hom b.isComonHom_hom)
    exact h
  haveI : IsBimonHom (M := ob t.obj) (N := ob t'.obj) g.hom.hom.hom :=
    { one_hom := he, mul_hom := hm, hom_counit := hu, hom_comul := hc }
  have hs : antipode t.obj ≫ g.hom.hom.hom = g.hom.hom.hom ≫ antipode t'.obj :=
    (HopfObj.hom_antipode (A := ob t.obj) (B := ob t'.obj) g.hom.hom.hom).symm
  ObjectProperty.homMk (sigHomMk g.hom.hom.hom hm he hc hu hs)

/-! ## The inverse functor: an isomorphism of categories over `C` -/

variable (C) in
/-- The strict inverse of the comparison functor: a Hopf monoid of `C`, as a
`T_Hopf`-bialgebra. -/
def inverseFunctor : Hopf C ⥤ ThyObj C where
  obj H := ofHopf H
  map g := homOfHopfHom g
  map_id _ := rfl
  map_comp _ _ := rfl

variable (C) in
/-- The comparison functor is a strict left inverse of `inverseFunctor`. -/
lemma inverseFunctor_comp_comparison : inverseFunctor C ⋙ comparison C = 𝟭 (Hopf C) := rfl

/-- `inverseFunctor` is a strict left inverse of the comparison functor on objects. -/
lemma inverseFunctor_obj_comparison_obj (t : ThyObj C) :
    (inverseFunctor C).obj ((comparison C).obj t) = t := by
  apply ObjectProperty.FullSubcategory.ext
  obtain ⟨⟨pt, cell⟩, h⟩ := t
  change Ins.mk pt _ = Ins.mk pt cell
  congr 1
  funext f
  cases f <;> rfl

variable (C) in
/-- `inverseFunctor` is a strict left inverse of the comparison functor. -/
lemma comparison_comp_inverseFunctor : comparison C ⋙ inverseFunctor C = 𝟭 (ThyObj C) :=
  comp_eq_id_of_faithful _ _ (inverseFunctor_comp_comparison C) inverseFunctor_obj_comparison_obj

variable (C) in
/-- The comparison functor lies over `C`: it commutes with the forgetful functors to `C`, where
`M^{T_Hopf}` lies over `C` through `U : M^{T_Hopf} → M₀` and the projection `M₀ → C`. -/
lemma comparison_comp_hopfForget :
    comparison C ⋙ hopfForget C = (HopfModel.forget C).toFunctor ⋙ (((hopfModel C).P0
        HopfEx.oneSig).π ()).toFunctor :=
  rfl

end UlmerBialgebras.Paper.HopfModel.Internal
