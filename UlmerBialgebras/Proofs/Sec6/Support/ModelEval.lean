module

public import UlmerBialgebras.Proofs.Sec3.LaxLimitCalc
public import UlmerBialgebras.Paper.Sec3DefsLaxLimit
public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc
public import UlmerBialgebras.Examples.MonadEx
public import UlmerBialgebras.Examples.MonModel
public import UlmerBialgebras.Models.Induced
public import UlmerBialgebras.Kan.KanModel

/-!
# Evaluation lemmas for `semAt` and the concrete `CAT` models

Evaluation lemmas for `LaxLimit.Internal.semAt`, for the functor and transformation interpretations
of the frozen the development repository's `Challenge/` models (`LaxLimit.monModel`,
`Loc.smonModel`), and for
`PreModel.appCell`, `LaxData.strAt`, `Model.trAt`, and `LaxData.eta` in `CAT`.

Because `semAt`, `appCell`, and `eta` apply `(M.fn B).toFunctor.map` to a morphism family indexed
by `Fin (Sg.arn B)` over the pi type `∀ i, (M.obj (Sg.art B i) : Type _)`, stating the `fn`
evaluation lemmas at that exact pi type lets `rw` and `simp` reduce `semAt`, `appCell`, `trAt`,
and `eta` without manual `change` restatements.

## Main results

* `UlmerBialgebras.Paper.ModelEval.cat_appCell_app`,
  `UlmerBialgebras.Paper.ModelEval.cat_strAt_app`,
  `UlmerBialgebras.Paper.ModelEval.cat_trAt_app`,
  `UlmerBialgebras.Paper.ModelEval.cat_eta_var_app`,
  `UlmerBialgebras.Paper.ModelEval.cat_eta_app_app`,
  `UlmerBialgebras.Paper.ModelEval.cat_sigStr_app`,
  `UlmerBialgebras.Paper.ModelEval.cat_thyForget_toFunctor`: componentwise evaluation in `CAT`.
* `UlmerBialgebras.Paper.LaxLimit.monModel_fn_tens_map`,
  `UlmerBialgebras.Paper.LaxLimit.monModel_fn_unit_map`,
  `UlmerBialgebras.Paper.Loc.smonPreModel_fn_tens_map`,
  `UlmerBialgebras.Paper.Loc.smonPreModel_fn_unit_map`,
  `UlmerBialgebras.Paper.Loc.smonModel_fn_tens_map`,
  `UlmerBialgebras.Paper.Loc.smonModel_fn_unit_map`,
  `UlmerBialgebras.Paper.Loc.smonModel_trAt_*_app`,
  `UlmerBialgebras.MonEx.monModel_trAt_*_app`: `fn` and `trAt` evaluation lemmas for the concrete
  monoidal models.
* `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_var`,
  `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_app`,
  `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_mndModel_T`,
  `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_monModel_tens`,
  `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_monModel_unit`,
  `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_smonModel_tens`,
  `UlmerBialgebras.Paper.LaxLimit.Internal.semAt_smonModel_unit`: recursive evaluation of `semAt` on
  the monad, monoidal, and symmetric monoidal models.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 3
-/

@[expose] public section

universe v u u₁ u₂ u₃ uᵥ

open CategoryTheory MonoidalCategory

namespace UlmerBialgebras.Paper.ModelEval

/-! ## Componentwise evaluation of `appCell`, `strAt`, `trAt`, and `eta` in `CAT` -/

section CatModel

variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-- In `CAT`, projecting from `M.Pctx a` at `p` returns `p i`. -/
lemma cat_Pctx_π_obj (M : Model Sg Cat.{v, u}) (a : Sg.Tr) (i : Fin (Sg.trn a))
    (p : (M.Pctx a).pt) :
    ((M.Pctx a).π i).toFunctor.obj p = p i := rfl

/-- In `CAT`, `(M.interp ρ (.var v)).toFunctor.obj p` is `(ρ v).toFunctor.obj p`. -/
lemma cat_interp_var_obj (M : PreModel Sg Cat.{v, u}) {V : Type uᵥ} {vty : V → Sg.Cat}
    {x : Cat.{v, u}} (ρ : ∀ v, x ⟶ M.obj (vty v)) (v : V) (p : x) :
    (M.interp ρ (Trm.var v)).toFunctor.obj p = (ρ v).toFunctor.obj p := rfl

/-- In `CAT`, `(M.interp ρ (.app B args)).toFunctor.obj p` is `(M.fn B).toFunctor.obj` applied to
the family of interpreted arguments at `p`. -/
lemma cat_interp_app_obj (M : PreModel Sg Cat.{v, u}) {V : Type uᵥ} {vty : V → Sg.Cat}
    {x : Cat.{v, u}} (ρ : ∀ v, x ⟶ M.obj (vty v)) (B : Sg.Fun)
    (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) (p : x) :
    (M.interp ρ (Trm.app B args)).toFunctor.obj p =
      (M.fn B).toFunctor.obj (fun i => (M.interp ρ (args i)).toFunctor.obj p) := rfl

/-- In `CAT`, `M.appCell B γ` evaluates at `p` to `(M.fn B).toFunctor.map` applied to the family of
components `(γ i).toNatTrans.app p`. -/
lemma cat_appCell_app (M : PreModel Sg Cat.{v, u}) (B : Sg.Fun) {x : Cat.{v, u}}
    {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) (p : x) :
    (M.appCell B γ).toNatTrans.app p =
      (M.fn B).toFunctor.map (X := fun i => (g i).toFunctor.obj p)
        (Y := fun i => (g' i).toFunctor.obj p) (fun i => (γ i).toNatTrans.app p) := by
  have h : ((M.P B).lift₂ (fun i => eqToHom ((M.P B).lift_π g i) ≫ γ i ≫
      eqToHom ((M.P B).lift_π g' i).symm)).toNatTrans.app p =
        (fun i => (γ i).toNatTrans.app p) := by
    funext i
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [PreModel.appCell, Cat.whiskerRight_app]
  exact congr((M.fn B).toFunctor.map $h)

/-- In `CAT`, `L.strAt B g` evaluates at `p` to `(L.str B).toNatTrans.app` at
`fun i => (g i).toFunctor.obj p`. -/
lemma cat_strAt_app {M N : PreModel Sg Cat.{v, u}} (L : LaxData M N) (B : Sg.Fun)
    {x : Cat.{v, u}} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) (p : x) :
    (L.strAt B g).toNatTrans.app p =
      (L.str B).toNatTrans.app (fun i => (g i).toFunctor.obj p) := by
  rw [LaxData.strAt]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- In `CAT`, `M.trAt a ρ` evaluates at `p` to `(M.tr a).toNatTrans.app` at
`fun i => (ρ i).toFunctor.obj p`, up to the transports from `interp_lift_ctx`. -/
lemma cat_trAt_app (M : Model Sg Cat.{v, u}) (a : Sg.Tr) {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) (p : x) :
    (M.trAt a ρ).toNatTrans.app p =
      eqToHom congr(($(M.interp_lift_ctx a ρ (Sg.trsrc a))).toFunctor.obj p) ≫
        (M.tr a).toNatTrans.app (fun i => (ρ i).toFunctor.obj p) ≫
        eqToHom congr(($(M.interp_lift_ctx a ρ (Sg.trtgt a))).toFunctor.obj p).symm := by
  simp only [Model.trAt, Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
  rfl

/-- In `CAT`, `(L.eta ρ (.var v)).toNatTrans.app p` is the identity. -/
lemma cat_eta_var_app {M N : PreModel Sg Cat.{v, u}} (L : LaxData M N)
    {V : Type uᵥ} {vty : V → Sg.Cat} {x : Cat.{v, u}} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (v : V) (p : x) :
    (L.eta ρ (Trm.var v)).toNatTrans.app p =
      𝟙 ((L.cell (vty v)).toFunctor.obj ((ρ v).toFunctor.obj p)) :=
  rfl

/-- In `CAT`, `(L.eta ρ (.app B args)).toNatTrans.app p` is `(N.fn B).toFunctor.map` applied to
the argument components followed by `(L.str B).toNatTrans.app`. -/
lemma cat_eta_app_app {M N : PreModel Sg Cat.{v, u}} (L : LaxData M N)
    {V : Type uᵥ} {vty : V → Sg.Cat} {x : Cat.{v, u}} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (B : Sg.Fun) (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) (p : x) :
    (L.eta ρ (Trm.app B args)).toNatTrans.app p =
      (N.fn B).toFunctor.map
          (X := fun i => (N.interp (fun v => ρ v ≫ L.cell (vty v)) (args i)).toFunctor.obj p)
          (Y := fun i => ((M.interp ρ (args i)) ≫ L.cell (Sg.art B i)).toFunctor.obj p)
          (fun i => (L.eta ρ (args i)).toNatTrans.app p) ≫
        (L.str B).toNatTrans.app (fun i => (M.interp ρ (args i)).toFunctor.obj p) := by
  rw [LaxData.eta_app, Cat.Hom.toNatTrans_comp, NatTrans.comp_app, cat_appCell_app]
  exact _ ≫= cat_strAt_app L B (fun i => M.interp ρ (args i)) p

/-- In `CAT`, evaluating `F.sigStr sg hiso` at `z` and `f` when `F.Psi sg (sg.fncod f)` is an
`eqToHom` reduces to `F.eta` composed with `F.cell.map` on `M.arrCell`, flanked by `eqToHom`. -/
lemma cat_sigStr_app {M N : Model Sg Cat.{v, max u v}} (F : LaxMor M N)
    (sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg)
    (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fncod f))) (f : sg.Fn)
    {hcod : (M.u sg ≫ F.prod0 sg) ≫ N.tm sg (sg.fncod f) =
      M.sigTm sg (sg.fncod f) ≫ F.cell (sg.fnty f)}
    (hpsi : F.Psi sg (sg.fncod f) = eqToHom hcod) (z : M.sigObj sg) :
    (F.sigStr sg hiso).toNatTrans.app z f =
      eqToHom congr(($(F.sigStr_dom_eq sg f)).toFunctor.obj z) ≫
        eqToHom congr(($(F.sig_src_eq sg (sg.fndom f))).toFunctor.obj z) ≫
        (F.toLaxData.eta (M.P0 sg).π (sg.fndom f)).toNatTrans.app ((M.u sg).toFunctor.obj z) ≫
        eqToHom congr(($(F.sig_tgt_eq sg (sg.fndom f))).toFunctor.obj z) ≫
        (F.cell (sg.fnty f)).toFunctor.map
          ((M.arrCell sg (OneSig.Arr.fn f)).toNatTrans.app z) ≫
        eqToHom congr(($hcod).toFunctor.obj z).symm ≫
        eqToHom congr(($(F.sigStr_cod_eq sg f)).toFunctor.obj z).symm := by
  have : IsIso (F.etaTm sg (sg.fncod f)) := hiso f
  have hinv : inv (F.Psi sg (sg.fncod f)) = eqToHom hcod.symm :=
    IsIso.inv_eq_of_hom_inv_id ((hpsi =≫ _).trans ((eqToHom_trans _ _).trans (eqToHom_refl _ _)))
  rw [LaxMor.sigStr, cat_lift₂_app, hinv, LaxMor.Psi, LaxMor.etaTm]
  simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans, Cat.whiskerLeft_toNatTrans,
    Cat.Hom₂.eqToHom_toNatTrans]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_app,
    Category.assoc]
  rfl

/-- In `CAT`, `(M.thyForget sg T).toFunctor` is the composition of `M.e` and `M.u`. -/
lemma cat_thyForget_toFunctor (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg) (T : Theory.{u₁, u₂, u₃, 0, 0, 0} sg) :
    (M.thyForget sg T).toFunctor = (M.e sg T).toFunctor ⋙ (M.u sg).toFunctor := rfl

end CatModel

end UlmerBialgebras.Paper.ModelEval

/-! ## Evaluation lemmas for `LaxLimit.monModel` (frozen in
`UlmerBialgebras/Paper/Sec3DefsLaxLimit.lean`) -/

namespace UlmerBialgebras.Paper.LaxLimit

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Evaluating the tensor functor symbol of `LaxLimit.monModel` on an object family tensors
indices `0` and `1`. -/
lemma monModel_fn_tens_obj
    (X : ∀ i : Fin (SigEx.monSig.arn SigEx.MonFun.tens),
      ((monModel C).obj (SigEx.monSig.art SigEx.MonFun.tens i) : Type u)) :
    ((monModel C).fn SigEx.MonFun.tens).toFunctor.obj X =
      MonoidalCategoryStruct.tensorObj (C := C) (X 0) (X 1) := rfl

/-- Evaluating the tensor functor symbol of `LaxLimit.monModel` on a morphism family tensors
indices `0` and `1`. -/
lemma monModel_fn_tens_map
    {X Y : ∀ i : Fin (SigEx.monSig.arn SigEx.MonFun.tens),
      ((monModel C).obj (SigEx.monSig.art SigEx.MonFun.tens i) : Type u)} (f : X ⟶ Y) :
    ((monModel C).fn SigEx.MonFun.tens).toFunctor.map f =
      MonoidalCategoryStruct.tensorHom (C := C) (f 0) (f 1) := rfl

/-- Evaluating the unit functor symbol of `LaxLimit.monModel` on an empty object family gives
`𝟙_ C`. -/
lemma monModel_fn_unit_obj
    (X : ∀ i : Fin (SigEx.monSig.arn SigEx.MonFun.unit),
      ((monModel C).obj (SigEx.monSig.art SigEx.MonFun.unit i) : Type u)) :
    ((monModel C).fn SigEx.MonFun.unit).toFunctor.obj X = 𝟙_ C := rfl

/-- Evaluating the unit functor symbol of `LaxLimit.monModel` on an empty morphism family gives
`𝟙 (𝟙_ C)`. -/
lemma monModel_fn_unit_map
    {X Y : ∀ i : Fin (SigEx.monSig.arn SigEx.MonFun.unit),
      ((monModel C).obj (SigEx.monSig.art SigEx.MonFun.unit i) : Type u)} (f : X ⟶ Y) :
    ((monModel C).fn SigEx.MonFun.unit).toFunctor.map f = 𝟙 (𝟙_ C) := rfl

end UlmerBialgebras.Paper.LaxLimit

/-! ## Evaluation lemmas for `Loc.smonModel` (frozen in `UlmerBialgebras/Paper/Sec3DefsLoc.lean`) -/

namespace UlmerBialgebras.Paper.Loc

section SMonPreModel

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Evaluating the tensor functor symbol of `Loc.smonPreModel` on an object family tensors
indices `0` and `1`. -/
lemma smonPreModel_fn_tens_obj
    (X : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.tens),
      ((smonPreModel C).obj (SigEx.smonSig.art SigEx.MonFun.tens i) : Type u)) :
    ((smonPreModel C).fn SigEx.MonFun.tens).toFunctor.obj X =
      MonoidalCategoryStruct.tensorObj (C := C) (X 0) (X 1) := rfl

/-- Evaluating the tensor functor symbol of `Loc.smonPreModel` on a morphism family tensors
indices `0` and `1`. -/
lemma smonPreModel_fn_tens_map
    {X Y : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.tens),
      ((smonPreModel C).obj (SigEx.smonSig.art SigEx.MonFun.tens i) : Type u)} (f : X ⟶ Y) :
    ((smonPreModel C).fn SigEx.MonFun.tens).toFunctor.map f =
      MonoidalCategoryStruct.tensorHom (C := C) (f 0) (f 1) := rfl

/-- Evaluating the unit functor symbol of `Loc.smonPreModel` on an empty object family gives
`𝟙_ C`. -/
lemma smonPreModel_fn_unit_obj
    (X : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.unit),
      ((smonPreModel C).obj (SigEx.smonSig.art SigEx.MonFun.unit i) : Type u)) :
    ((smonPreModel C).fn SigEx.MonFun.unit).toFunctor.obj X = 𝟙_ C := rfl

/-- Evaluating the unit functor symbol of `Loc.smonPreModel` on an empty morphism family gives
`𝟙 (𝟙_ C)`. -/
lemma smonPreModel_fn_unit_map
    {X Y : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.unit),
      ((smonPreModel C).obj (SigEx.smonSig.art SigEx.MonFun.unit i) : Type u)} (f : X ⟶ Y) :
    ((smonPreModel C).fn SigEx.MonFun.unit).toFunctor.map f = 𝟙 (𝟙_ C) := rfl

end SMonPreModel

section SMonModel

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Evaluating the tensor functor symbol of `Loc.smonModel` on an object family tensors
indices `0` and `1`. -/
lemma smonModel_fn_tens_obj
    (X : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.tens),
      ((smonModel C).obj (SigEx.smonSig.art SigEx.MonFun.tens i) : Type u)) :
    ((smonModel C).fn SigEx.MonFun.tens).toFunctor.obj X =
      MonoidalCategoryStruct.tensorObj (C := C) (X 0) (X 1) := rfl

/-- Evaluating the tensor functor symbol of `Loc.smonModel` on a morphism family tensors
indices `0` and `1`. -/
lemma smonModel_fn_tens_map
    {X Y : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.tens),
      ((smonModel C).obj (SigEx.smonSig.art SigEx.MonFun.tens i) : Type u)} (f : X ⟶ Y) :
    ((smonModel C).fn SigEx.MonFun.tens).toFunctor.map f =
      MonoidalCategoryStruct.tensorHom (C := C) (f 0) (f 1) := rfl

/-- Evaluating the unit functor symbol of `Loc.smonModel` on an empty object family gives
`𝟙_ C`. -/
lemma smonModel_fn_unit_obj
    (X : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.unit),
      ((smonModel C).obj (SigEx.smonSig.art SigEx.MonFun.unit i) : Type u)) :
    ((smonModel C).fn SigEx.MonFun.unit).toFunctor.obj X = 𝟙_ C := rfl

/-- Evaluating the unit functor symbol of `Loc.smonModel` on an empty morphism family gives
`𝟙 (𝟙_ C)`. -/
lemma smonModel_fn_unit_map
    {X Y : ∀ i : Fin (SigEx.smonSig.arn SigEx.MonFun.unit),
      ((smonModel C).obj (SigEx.smonSig.art SigEx.MonFun.unit i) : Type u)} (f : X ⟶ Y) :
    ((smonModel C).fn SigEx.MonFun.unit).toFunctor.map f = 𝟙 (𝟙_ C) := rfl

/-- Evaluating the `assoc` cell of `Loc.smonModel` gives the associator. -/
lemma smonModel_tr_assoc_app (p : ((smonModel C).Pctx SigEx.SMonTr.assoc).pt) :
    ((smonModel C).tr SigEx.SMonTr.assoc).toNatTrans.app p =
      (MonoidalCategoryStruct.associator (C := C) (p 0) (p 1) (p 2)).hom := rfl

/-- Evaluating the `assocInv` cell of `Loc.smonModel` gives the inverse associator. -/
lemma smonModel_tr_assocInv_app (p : ((smonModel C).Pctx SigEx.SMonTr.assocInv).pt) :
    ((smonModel C).tr SigEx.SMonTr.assocInv).toNatTrans.app p =
      (MonoidalCategoryStruct.associator (C := C) (p 0) (p 1) (p 2)).inv := rfl

/-- Evaluating the `lunit` cell of `Loc.smonModel` gives the left unitor. -/
lemma smonModel_tr_lunit_app (p : ((smonModel C).Pctx SigEx.SMonTr.lunit).pt) :
    ((smonModel C).tr SigEx.SMonTr.lunit).toNatTrans.app p =
      (MonoidalCategoryStruct.leftUnitor (C := C) (p 0)).hom := rfl

/-- Evaluating the `lunitInv` cell of `Loc.smonModel` gives the inverse left unitor. -/
lemma smonModel_tr_lunitInv_app (p : ((smonModel C).Pctx SigEx.SMonTr.lunitInv).pt) :
    ((smonModel C).tr SigEx.SMonTr.lunitInv).toNatTrans.app p =
      (MonoidalCategoryStruct.leftUnitor (C := C) (p 0)).inv := rfl

/-- Evaluating the `runit` cell of `Loc.smonModel` gives the right unitor. -/
lemma smonModel_tr_runit_app (p : ((smonModel C).Pctx SigEx.SMonTr.runit).pt) :
    ((smonModel C).tr SigEx.SMonTr.runit).toNatTrans.app p =
      (MonoidalCategoryStruct.rightUnitor (C := C) (p 0)).hom := rfl

/-- Evaluating the `runitInv` cell of `Loc.smonModel` gives the inverse right unitor. -/
lemma smonModel_tr_runitInv_app (p : ((smonModel C).Pctx SigEx.SMonTr.runitInv).pt) :
    ((smonModel C).tr SigEx.SMonTr.runitInv).toNatTrans.app p =
      (MonoidalCategoryStruct.rightUnitor (C := C) (p 0)).inv := rfl

/-- Evaluating the `sym` cell of `Loc.smonModel` gives the braiding. -/
lemma smonModel_tr_sym_app (p : ((smonModel C).Pctx SigEx.SMonTr.sym).pt) :
    ((smonModel C).tr SigEx.SMonTr.sym).toNatTrans.app p =
      (BraidedCategory.braiding (C := C) (p 0) (p 1)).hom := rfl

/-- Evaluating `smonModel.trAt` at `assoc` gives the associator. -/
lemma smonModel_trAt_assoc_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.assoc i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.assoc ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.associator (C := C)
        ((ρ 0).toFunctor.obj p) ((ρ 1).toFunctor.obj p) ((ρ 2).toFunctor.obj p)).hom := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `smonModel.trAt` at `assocInv` gives the inverse associator. -/
lemma smonModel_trAt_assocInv_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.assocInv i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.assocInv ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.associator (C := C)
        ((ρ 0).toFunctor.obj p) ((ρ 1).toFunctor.obj p) ((ρ 2).toFunctor.obj p)).inv := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `smonModel.trAt` at `lunit` gives the left unitor. -/
lemma smonModel_trAt_lunit_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.lunit i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.lunit ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.leftUnitor (C := C) ((ρ 0).toFunctor.obj p)).hom := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `smonModel.trAt` at `lunitInv` gives the inverse left unitor. -/
lemma smonModel_trAt_lunitInv_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.lunitInv i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.lunitInv ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.leftUnitor (C := C) ((ρ 0).toFunctor.obj p)).inv := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `smonModel.trAt` at `runit` gives the right unitor. -/
lemma smonModel_trAt_runit_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.runit i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.runit ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.rightUnitor (C := C) ((ρ 0).toFunctor.obj p)).hom := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `smonModel.trAt` at `runitInv` gives the inverse right unitor. -/
lemma smonModel_trAt_runitInv_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.runitInv i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.runitInv ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.rightUnitor (C := C) ((ρ 0).toFunctor.obj p)).inv := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `smonModel.trAt` at `sym` gives the braiding. -/
lemma smonModel_trAt_sym_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (smonModel C).obj (SigEx.smonSig.trt SigEx.SMonTr.sym i)) (p : x) :
    ((smonModel C).trAt SigEx.SMonTr.sym ρ).toNatTrans.app p =
      (BraidedCategory.braiding (C := C)
        ((ρ 0).toFunctor.obj p) ((ρ 1).toFunctor.obj p)).hom := by
  rw [ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

end SMonModel

end UlmerBialgebras.Paper.Loc

/-! ## Evaluation lemmas for `Model.trAt` on `MonEx.monModel` -/

namespace UlmerBialgebras.MonEx

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Evaluating `Model.trAt` on `MonEx.monModel` at `assoc` gives the associator. -/
lemma monModel_trAt_assoc_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (monModel C).obj (twoSig.trt TrSym.assoc i)) (p : x) :
    ((monModel C).trAt TrSym.assoc ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.associator (C := C)
        ((ρ 0).toFunctor.obj p) ((ρ 1).toFunctor.obj p) ((ρ 2).toFunctor.obj p)).hom := by
  rw [Paper.ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `Model.trAt` on `MonEx.monModel` at `lunit` gives the left unitor. -/
lemma monModel_trAt_lunit_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (monModel C).obj (twoSig.trt TrSym.lunit i)) (p : x) :
    ((monModel C).trAt TrSym.lunit ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.leftUnitor (C := C) ((ρ 0).toFunctor.obj p)).hom := by
  rw [Paper.ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Evaluating `Model.trAt` on `MonEx.monModel` at `runit` gives the right unitor. -/
lemma monModel_trAt_runit_app {x : Cat.{v, u}}
    (ρ : ∀ i, x ⟶ (monModel C).obj (twoSig.trt TrSym.runit i)) (p : x) :
    ((monModel C).trAt TrSym.runit ρ).toNatTrans.app p =
      (MonoidalCategoryStruct.rightUnitor (C := C) ((ρ 0).toFunctor.obj p)).hom := by
  rw [Paper.ModelEval.cat_trAt_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

end UlmerBialgebras.MonEx

/-! ## Evaluation lemmas for `semAt` -/

namespace UlmerBialgebras.Paper.LaxLimit.Internal

/-- `semAt` on a variable term is the identity on the object component of `z`. -/
lemma semAt_var {Sg : TwoSig.{0, 0, 0}} (M : Model Sg Cat.{v, max u v})
    (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) (c : Sg.Cat) :
    semAt M z (Trm.var c) = 𝟙 (Ins.pt z c) := rfl

/-- `semAt` on an application term applies `(M.fn B).toFunctor.map` to the recursive family of
evaluations and postcomposes with `Ins.cell z B`. -/
lemma semAt_app {Sg : TwoSig.{0, 0, 0}} (M : Model Sg Cat.{v, max u v})
    (z : (M.sigObj (LaxEx.oneSig Sg) : Type (max u v))) (B : Sg.Fun)
    (ts : ∀ i, (LaxEx.oneSig Sg).CTrm (Sg.art B i)) :
    semAt M z (Trm.app B ts) =
      (M.fn B).toFunctor.map
          (X := fun i => (M.sigTm (LaxEx.oneSig Sg) (ts i)).toFunctor.obj z)
          (Y := fun i => (M.sigTm (LaxEx.oneSig Sg) (Trm.var (Sg.art B i))).toFunctor.obj z)
          (fun i => semAt M z (ts i)) ≫
        Ins.cell z B := rfl

/-- `semAt` on the monad model `MndEx.model T` at `.app .T ts` applies `T.map` to `ts 0` followed
by `Ins.cell z .T`. -/
lemma semAt_mndModel_T {C : Type (max u v)} [Category.{v} C] (T : Monad C)
    (z : ((MndEx.model T).sigObj (LaxEx.oneSig SigEx.mndSig) : Type (max u v)))
    (ts : ∀ i, (LaxEx.oneSig SigEx.mndSig).CTrm (SigEx.mndSig.art SigEx.MndFun.T i)) :
    semAt (MndEx.model T) z (Trm.app SigEx.MndFun.T ts) =
      (T : C ⥤ C).map (semAt (MndEx.model T) z (ts 0)) ≫ Ins.cell z SigEx.MndFun.T := rfl

/-- `semAt` on `LaxLimit.monModel C` at `.app .tens ts` tensors the evaluations of `ts 0` and
`ts 1`, followed by `Ins.cell z .tens`. -/
lemma semAt_monModel_tens {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v)))
    (ts : ∀ i, (LaxEx.oneSig SigEx.monSig).CTrm (SigEx.monSig.art SigEx.MonFun.tens i)) :
    semAt (LaxLimit.monModel C) z (Trm.app SigEx.MonFun.tens ts) =
      MonoidalCategoryStruct.tensorHom (C := C)
          (semAt (LaxLimit.monModel C) z (ts 0)) (semAt (LaxLimit.monModel C) z (ts 1)) ≫
        Ins.cell z SigEx.MonFun.tens := rfl

/-- `semAt` on `LaxLimit.monModel C` at `.app .unit ts` is `Ins.cell z .unit`. -/
lemma semAt_monModel_unit {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v)))
    (ts : ∀ i, (LaxEx.oneSig SigEx.monSig).CTrm (SigEx.monSig.art SigEx.MonFun.unit i)) :
    semAt (LaxLimit.monModel C) z (Trm.app SigEx.MonFun.unit ts) =
      Ins.cell z SigEx.MonFun.unit :=
  Category.id_comp _

/-- `semAt` on `Loc.smonModel C` at `.app .tens ts` tensors the evaluations of `ts 0` and `ts 1`,
followed by `Ins.cell z .tens`. -/
lemma semAt_smonModel_tens {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C]
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v)))
    (ts : ∀ i, (LaxEx.oneSig SigEx.smonSig).CTrm (SigEx.smonSig.art SigEx.MonFun.tens i)) :
    semAt (Loc.smonModel C) z (Trm.app SigEx.MonFun.tens ts) =
      MonoidalCategoryStruct.tensorHom (C := C)
          (semAt (Loc.smonModel C) z (ts 0)) (semAt (Loc.smonModel C) z (ts 1)) ≫
        Ins.cell z SigEx.MonFun.tens := rfl

/-- `semAt` on `Loc.smonModel C` at `.app .unit ts` is `Ins.cell z .unit`. -/
lemma semAt_smonModel_unit {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C]
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v)))
    (ts : ∀ i, (LaxEx.oneSig SigEx.smonSig).CTrm (SigEx.smonSig.art SigEx.MonFun.unit i)) :
    semAt (Loc.smonModel C) z (Trm.app SigEx.MonFun.unit ts) =
      Ins.cell z SigEx.MonFun.unit :=
  Category.id_comp _

/-! ### Evaluated `semAt` terms for the transformation symbols of `Σ_Mnd`, `Σ_Mon`, and `Σ_SMon` -/

section MndSemAt

variable {C : Type (max u v)} [Category.{v} C] (T : Monad C)

/-- `semAt` on `trtgt .mu` (i.e. `T(x)`) for the monad model evaluates to the action cell. -/
lemma semAt_mndModel_trtgt_mu
    (z : ((MndEx.model T).sigObj (LaxEx.oneSig SigEx.mndSig) : Type (max u v))) :
    semAt (MndEx.model T) z ((SigEx.mndSig.trtgt SigEx.MndTr.mu).subst
      (LaxEx.subS SigEx.mndSig SigEx.MndTr.mu)) = Ins.cell z SigEx.MndFun.T :=
  (semAt_mndModel_T T z _).trans
    (((T : C ⥤ C).map_id (Ins.pt z ()) =≫ _).trans (Category.id_comp _))

/-- `semAt` on `trsrc .mu` (i.e. `T(T(x))`) for the monad model evaluates to `T(a) ≫ a`. -/
lemma semAt_mndModel_trsrc_mu
    (z : ((MndEx.model T).sigObj (LaxEx.oneSig SigEx.mndSig) : Type (max u v))) :
    semAt (MndEx.model T) z ((SigEx.mndSig.trsrc SigEx.MndTr.mu).subst
      (LaxEx.subS SigEx.mndSig SigEx.MndTr.mu)) =
      (T : C ⥤ C).map (Ins.cell z SigEx.MndFun.T) ≫ Ins.cell z SigEx.MndFun.T :=
  (semAt_mndModel_T T z _).trans (congr((T : C ⥤ C).map $(semAt_mndModel_trtgt_mu T z)) =≫ _)

/-- `semAt` on `trtgt .eta` (i.e. `T(x)`) for the monad model evaluates to the action cell. -/
lemma semAt_mndModel_trtgt_eta
    (z : ((MndEx.model T).sigObj (LaxEx.oneSig SigEx.mndSig) : Type (max u v))) :
    semAt (MndEx.model T) z ((SigEx.mndSig.trtgt SigEx.MndTr.eta).subst
      (LaxEx.subS SigEx.mndSig SigEx.MndTr.eta)) = Ins.cell z SigEx.MndFun.T :=
  semAt_mndModel_trtgt_mu T z

/-- `semAt` on `trsrc .eta` (i.e. `x`) for the monad model evaluates to `𝟙 x`. -/
lemma semAt_mndModel_trsrc_eta
    (z : ((MndEx.model T).sigObj (LaxEx.oneSig SigEx.mndSig) : Type (max u v))) :
    semAt (MndEx.model T) z ((SigEx.mndSig.trsrc SigEx.MndTr.eta).subst
      (LaxEx.subS SigEx.mndSig SigEx.MndTr.eta)) = 𝟙 (Ins.pt z ()) := rfl

end MndSemAt

section MonSemAt

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]

/-- `semAt` on `x ⊗ x` for `LaxLimit.monModel C` evaluates to the multiplication cell. -/
lemma semAt_monModel_tens_var_var
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z (SigEx.monTens (Trm.var ()) (Trm.var ())) =
      Ins.cell z SigEx.MonFun.tens :=
  (semAt_monModel_tens z _).trans
    ((id_tensorHom_id (C := C) (Ins.pt z ()) (Ins.pt z ()) =≫ _).trans (Category.id_comp _))

/-- `semAt` on `trtgt .assoc` (i.e. `x ⊗ (x ⊗ x)`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trtgt_assoc
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.assoc).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.assoc)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.tens) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_monModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C) (𝟙 (Ins.pt z ()))
        $(semAt_monModel_tens_var_var z))).trans
      (id_tensorHom (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.tens))) =≫ _)

/-- `semAt` on `trsrc .assoc` (i.e. `(x ⊗ x) ⊗ x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trsrc_assoc
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.assoc).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.assoc)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.tens) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_monModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C)
        $(semAt_monModel_tens_var_var z) (𝟙 (Ins.pt z ())))).trans
      (tensorHom_id (C := C) (Ins.cell z SigEx.MonFun.tens) (Ins.pt z ()))) =≫ _)

/-- `semAt` on `trtgt .assocInv` (i.e. `(x ⊗ x) ⊗ x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trtgt_assocInv
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.assocInv).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.assocInv)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.tens) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_monModel_trsrc_assoc z

/-- `semAt` on `trsrc .assocInv` (i.e. `x ⊗ (x ⊗ x)`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trsrc_assocInv
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.assocInv).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.assocInv)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.tens) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_monModel_trtgt_assoc z

/-- `semAt` on `trtgt .lunit` (i.e. `x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trtgt_lunit
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.lunit).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.lunit)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trsrc .lunit` (i.e. `I ⊗ x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trsrc_lunit
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.lunit).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.lunit)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.unit) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_monModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C)
        $(semAt_monModel_unit z (fun i => i.elim0)) (𝟙 (Ins.pt z ())))).trans
      (tensorHom_id (C := C) (Ins.cell z SigEx.MonFun.unit) (Ins.pt z ()))) =≫ _)

/-- `semAt` on `trtgt .lunitInv` (i.e. `I ⊗ x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trtgt_lunitInv
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.lunitInv).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.lunitInv)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.unit) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_monModel_trsrc_lunit z

/-- `semAt` on `trsrc .lunitInv` (i.e. `x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trsrc_lunitInv
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.lunitInv).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.lunitInv)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trtgt .runit` (i.e. `x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trtgt_runit
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.runit).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.runit)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trsrc .runit` (i.e. `x ⊗ I`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trsrc_runit
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.runit).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.runit)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.unit) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_monModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C) (𝟙 (Ins.pt z ()))
        $(semAt_monModel_unit z (fun i => i.elim0)))).trans
      (id_tensorHom (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.unit))) =≫ _)

/-- `semAt` on `trtgt .runitInv` (i.e. `x ⊗ I`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trtgt_runitInv
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.runitInv).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.runitInv)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.unit) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_monModel_trsrc_runit z

/-- `semAt` on `trsrc .runitInv` (i.e. `x`) for `LaxLimit.monModel C`. -/
lemma semAt_monModel_trsrc_runitInv
    (z : ((LaxLimit.monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))) :
    semAt (LaxLimit.monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.runitInv).subst
      (LaxEx.subS SigEx.monSig SigEx.MonTr.runitInv)) = 𝟙 (Ins.pt z ()) := rfl

end MonSemAt

section SMonSemAt

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- `semAt` on `x ⊗ x` for `Loc.smonModel C` evaluates to the multiplication cell. -/
lemma semAt_smonModel_tens_var_var
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z (SigEx.monTens (Trm.var ()) (Trm.var ())) =
      Ins.cell z SigEx.MonFun.tens :=
  (semAt_smonModel_tens z _).trans
    ((id_tensorHom_id (C := C) (Ins.pt z ()) (Ins.pt z ()) =≫ _).trans (Category.id_comp _))

/-- `semAt` on `trtgt .assoc` (i.e. `x ⊗ (x ⊗ x)`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_assoc
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.assoc).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assoc)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.tens) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_smonModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C) (𝟙 (Ins.pt z ()))
        $(semAt_smonModel_tens_var_var z))).trans
      (id_tensorHom (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.tens))) =≫ _)

/-- `semAt` on `trsrc .assoc` (i.e. `(x ⊗ x) ⊗ x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_assoc
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.assoc).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assoc)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.tens) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_smonModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C)
        $(semAt_smonModel_tens_var_var z) (𝟙 (Ins.pt z ())))).trans
      (tensorHom_id (C := C) (Ins.cell z SigEx.MonFun.tens) (Ins.pt z ()))) =≫ _)

/-- `semAt` on `trtgt .assocInv` (i.e. `(x ⊗ x) ⊗ x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_assocInv
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.assocInv).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assocInv)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.tens) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_smonModel_trsrc_assoc z

/-- `semAt` on `trsrc .assocInv` (i.e. `x ⊗ (x ⊗ x)`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_assocInv
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.assocInv).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assocInv)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.tens) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_smonModel_trtgt_assoc z

/-- `semAt` on `trtgt .lunit` (i.e. `x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_lunit
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.lunit).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunit)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trsrc .lunit` (i.e. `I ⊗ x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_lunit
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.lunit).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunit)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.unit) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_smonModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C)
        $(semAt_smonModel_unit z (fun i => i.elim0)) (𝟙 (Ins.pt z ())))).trans
      (tensorHom_id (C := C) (Ins.cell z SigEx.MonFun.unit) (Ins.pt z ()))) =≫ _)

/-- `semAt` on `trtgt .lunitInv` (i.e. `I ⊗ x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_lunitInv
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.lunitInv).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunitInv)) =
      MonoidalCategoryStruct.whiskerRight (C := C) (Ins.cell z SigEx.MonFun.unit) (Ins.pt z ()) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_smonModel_trsrc_lunit z

/-- `semAt` on `trsrc .lunitInv` (i.e. `x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_lunitInv
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.lunitInv).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunitInv)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trtgt .runit` (i.e. `x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_runit
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.runit).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runit)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trsrc .runit` (i.e. `x ⊗ I`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_runit
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.runit).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runit)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.unit) ≫
        Ins.cell z SigEx.MonFun.tens :=
  (semAt_smonModel_tens z _).trans
    (((congr(MonoidalCategoryStruct.tensorHom (C := C) (𝟙 (Ins.pt z ()))
        $(semAt_smonModel_unit z (fun i => i.elim0)))).trans
      (id_tensorHom (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.unit))) =≫ _)

/-- `semAt` on `trtgt .runitInv` (i.e. `x ⊗ I`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_runitInv
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.runitInv).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runitInv)) =
      MonoidalCategoryStruct.whiskerLeft (C := C) (Ins.pt z ()) (Ins.cell z SigEx.MonFun.unit) ≫
        Ins.cell z SigEx.MonFun.tens :=
  semAt_smonModel_trsrc_runit z

/-- `semAt` on `trsrc .runitInv` (i.e. `x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_runitInv
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.runitInv).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runitInv)) = 𝟙 (Ins.pt z ()) := rfl

/-- `semAt` on `trtgt .sym` (i.e. `x ⊗ x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trtgt_sym
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.sym).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.sym)) = Ins.cell z SigEx.MonFun.tens :=
  semAt_smonModel_tens_var_var z

/-- `semAt` on `trsrc .sym` (i.e. `x ⊗ x`) for `Loc.smonModel C`. -/
lemma semAt_smonModel_trsrc_sym
    (z : ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))) :
    semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.sym).subst
      (LaxEx.subS SigEx.smonSig SigEx.SMonTr.sym)) = Ins.cell z SigEx.MonFun.tens :=
  semAt_smonModel_tens_var_var z

end SMonSemAt

end UlmerBialgebras.Paper.LaxLimit.Internal
