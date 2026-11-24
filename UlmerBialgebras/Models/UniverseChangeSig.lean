module

public import UlmerBialgebras.Models.UniverseChange

/-!
# Change of universe for the objects of operations and of bialgebras

The second part of `UlmerBialgebras/Models/UniverseChange.lean`: the change of universe
`Cat.{v, max u v} → Cat.{max u v, max u v}` on the object of operations `M^σ` and on the
equifier condition defining `M^T`, for the lifted model `UlmerBialgebras.UnivChange.upModel`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], §3
-/

@[expose] public section

universe w v u u₁ u₂ u₃

namespace UlmerBialgebras.UnivChange

open CategoryTheory
open scoped CategoryTheory.Bicategory

variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-! ## The object of operations -/

namespace Model

variable (M : Model Sg Cat.{v, max u v}) (sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg)


/-- The comparison `Ψ : (upModel M)^σ → up(M^σ)` of the objects of operations. -/
def sigDown : (upModel.{v, u} M).sigObj sg ⟶ upCat.{v, u} (M.sigObj sg) :=
  (insMap (F := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G := ((upModel.{v, u} M).codCell sg).toFunctor)
    (piUpS.{v, u} _).toFunctor (piUpS.{v, u} _).toFunctor
    (Cat.Hom.ext_iff.mp (upModel_domCell.{v, u} M sg))
    (Cat.Hom.ext_iff.mp (upModel_codCell.{v, u} M sg)) ⋙
    insDown.{v, u} (M.domCell sg) (M.codCell sg)).toCatHom

/-- `Ψ` commutes with the forgetful 1-cells to the products of the sorts. -/
lemma sigDown_u :
    sigDown M sg ≫ upHom (M.u sg) = (upModel.{v, u} M).u sg ≫ piUpS.{v, u} _ := rfl


/-- The domain 1-cell of the lifted model corresponds, via `piDownS`, to the lift of the domain
1-cell of `M`. -/
lemma upModel_domCell' :
    piDownS.{v, u} _ ≫ (upModel.{v, u} M).domCell sg = upHom (M.domCell sg) ≫ piDownS.{v, u} _ :=
  congr(piDownS.{v, u} _ ≫ $(upModel_domCell M sg) ≫ piDownS.{v, u} _)

/-- The codomain 1-cell of the lifted model corresponds, via `piDownS`, to the lift of the codomain
1-cell of `M`. -/
lemma upModel_codCell' :
    piDownS.{v, u} _ ≫ (upModel.{v, u} M).codCell sg = upHom (M.codCell sg) ≫ piDownS.{v, u} _ :=
  congr(piDownS.{v, u} _ ≫ $(upModel_codCell M sg) ≫ piDownS.{v, u} _)

/-- The inverse comparison `up(M^σ) → (upModel M)^σ` of the objects of operations. -/
def sigUp : upCat.{v, u} (M.sigObj sg) ⟶ (upModel.{v, u} M).sigObj sg :=
  (insUp.{v, u} (M.domCell sg) (M.codCell sg) ⋙
    insMap (F := (upHom (M.domCell sg)).toFunctor) (G := (upHom (M.codCell sg)).toFunctor)
      (F' := ((upModel.{v, u} M).domCell sg).toFunctor)
      (G' := ((upModel.{v, u} M).codCell sg).toFunctor)
      (piDownS.{v, u} _).toFunctor (piDownS.{v, u} _).toFunctor
      (Cat.Hom.ext_iff.mp (upModel_domCell' M sg).symm)
      (Cat.Hom.ext_iff.mp (upModel_codCell' M sg).symm)).toCatHom

/-- On objects, `Ψ` is a left inverse of the inverse comparison `sigUp`. -/
lemma sigDown_sigUp_obj (y : upCat.{v, u} (M.sigObj sg)) :
    (sigDown M sg).toFunctor.obj ((sigUp M sg).toFunctor.obj y) = y := by
  refine Ins.obj_ext_of_conjEq (F := (M.domCell sg).toFunctor) (G := (M.codCell sg).toFunctor)
    rfl ?_
  have c₁ := conjEq_map (downFunctor _) (insMap_cell_conjEq
    (F := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G := ((upModel.{v, u} M).codCell sg).toFunctor)
    (piUpS.{v, u} _).toFunctor (piUpS.{v, u} _).toFunctor
    (Cat.Hom.ext_iff.mp (upModel_domCell.{v, u} M sg))
    (Cat.Hom.ext_iff.mp (upModel_codCell.{v, u} M sg)) ((sigUp M sg).toFunctor.obj y))
  have c₂ := insMap_cell_conjEq (F := (upHom (M.domCell sg)).toFunctor)
    (G := (upHom (M.codCell sg)).toFunctor)
    (F' := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G' := ((upModel.{v, u} M).codCell sg).toFunctor)
    (piDownS.{v, u} _).toFunctor (piDownS.{v, u} _).toFunctor
    (Cat.Hom.ext_iff.mp (upModel_domCell' M sg).symm)
    (Cat.Hom.ext_iff.mp (upModel_codCell' M sg).symm)
    ((insUp (M.domCell sg) (M.codCell sg)).obj y)
  exact (c₁.trans (conjEq_map ((piUpS.{v, u} _).toFunctor ⋙ downFunctor _) c₂)).trans
    (ConjEq.of_eq rfl)

/-- On objects, the inverse comparison `sigUp` is a left inverse of `Ψ`. -/
lemma sigUp_sigDown_obj (z : (upModel.{v, u} M).sigObj sg) :
    (sigUp M sg).toFunctor.obj ((sigDown M sg).toFunctor.obj z) = z := by
  refine Ins.obj_ext_of_conjEq (F := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G := ((upModel.{v, u} M).codCell sg).toFunctor) rfl ?_
  have c₁ := insMap_cell_conjEq (F := (upHom (M.domCell sg)).toFunctor)
    (G := (upHom (M.codCell sg)).toFunctor)
    (F' := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G' := ((upModel.{v, u} M).codCell sg).toFunctor)
    (piDownS.{v, u} _).toFunctor (piDownS.{v, u} _).toFunctor
    (Cat.Hom.ext_iff.mp (upModel_domCell' M sg).symm)
    (Cat.Hom.ext_iff.mp (upModel_codCell' M sg).symm)
    ((insUp (M.domCell sg) (M.codCell sg)).obj ((sigDown M sg).toFunctor.obj z))
  have c₂ := conjEq_map (piDownS.{v, u} _).toFunctor (insMap_cell_conjEq
    (F := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G := ((upModel.{v, u} M).codCell sg).toFunctor)
    (piUpS.{v, u} _).toFunctor (piUpS.{v, u} _).toFunctor
    (Cat.Hom.ext_iff.mp (upModel_domCell.{v, u} M sg))
    (Cat.Hom.ext_iff.mp (upModel_codCell.{v, u} M sg)) z)
  exact (c₁.trans c₂).trans (ConjEq.of_eq rfl)

/-- `Ψ` is an isomorphism of categories: one composite. -/
lemma sigUp_sigDown : sigUp M sg ≫ sigDown M sg = 𝟙 _ := by
  refine Cat.Hom.ext (CategoryTheory.Functor.ext (sigDown_sigUp_obj M sg) (fun y y' f => ?_))
  apply ULift.ext
  apply Ins.hom_ext
  refine Eq.trans ?_ (uliftIns_conj_base _ _ _).symm
  exact eq_conj_eqToHom_self _ _ _

/-- `Ψ` is an isomorphism of categories: the other composite. -/
lemma sigDown_sigUp : sigDown M sg ≫ sigUp M sg = 𝟙 _ := by
  refine Cat.Hom.ext (CategoryTheory.Functor.ext (sigUp_sigDown_obj M sg) (fun z z' f => ?_))
  apply Ins.hom_ext
  refine Eq.trans ?_ (ins_conj_base _ _ _).symm
  exact eq_conj_eqToHom_self _ _ _

/-- The closed terms evaluated on `(upModel M)^σ` are the lifted closed terms evaluated on `M^σ`,
after `Ψ`. -/
lemma upModel_sigTm {c : Sg.Cat} (t : sg.CTrm c) :
    (upModel.{v, u} M).sigTm sg t = sigDown M sg ≫ upHom (M.sigTm sg t) := by
  rw [UlmerBialgebras.Model.sigTm_eq, UlmerBialgebras.Model.sigTm_eq, upModel_tm]
  rfl

/-- The objects of `(upModel M)^σ(t)` and of `M^σ(t)` at `Ψ z` agree. -/
lemma upModel_sigTm_obj {c : Sg.Cat} (t : sg.CTrm c) (z : (upModel.{v, u} M).sigObj sg) :
    ((upModel.{v, u} M).sigTm sg t).toFunctor.obj z =
      (upHom (M.sigTm sg t)).toFunctor.obj ((sigDown M sg).toFunctor.obj z) :=
  Functor.congr_obj (Cat.Hom.ext_iff.mp (upModel_sigTm M sg t)) z

/-- The lift of a component of a 2-cell of `M` at `Ψ z`, as a morphism of the lifted category. -/
abbrev upApp {c : Sg.Cat} {t t' : sg.CTrm c} (y : M.sigTm sg t ⟶ M.sigTm sg t')
    (z : (upModel.{v, u} M).sigObj sg) :
    (upHom (M.sigTm sg t)).toFunctor.obj ((sigDown M sg).toFunctor.obj z) ⟶
      (upHom (M.sigTm sg t')).toFunctor.obj ((sigDown M sg).toFunctor.obj z) :=
  (upFunctor _).map (y.toNatTrans.app ((sigDown M sg).toFunctor.obj z))

/-- A 2-cell between evaluated closed terms of the lifted model agrees with a 2-cell of `M`
componentwise, up to `eqToHom`s. -/
def CellComp {c : Sg.Cat} {t t' : sg.CTrm c}
    (x : (upModel.{v, u} M).sigTm sg t ⟶ (upModel.{v, u} M).sigTm sg t')
    (y : M.sigTm sg t ⟶ M.sigTm sg t') : Prop :=
  ∀ z, ConjEq (x.toNatTrans.app z) (upApp M sg y z)

/-- Componentwise agreement `CellComp` of 2-cells is compatible with composition. -/
lemma CellComp.comp {c : Sg.Cat} {t t' t'' : sg.CTrm c}
    {x : (upModel.{v, u} M).sigTm sg t ⟶ (upModel.{v, u} M).sigTm sg t'}
    {x' : (upModel.{v, u} M).sigTm sg t' ⟶ (upModel.{v, u} M).sigTm sg t''}
    {y : M.sigTm sg t ⟶ M.sigTm sg t'} {y' : M.sigTm sg t' ⟶ M.sigTm sg t''}
    (h : CellComp M sg x y) (h' : CellComp M sg x' y') : CellComp M sg (x ≫ x') (y ≫ y') :=
  fun z => (h z).comp (h' z)


/-- The arrow of a function symbol: the lifted model and `M` agree. -/
lemma cellComp_fn (f : sg.Fn) :
    CellComp M sg ((upModel.{v, u} M).arrCell sg (OneSig.Arr.fn f))
      (M.arrCell sg (OneSig.Arr.fn f)) := by
  intro z
  rw [UlmerBialgebras.Model.arrCell_fn, UlmerBialgebras.Model.arrCell_fn]
  refine (conjEq_app _ _ _ z).trans ?_
  refine ConjEq.symm ((conjEq_map (upFunctor _) (conjEq_app _ _ _ _)).trans ?_)
  have key := conjEq_down_proj (insMap_cell_conjEq (F := ((upModel.{v, u} M).domCell sg).toFunctor)
    (G := ((upModel.{v, u} M).codCell sg).toFunctor)
    (piUpS.{v, u} _).toFunctor (piUpS.{v, u} _).toFunctor
    (Cat.Hom.ext_iff.mp (upModel_domCell.{v, u} M sg))
    (Cat.Hom.ext_iff.mp (upModel_codCell.{v, u} M sg)) z) f
  exact (conjEq_map (upFunctor _) key).trans (ConjEq.of_eq rfl)


/-- The lift of the environment of a transformation symbol, in the lifted model. -/
lemma upModel_lift_env (a : Sg.Tr) (sub : ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i)) :
    ((upModel.{v, u} M).Pctx a).lift (fun i => (upModel.{v, u} M).sigTm sg (sub i)) ≫
        piUp.{v, u} _ =
      sigDown M sg ≫ upHom ((M.Pctx a).lift (fun i => M.sigTm sg (sub i))) := by
  rw [show (fun i => (upModel.{v, u} M).sigTm sg (sub i)) =
    fun i => sigDown M sg ≫ upHom (M.sigTm sg (sub i)) from funext fun i => upModel_sigTm M sg _]
  exact lift_piUp _ (sigDown M sg) _

/-- The arrow of a transformation symbol: the lifted model and `M` agree. -/
lemma cellComp_tr (a : Sg.Tr) (sub : ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i)) :
    CellComp M sg ((upModel.{v, u} M).arrCell sg (OneSig.Arr.tr a sub))
      (M.arrCell sg (OneSig.Arr.tr a sub)) := by
  intro z
  rw [UlmerBialgebras.Model.arrCell_tr, UlmerBialgebras.Model.arrCell_tr]
  refine (conjEq_app _ _ _ z).trans ?_
  refine ConjEq.symm ((conjEq_map (upFunctor _) (conjEq_app _ _ _ _)).trans ?_)
  unfold UlmerBialgebras.Model.trAt
  refine ConjEq.symm ((conjEq_app _ _ _ z).trans ?_)
  refine ConjEq.symm ((conjEq_map (upFunctor _) (conjEq_app _ _ _ _)).trans ?_)
  rw [Cat.whiskerLeft_app]
  refine ConjEq.trans ?_ (upModel_tr_app M a _).symm
  exact ((conjEq_app_congr (upCell (M.tr a))
    (Functor.congr_obj (Cat.Hom.ext_iff.mp (upModel_lift_env M sg a sub)) z)).trans
    (ConjEq.of_eq rfl)).symm


/-- The arrow of a functor symbol applied to an arrow `g` in argument `i`: the lifted model and
`M` agree if they agree on `g`. -/
lemma cellComp_app (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
    (hne : ∀ j, j ≠ i → args j = args' j) (g : sg.Arr (args i) (args' i))
    (ih : CellComp M sg ((upModel.{v, u} M).arrCell sg g) (M.arrCell sg g)) :
    CellComp M sg ((upModel.{v, u} M).arrCell sg (OneSig.Arr.app B i args args' hne g))
      (M.arrCell sg (OneSig.Arr.app B i args args' hne g)) := by
  intro z
  rw [UlmerBialgebras.Model.arrCell_app, UlmerBialgebras.Model.arrCell_app]
  unfold PreModel.appCell
  refine (conjEq_map (upFunctor _) (conjEq_map (M.fn B).toFunctor
    (conjEq_pi fun j => ?_))).trans (ConjEq.of_eq rfl)
  refine (conjEq_map (downFunctor _) (conjEq_app _ _ _ z)).trans ?_
  refine ConjEq.symm ((conjEq_app _ _ _ _).trans ?_)
  by_cases hj : j = i
  · subst hj
    simp only [dite_true, cast_eq]
    exact (conjEq_map (downFunctor _) (ih z)).symm
  · simp only [dite_eq_right hj]
    rw [Cat.eqToHom_app]
    exact (conjEq_eqToHom_app _ _ _
      congr((downFunctor _).obj $(upModel_sigTm_obj M sg (args j) z)).symm).trans
      (ConjEq.of_eq (eqToHom_map (downFunctor _) _)).symm


/-- **The arrows of the term graph**: the lifted model and `M` agree. -/
lemma cellComp_arr {c : Sg.Cat} {t t' : sg.CTrm c} (g : sg.Arr t t') :
    CellComp M sg ((upModel.{v, u} M).arrCell sg g) (M.arrCell sg g) := by
  induction g with
  | fn f => exact cellComp_fn M sg f
  | tr a sub => exact cellComp_tr M sg a sub
  | app B i args args' hne g ih => exact cellComp_app M sg B i args args' hne g ih

/-- **The paths of the term graph**: the lifted model and `M` agree. -/
lemma cellComp_path {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    CellComp M sg ((upModel.{v, u} M).pathCell sg p) (M.pathCell sg p) := by
  induction p with
  | nil t =>
    intro z
    rw [UlmerBialgebras.Model.pathCell_nil, UlmerBialgebras.Model.pathCell_nil]
    exact ConjEq.eqToHom_eqToHom (Y := ((upModel.{v, u} M).sigTm sg t).toFunctor.obj z) rfl rfl
      (upModel_sigTm_obj M sg t z) |>.trans (ConjEq.of_eq rfl)
  | cons g p ih =>
    rw [UlmerBialgebras.Model.pathCell_cons, UlmerBialgebras.Model.pathCell_cons]
    exact (cellComp_arr M sg g).comp M sg ih

end Model


/-! ## The equifier condition -/

section Equif

variable {Sg : TwoSig.{u₁, u₂, u₃}} {sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg}

/-- In `CAT`, an object of `N^σ` satisfies the equations of `T` iff the two paths of each
equation agree at it. -/
lemma lhsCell_app_eq_iff (N : Model Sg Cat.{v, max u v}) (T : Theory.{u₁, u₂, u₃, 0, 0, 0} sg)
    (y : N.sigObj sg) :
    (N.lhsCell sg T).toNatTrans.app y = (N.rhsCell sg T).toNatTrans.app y ↔
      ∀ r, (N.pathCell sg (T.lhs r)).toNatTrans.app y =
        (N.pathCell sg (T.rhs r)).toNatTrans.app y := by
  refine funext_iff.trans (forall_congr' fun r => ?_)
  change (eqToHom _ ≫ N.pathCell sg (T.lhs r) ≫ eqToHom _).toNatTrans.app y =
    (eqToHom _ ≫ N.pathCell sg (T.rhs r) ≫ eqToHom _).toNatTrans.app y ↔ _
  simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, cancel_epi, cancel_mono]

end Equif


namespace Model

variable (M : Model Sg Cat.{v, max u v}) (sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg)
  (T : Theory.{u₁, u₂, u₃, 0, 0, 0} sg)

/-- **The equations of `T`**: an object of `(upModel M)^σ` satisfies them iff its image under
`Ψ` does. -/
lemma upModel_lhsCell_app_eq_iff (z : (upModel.{v, u} M).sigObj sg) :
    ((upModel.{v, u} M).lhsCell sg T).toNatTrans.app z =
        ((upModel.{v, u} M).rhsCell sg T).toNatTrans.app z ↔
      (M.lhsCell sg T).toNatTrans.app ((sigDown M sg).toFunctor.obj z) =
        (M.rhsCell sg T).toNatTrans.app ((sigDown M sg).toFunctor.obj z) := by
  refine (lhsCell_app_eq_iff (upModel.{v, u} M) T z).trans
    ((forall_congr' fun r => ?_).trans (lhsCell_app_eq_iff M T _).symm)
  refine ((cellComp_path M sg (T.lhs r) z).eq_iff (cellComp_path M sg (T.rhs r) z)).trans ?_
  exact ULift.up_inj


/-- The comparison `(upModel M)^T → up(M^T)` of the objects of `T`-bialgebras. -/
def thyDown : (upModel.{v, u} M).thyObj sg T ⟶ upCat.{v, u} (M.thyObj sg T) :=
  Functor.toCatHom
    { obj := fun w =>
        (⟨(sigDown M sg).toFunctor.obj
            (w : Equif ((upModel.{v, u} M).lhsCell sg T).toNatTrans
              ((upModel.{v, u} M).rhsCell sg T).toNatTrans).obj,
          (upModel_lhsCell_app_eq_iff M sg T _).1
            (w : Equif ((upModel.{v, u} M).lhsCell sg T).toNatTrans
              ((upModel.{v, u} M).rhsCell sg T).toNatTrans).property⟩ :
          Equif (M.lhsCell sg T).toNatTrans (M.rhsCell sg T).toNatTrans)
      map := fun f => ULift.up ⟨((sigDown M sg).toFunctor.map f.hom).down⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }

/-- The comparison of the objects of `T`-bialgebras commutes with the forgetful 1-cells. -/
lemma thyDown_e : thyDown M sg T ≫ upHom (M.e sg T) = (upModel.{v, u} M).e sg T ≫ sigDown M sg :=
  rfl


/-- Transport of the equations of `T` at an object of `up(M^σ)` along an equality of objects. -/
lemma equif_transport {x y : upCat.{v, u} (M.sigObj sg)} (e : x = y)
    (h : (M.lhsCell sg T).toNatTrans.app y = (M.rhsCell sg T).toNatTrans.app y) :
    (M.lhsCell sg T).toNatTrans.app x = (M.rhsCell sg T).toNatTrans.app x := by
  subst e; exact h

/-- The inverse comparison `up(M^T) → (upModel M)^T`. -/
def thyUp : upCat.{v, u} (M.thyObj sg T) ⟶ (upModel.{v, u} M).thyObj sg T :=
  Functor.toCatHom
    { obj := fun w =>
        (⟨(sigUp M sg).toFunctor.obj
            (w : Equif (M.lhsCell sg T).toNatTrans (M.rhsCell sg T).toNatTrans).obj,
          (upModel_lhsCell_app_eq_iff M sg T _).2
            (equif_transport M sg T (sigDown_sigUp_obj M sg _)
              (w : Equif (M.lhsCell sg T).toNatTrans (M.rhsCell sg T).toNatTrans).property)⟩ :
          Equif ((upModel.{v, u} M).lhsCell sg T).toNatTrans
            ((upModel.{v, u} M).rhsCell sg T).toNatTrans)
      map := fun f => ⟨(sigUp M sg).toFunctor.map (ULift.up f.down.hom)⟩
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }

/-- The inverse comparison `thyUp` commutes with the 1-cells `e` to the objects of operations. -/
lemma thyUp_e : thyUp M sg T ≫ (upModel.{v, u} M).e sg T = upHom (M.e sg T) ≫ sigUp M sg :=
  rfl


/-- The comparison of the objects of `T`-bialgebras is an isomorphism of categories: one
composite. -/
lemma thyUp_thyDown : thyUp M sg T ≫ thyDown M sg T = 𝟙 _ := by
  refine Cat.Hom.ext (CategoryTheory.Functor.ext
    (fun w => ObjectProperty.FullSubcategory.ext (sigDown_sigUp_obj M sg _))
    (fun w w' f => ?_))
  apply ULift.ext
  apply InducedCategory.hom_ext
  apply Ins.hom_ext
  refine Eq.trans ?_ (uliftEquifIns_conj_base _ _ _).symm
  exact eq_conj_eqToHom_self _ _ _

/-- The comparison of the objects of `T`-bialgebras is an isomorphism of categories: the other
composite. -/
lemma thyDown_thyUp : thyDown M sg T ≫ thyUp M sg T = 𝟙 _ := by
  refine Cat.Hom.ext (CategoryTheory.Functor.ext
    (fun w => ObjectProperty.FullSubcategory.ext (sigUp_sigDown_obj M sg _))
    (fun w w' f => ?_))
  apply InducedCategory.hom_ext
  apply Ins.hom_ext
  refine Eq.trans ?_ (equifIns_conj_base _ _ _).symm
  exact eq_conj_eqToHom_self _ _ _

/-- **The universe-change transport.** For a Σ-model `M` in `Cat.{v, max u v}`, the object of
`T`-bialgebras of the lifted model `upModel M` is isomorphic, as a category, to the change of
universe of the object of `T`-bialgebras of `M`, compatibly with the forgetful 1-cells to the
products of the sorts. -/
def thyIso : (upModel.{v, u} M).thyObj sg T ≅ upCat.{v, u} (M.thyObj sg T) where
  hom := thyDown M sg T
  inv := thyUp M sg T
  hom_inv_id := thyDown_thyUp M sg T
  inv_hom_id := thyUp_thyDown M sg T

/-- The comparison `thyDown` commutes with the forgetful 1-cells `U = e ≫ u`. -/
lemma thyDown_forget :
    thyDown M sg T ≫ upHom (M.e sg T ≫ M.u sg) =
      ((upModel.{v, u} M).e sg T ≫ (upModel.{v, u} M).u sg) ≫ piUpS.{v, u} _ := by
  rw [upHom_comp, ← Category.assoc, thyDown_e, Category.assoc, sigDown_u]
  exact (Category.assoc _ _ _).symm

/-- The transport isomorphism commutes with the forgetful 1-cells `U = e ≫ u`. -/
lemma thyIso_hom_forget :
    (thyIso M sg T).hom ≫ upHom (M.e sg T ≫ M.u sg) =
      ((upModel.{v, u} M).e sg T ≫ (upModel.{v, u} M).u sg) ≫ piUpS.{v, u} _ :=
  thyDown_forget M sg T

end Model


/-! ## Transfer of 1-cells between objects of `T`-bialgebras -/

section Transfer

variable {X Y : Cat.{v, max u v}}

/-- A 1-cell between lifted categories, as a 1-cell between the categories. -/
def downHom (G : upCat.{v, u} X ⟶ upCat.{v, u} Y) : X ⟶ Y :=
  (upFunctor X ⋙ G.toFunctor ⋙ downFunctor Y).toCatHom

/-- The descent of the lift of a 1-cell is the 1-cell. -/
lemma downHom_upHom (F : X ⟶ Y) : downHom (upHom F) = F := rfl

/-- The lift of the descent of a 1-cell between lifted categories is the 1-cell. -/
lemma upHom_downHom (G : upCat.{v, u} X ⟶ upCat.{v, u} Y) : upHom (downHom G) = G := rfl

/-- Lifting 1-cells to the lifted categories is injective. -/
lemma upHom_injective {F F' : X ⟶ Y} (h : upHom.{v, u} F = upHom F') : F = F' := by
  rw [← downHom_upHom F, h, downHom_upHom]

/-- The lift of a category is equivalent to it. -/
def upEquiv (C : Cat.{v, max u v}) : C ≌ upCat.{v, u} C where
  functor := upFunctor C
  inverse := downFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by
    simp only [Iso.refl_hom, NatTrans.id_app]
    exact Category.comp_id _

end Transfer

namespace Model

variable {Sg : TwoSig.{u₁, u₂, u₃}} {sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg}
  {T : Theory.{u₁, u₂, u₃, 0, 0, 0} sg} {N N' : Model Sg Cat.{v, max u v}}

/-- The inverse comparison `sigUp` commutes with the forgetful 1-cells to the products of the
sorts. -/
lemma sigUp_u : sigUp N sg ≫ (upModel.{v, u} N).u sg = upHom (N.u sg) ≫ piDownS.{v, u} _ :=
  rfl

/-- The inverse comparison `thyUp` commutes with the forgetful 1-cells `U = e ≫ u`. -/
lemma thyUp_forget :
    thyUp N sg T ≫ ((upModel.{v, u} N).e sg T ≫ (upModel.{v, u} N).u sg) =
      upHom (N.e sg T ≫ N.u sg) ≫ piDownS.{v, u} _ :=
  rfl

/-- The lift of a 1-cell between objects of `T`-bialgebras. -/
def upThy (L : N.thyObj sg T ⟶ N'.thyObj sg T) :
    (upModel.{v, u} N).thyObj sg T ⟶ (upModel.{v, u} N').thyObj sg T :=
  thyDown N sg T ≫ upHom L ≫ thyUp N' sg T

/-- The descent of a 1-cell between objects of `T`-bialgebras of lifted models. -/
def downThy (L : (upModel.{v, u} N).thyObj sg T ⟶ (upModel.{v, u} N').thyObj sg T) :
    N.thyObj sg T ⟶ N'.thyObj sg T :=
  downHom (thyUp N sg T ≫ L ≫ thyDown N' sg T)

/-- The descent of the lift of a 1-cell between objects of `T`-bialgebras is the 1-cell. -/
lemma downThy_upThy (L : N.thyObj sg T ⟶ N'.thyObj sg T) : downThy (upThy L) = L := by
  calc downThy (upThy L)
      = downHom ((thyUp N sg T ≫ thyDown N sg T) ≫ upHom L ≫
          (thyUp N' sg T ≫ thyDown N' sg T)) := rfl
    _ = L := by rw [thyUp_thyDown, thyUp_thyDown]; rfl

/-- The lift of the descent of a 1-cell between objects of `T`-bialgebras of lifted models is the
1-cell. -/
lemma upThy_downThy (L : (upModel.{v, u} N).thyObj sg T ⟶ (upModel.{v, u} N').thyObj sg T) :
    upThy (downThy L) = L := by
  calc upThy (downThy L)
      = (thyDown N sg T ≫ thyUp N sg T) ≫ L ≫ (thyDown N' sg T ≫ thyUp N' sg T) := rfl
    _ = L := by rw [thyDown_thyUp, thyDown_thyUp, Category.id_comp, Category.comp_id]

/-- The change of universe of a 1-cell between the products of the sorts. -/
def upP0 (φ : (N.P0 sg).pt ⟶ (N'.P0 sg).pt) :
    ((upModel.{v, u} N).P0 sg).pt ⟶ ((upModel.{v, u} N').P0 sg).pt :=
  piUpS.{v, u} _ ≫ upHom φ ≫ piDownS.{v, u} _

/-- The lift of a 1-cell over `φ` is over the lift of `φ`. -/
lemma upThy_forget {L : N.thyObj sg T ⟶ N'.thyObj sg T} {φ : (N.P0 sg).pt ⟶ (N'.P0 sg).pt}
    (h : L ≫ (N'.e sg T ≫ N'.u sg) = (N.e sg T ≫ N.u sg) ≫ φ) :
    upThy L ≫ ((upModel.{v, u} N').e sg T ≫ (upModel.{v, u} N').u sg) =
      ((upModel.{v, u} N).e sg T ≫ (upModel.{v, u} N).u sg) ≫ upP0 φ := by
  have h₂ : thyDown N sg T ≫ upHom (L ≫ (N'.e sg T ≫ N'.u sg)) ≫ piDownS.{v, u} _ =
      thyDown N sg T ≫ upHom ((N.e sg T ≫ N.u sg) ≫ φ) ≫ piDownS.{v, u} _ := by rw [h]
  exact h₂

/-- A 1-cell is over `φ` if its lift is over the lift of `φ`. -/
lemma forget_of_upThy {L : N.thyObj sg T ⟶ N'.thyObj sg T} {φ : (N.P0 sg).pt ⟶ (N'.P0 sg).pt}
    (h : upThy L ≫ ((upModel.{v, u} N').e sg T ≫ (upModel.{v, u} N').u sg) =
      ((upModel.{v, u} N).e sg T ≫ (upModel.{v, u} N).u sg) ≫ upP0 φ) :
    L ≫ (N'.e sg T ≫ N'.u sg) = (N.e sg T ≫ N.u sg) ≫ φ := by
  apply upHom_injective
  have h₂ := congr(thyUp N sg T ≫ $h ≫ piUpS.{v, u} _)
  have h₃ : thyUp N sg T ≫ (upThy L ≫ ((upModel.{v, u} N').e sg T ≫
      (upModel.{v, u} N').u sg)) ≫ piUpS.{v, u} _ =
        (thyUp N sg T ≫ thyDown N sg T) ≫ upHom (L ≫ (N'.e sg T ≫ N'.u sg)) := rfl
  rw [thyUp_thyDown, Category.id_comp] at h₃
  exact h₃.symm.trans h₂


/-- The comparison of the objects of `T`-bialgebras, as an equivalence of categories. -/
def thyEquiv (N : Model Sg Cat.{v, max u v}) :
    ((upModel.{v, u} N).thyObj sg T : Type (max u v)) ≌ upCat.{v, u} (N.thyObj sg T) :=
  Cat.equivOfIso (thyIso N sg T)

instance (N : Model Sg Cat.{v, max u v}) : (thyDown N sg T).toFunctor.IsEquivalence :=
  (thyEquiv (sg := sg) (T := T) N).isEquivalence_functor

instance (N : Model Sg Cat.{v, max u v}) : (thyUp N sg T).toFunctor.IsEquivalence :=
  (thyEquiv (sg := sg) (T := T) N).isEquivalence_inverse

instance (C : Cat.{v, max u v}) : (upFunctor.{v, u} C).IsEquivalence :=
  (upEquiv C).isEquivalence_functor

instance (C : Cat.{v, max u v}) : (downFunctor.{v, u} C).IsEquivalence :=
  (upEquiv C).isEquivalence_inverse

/-- The functor underlying `upThy L` is the composite of `thyDown`, `downFunctor`, `L`, `upFunctor`
and `thyUp`. -/
lemma upThy_toFunctor (L : N.thyObj sg T ⟶ N'.thyObj sg T) :
    (upThy L).toFunctor = (thyDown N sg T).toFunctor ⋙ downFunctor _ ⋙ L.toFunctor ⋙
      upFunctor _ ⋙ (thyUp N' sg T).toFunctor :=
  rfl

/-- The functor underlying `downThy L` is the composite of `upFunctor`, `thyUp`, `L`, `thyDown` and
`downFunctor`. -/
lemma downThy_toFunctor
    (L : (upModel.{v, u} N).thyObj sg T ⟶ (upModel.{v, u} N').thyObj sg T) :
    (downThy L).toFunctor = upFunctor _ ⋙ (thyUp N sg T).toFunctor ⋙ L.toFunctor ⋙
      (thyDown N' sg T).toFunctor ⋙ downFunctor _ :=
  rfl

/-- The functor underlying `L` is the composite of `upFunctor`, `thyUp`, the functor underlying
`upThy L`, `thyDown` and `downFunctor`. -/
lemma toFunctor_eq_downThy_upThy (L : N.thyObj sg T ⟶ N'.thyObj sg T) :
    L.toFunctor = upFunctor _ ⋙ (thyUp N sg T).toFunctor ⋙ (upThy L).toFunctor ⋙
      (thyDown N' sg T).toFunctor ⋙ downFunctor _ := by
  conv_lhs => rw [← downThy_upThy L]
  exact downThy_toFunctor _

/-- A 1-cell preserves the colimits of a shape iff its lift does. -/
lemma preservesColimitsOfShape_upThy_iff (J : Type*) [Category J]
    (L : N.thyObj sg T ⟶ N'.thyObj sg T) :
    Limits.PreservesColimitsOfShape J (upThy L).toFunctor ↔
      Limits.PreservesColimitsOfShape J L.toFunctor := by
  constructor
  · intro
    rw [toFunctor_eq_downThy_upThy L]
    infer_instance
  · intro
    rw [upThy_toFunctor]
    infer_instance

/-- A 1-cell preserves the limits of a shape iff its lift does. -/
lemma preservesLimitsOfShape_upThy_iff (J : Type*) [Category J]
    (L : N.thyObj sg T ⟶ N'.thyObj sg T) :
    Limits.PreservesLimitsOfShape J (upThy L).toFunctor ↔
      Limits.PreservesLimitsOfShape J L.toFunctor := by
  constructor
  · intro
    rw [toFunctor_eq_downThy_upThy L]
    infer_instance
  · intro
    rw [upThy_toFunctor]
    infer_instance

/-- A morphism of `(upModel N)^T` is an isomorphism iff its image in `N^T` is. -/
lemma isIso_iff_thyDown {x y : (upModel.{v, u} N).thyObj sg T} (g : x ⟶ y) :
    IsIso g ↔ IsIso ((downFunctor _).map ((thyDown N sg T).toFunctor.map g)) := by
  constructor
  · intro; infer_instance
  · intro h
    have : IsIso ((thyDown N sg T).toFunctor.map g) :=
      (isIso_of_reflects_iso _ (downFunctor _) : _)
    exact isIso_of_reflects_iso g (thyDown N sg T).toFunctor

/-- A morphism of `N^T` is an isomorphism iff its image in `(upModel N)^T` is. -/
lemma isIso_iff_thyUp {x y : N.thyObj sg T} (f : x ⟶ y) :
    IsIso f ↔ IsIso ((thyUp N sg T).toFunctor.map ((upFunctor _).map f)) := by
  constructor
  · intro; infer_instance
  · intro h
    have : IsIso ((upFunctor _).map f) :=
      (isIso_of_reflects_iso _ (thyUp N sg T).toFunctor : _)
    exact isIso_of_reflects_iso f (upFunctor _)

/-- The lift of a 1-cell sends a morphism to an isomorphism iff the 1-cell sends its image to an
isomorphism. -/
lemma isIso_upThy_map_iff (L : N.thyObj sg T ⟶ N'.thyObj sg T)
    {x y : (upModel.{v, u} N).thyObj sg T} (g : x ⟶ y) :
    IsIso ((upThy L).toFunctor.map g) ↔
      IsIso (L.toFunctor.map ((downFunctor _).map ((thyDown N sg T).toFunctor.map g))) := by
  rw [upThy_toFunctor]
  simp only [Functor.comp_map]
  constructor
  · intro h
    have : IsIso ((upFunctor _).map (L.toFunctor.map ((downFunctor _).map
        ((thyDown N sg T).toFunctor.map g)))) :=
      (isIso_of_reflects_iso _ (thyUp N' sg T).toFunctor : _)
    exact isIso_of_reflects_iso _ (upFunctor _)
  · intro; infer_instance

/-- A morphism is an isomorphism iff its image under two functors that reflect isomorphisms is. -/
lemma isIso_map_map_iff {C D E : Type*} [Category C] [Category D] [Category E] (F : C ⥤ D)
    (G : D ⥤ E) [F.ReflectsIsomorphisms] [G.ReflectsIsomorphisms] {a b : C} (g : a ⟶ b) :
    IsIso (G.map (F.map g)) ↔ IsIso g :=
  ⟨fun _ => by
    have := isIso_of_reflects_iso (F.map g) G
    exact isIso_of_reflects_iso g F, fun _ => inferInstance⟩

/-- A 1-cell sends a morphism to an isomorphism iff its lift sends the image of the morphism to an
isomorphism. -/
lemma isIso_map_iff_upThy (L : N.thyObj sg T ⟶ N'.thyObj sg T) {x y : N.thyObj sg T}
    (f : x ⟶ y) :
    IsIso (L.toFunctor.map f) ↔
      IsIso ((upThy L).toFunctor.map ((thyUp N sg T).toFunctor.map ((upFunctor _).map f))) := by
  suffices ∀ G, G = upFunctor _ ⋙ (thyUp N sg T).toFunctor ⋙ (upThy L).toFunctor ⋙
      (thyDown N' sg T).toFunctor ⋙ downFunctor _ → (IsIso (G.map f) ↔
        IsIso ((upThy L).toFunctor.map ((thyUp N sg T).toFunctor.map ((upFunctor _).map f)))) from
    this _ (toFunctor_eq_downThy_upThy L)
  rintro G rfl
  simp only [Functor.comp_map]
  exact isIso_map_map_iff _ _ _

end Model

end UlmerBialgebras.UnivChange
