module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import UlmerBialgebras.Proofs.Sec3.LaxLimitCalc
public import UlmerBialgebras.Proofs.Sec3.CategoryIso

/-!
# Comparisons for the lax-limit theories

Construct the comparison functors for Examples 3.20 (4): the categories of lax-limit
bialgebras are compared with `T.Algebra`, `Mon C` and `CommMon C`. The defining conditions
are evaluated symbol by symbol, and explicit inverse functors satisfy the strict inverse
identities and commute with the forgetful functors to the base category.

## Main results

* `UlmerBialgebras.Paper.LaxLimit.Internal.MndCase.comparison`: the comparison functor from
  `M^{T_Lax}`, for the model of a monad `T`, to `T.Algebra`; `MndCase.inverseFunctor` is a strict
  inverse (`MndCase.comparison_comp_inverseFunctor`, `MndCase.inverseFunctor_comp_comparison`).
* `UlmerBialgebras.Paper.LaxLimit.Internal.MonCase.comparison`: the comparison functor from
  `M^{T_Lax}` to `Mon C`, with strict inverse `MonCase.inverseFunctor`.
* `UlmerBialgebras.Paper.LaxLimit.Internal.SMonCase.comparison`: the comparison functor from
  `M^{T_Lax}` to `CommMon C`, with strict inverse `SMonCase.inverseFunctor`.
* `UlmerBialgebras.Paper.LaxLimit.Internal.MonCase.comparison_comp_forget`: the comparison functor
  commutes with the forgetful functors to `C` (likewise `MndCase.comparison_comp_forget` and
  `SMonCase.comparison_comp_forget`).

The symmetric monoidal case (`SMonCase`) is in `UlmerBialgebras/Proofs/Sec3/LaxLimitEquivSMon.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.20
  (4)
* [R. Street, *Limits indexed by category-valued 2-functors*][streetLimitsIndexedCategoryvalued1976]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section


universe v u

namespace UlmerBialgebras.Paper.LaxLimit.Internal

open CategoryTheory MonoidalCategory

/-! ## Monads -/

namespace MndCase

variable {C : Type (max u v)} [Category.{v} C] (T : Monad C)

/-- The objects of `M^σ` for the lax-limit signature of `Σ_Mnd` and the model of `T`. -/
abbrev SigObj : Type (max u v) :=
  ((MndEx.model T).sigObj (LaxEx.oneSig SigEx.mndSig) : Type (max u v))

variable {T}

/-- The underlying object of an object of `M^σ`. -/
def ob (z : SigObj T) : C := Ins.pt z ()

/-- The structure map `T x ⟶ x` of an object of `M^σ`. -/
def act (z : SigObj T) : (T : C ⥤ C).obj (ob z) ⟶ ob z := Ins.cell z SigEx.MndFun.T

/-- The monad model interprets multiplication by the multiplication cell. -/
@[simp] lemma model_tr_mu : (MndEx.model T).tr SigEx.MndTr.mu = MndEx.muCell T := rfl

/-- The monad model interprets the unit by the unit cell. -/
@[simp] lemma model_tr_eta : (MndEx.model T).tr SigEx.MndTr.eta = MndEx.etaCell T := rfl

/-- A substituted sort term evaluates to the underlying object. -/
@[simp] lemma sigTm_obj_subS (a : SigEx.MndTr) (i : Fin (SigEx.mndSig.trn a)) (z : SigObj T) :
    ((MndEx.model T).sigTm (LaxEx.oneSig SigEx.mndSig) (LaxEx.subS SigEx.mndSig a i)).toFunctor.obj
        z =
      ob z := rfl

/-- The arrow of the transformation symbol `µ` evaluates at `z ∈ M^σ` to
    `T.μ.app x`, where `x = ob z`. -/
lemma arrCell_mu_app (z : SigObj T) :
    ((MndEx.model T).arrCell (LaxEx.oneSig SigEx.mndSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.mndSig) SigEx.MndTr.mu
        (LaxEx.subS SigEx.mndSig SigEx.MndTr.mu))).toNatTrans.app z = T.μ.app (ob z) := by
  rw [Model.arrCell_tr, Model.trAt, model_tr_mu]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `η` evaluates at `z ∈ M^σ` to
    `T.η.app x`, where `x = ob z`. -/
lemma arrCell_eta_app (z : SigObj T) :
    ((MndEx.model T).arrCell (LaxEx.oneSig SigEx.mndSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.mndSig) SigEx.MndTr.eta
        (LaxEx.subS SigEx.mndSig SigEx.MndTr.eta))).toNatTrans.app z = T.η.app (ob z) := by
  rw [Model.arrCell_tr, Model.trAt, model_tr_eta]
  simp only [Fin.isValue, PreModel.interp_var, PreModel.interp_app, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, cat_finProd_π_obj,
    cat_finProd_lift_obj, sigTm_obj_subS, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The `T_Lax` equation of the transformation symbol `µ`, evaluated at `z ∈ M^σ`, holds
    iff (with `x = ob z`, `a = act z`) `μ_x ≫ a = T(a) ≫ a` (associativity of `a`). -/
lemma eqn_mu (z : SigObj T) :
    ((MndEx.model T).arrCell (LaxEx.oneSig SigEx.mndSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.mndSig) SigEx.MndTr.mu
          (LaxEx.subS SigEx.mndSig SigEx.MndTr.mu))).toNatTrans.app z ≫
        semAt (MndEx.model T) z ((SigEx.mndSig.trtgt SigEx.MndTr.mu).subst
          (LaxEx.subS SigEx.mndSig SigEx.MndTr.mu)) =
      semAt (MndEx.model T) z ((SigEx.mndSig.trsrc SigEx.MndTr.mu).subst
          (LaxEx.subS SigEx.mndSig SigEx.MndTr.mu)) ↔
    T.μ.app (ob z) ≫ act z = (T : C ⥤ C).map (act z) ≫ act z := by
  rw [arrCell_mu_app]
  change T.μ.app (ob z) ≫ ((T : C ⥤ C).map (𝟙 (ob z)) ≫ act z) =
      (T : C ⥤ C).map ((T : C ⥤ C).map (𝟙 (ob z)) ≫ act z) ≫ act z ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `η`, evaluated at `z ∈ M^σ`, holds
    iff (with `x = ob z`, `a = act z`) `η_x ≫ a = 𝟙 x` (unit law of `a`). -/
lemma eqn_eta (z : SigObj T) :
    ((MndEx.model T).arrCell (LaxEx.oneSig SigEx.mndSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.mndSig) SigEx.MndTr.eta
          (LaxEx.subS SigEx.mndSig SigEx.MndTr.eta))).toNatTrans.app z ≫
        semAt (MndEx.model T) z ((SigEx.mndSig.trtgt SigEx.MndTr.eta).subst
          (LaxEx.subS SigEx.mndSig SigEx.MndTr.eta)) =
      semAt (MndEx.model T) z ((SigEx.mndSig.trsrc SigEx.MndTr.eta).subst
          (LaxEx.subS SigEx.mndSig SigEx.MndTr.eta)) ↔
    T.η.app (ob z) ≫ act z = 𝟙 (ob z) := by
  rw [arrCell_eta_app]
  change T.η.app (ob z) ≫ ((T : C ⥤ C).map (𝟙 (ob z)) ≫ act z) = 𝟙 (ob z) ↔ _
  simp

/-- **The defining condition of `M^{T_Lax}`** for the model of a monad: the two axioms of an
Eilenberg–Moore algebra. -/
lemma mem_thy_iff (z : SigObj T) :
    ((MndEx.model T).lhsCell (LaxEx.oneSig SigEx.mndSig) (LaxEx.theory
        SigEx.mndSig)).toNatTrans.app z =
        ((MndEx.model T).rhsCell (LaxEx.oneSig SigEx.mndSig) (LaxEx.theory
            SigEx.mndSig)).toNatTrans.app z ↔
      (T.μ.app (ob z) ≫ act z = (T : C ⥤ C).map (act z) ≫ act z ∧
        T.η.app (ob z) ≫ act z = 𝟙 (ob z)) := by
  rw [mem_thy_iff_semAt]
  constructor
  · intro h
    exact ⟨(eqn_mu z).1 (h SigEx.MndTr.mu), (eqn_eta z).1 (h SigEx.MndTr.eta)⟩
  · rintro ⟨h1, h2⟩ a
    cases a
    · exact (eqn_mu z).2 h1
    · exact (eqn_eta z).2 h2

/-- A `T_Lax`-bialgebra for the model of `T`, as a `T`-algebra. -/
def toAlg (t : ThyObj (MndEx.model T)) : T.Algebra where
  A := ob t.obj
  a := act t.obj
  unit := ((mem_thy_iff t.obj).1 t.property).2
  assoc := ((mem_thy_iff t.obj).1 t.property).1

variable (T) in
/-- The comparison functor from `M^{T_Lax}` to the Eilenberg–Moore category. -/
def comparison : ThyObj (MndEx.model T) ⥤ T.Algebra where
  obj t := toAlg t
  map {_ _} f := { f := f.hom.base (), h := (congr($(f.hom.w) SigEx.MndFun.T)).symm }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor `M^{T_Lax} ⥤ T.Algebra` is faithful. -/
instance : (comparison T).Faithful where
  map_injective {_ _ f g} h := by
    apply ObjectProperty.hom_ext
    apply Ins.hom_ext
    funext s
    cases s
    exact congrArg Monad.Algebra.Hom.f h

/-- A `T`-algebra, as an object of `M^σ`. -/
def ofAlgSig (A : T.Algebra) : SigObj T where
  pt := fun _ => A.A
  cell := fun B => match B with
    | SigEx.MndFun.T => A.a

/-! ### The inverse functor: an isomorphism of categories over `C` -/

/-- A `T`-algebra, as an object of `M^{T_Lax}`. -/
def ofAlg (A : T.Algebra) : ThyObj (MndEx.model T) :=
  ⟨ofAlgSig A, (mem_thy_iff (ofAlgSig A)).2 ⟨A.assoc, A.unit⟩⟩

variable (T) in
/-- The strict inverse of the comparison functor: a `T`-algebra, as a `T_Lax`-bialgebra. -/
def inverseFunctor : T.Algebra ⥤ ThyObj (MndEx.model T) where
  obj A := ofAlg A
  map {A A'} f := ObjectProperty.homMk (⟨fun _ => f.f, by
    funext s
    cases s
    exact f.h.symm⟩ : (ofAlg A).obj ⟶ (ofAlg A').obj)
  map_id _ := rfl
  map_comp _ _ := rfl

variable (T) in
/-- The comparison functor is a strict left inverse of `inverseFunctor`. -/
lemma inverseFunctor_comp_comparison : inverseFunctor T ⋙ comparison T = 𝟭 T.Algebra := rfl

/-- `inverseFunctor` is a strict left inverse of the comparison functor on objects. The only
function symbol of `σ_Lax` for `Σ_Mnd` is `T`, so this holds by `rfl`. -/
lemma inverseFunctor_obj_comparison_obj (t : ThyObj (MndEx.model T)) :
    (inverseFunctor T).obj ((comparison T).obj t) = t :=
  rfl

variable (T) in
/-- `inverseFunctor` is a strict left inverse of the comparison functor. -/
lemma comparison_comp_inverseFunctor :
    comparison T ⋙ inverseFunctor T = 𝟭 (ThyObj (MndEx.model T)) :=
  comp_eq_id_of_faithful _ _ (inverseFunctor_comp_comparison T) inverseFunctor_obj_comparison_obj

variable (T) in
/-- The comparison functor lies over `C`: it commutes with the forgetful functors to `C`, where
`M^{T_Lax}` lies over `C` through `U : M^{T_Lax} → M₀` and the projection `M₀ → C`. -/
lemma comparison_comp_forget :
    comparison T ⋙ T.forget = ((MndEx.model T).thyForget (LaxEx.oneSig SigEx.mndSig)
      (LaxEx.theory SigEx.mndSig)).toFunctor ⋙ (((MndEx.model T).P0 (LaxEx.oneSig SigEx.mndSig)).π
          ()).toFunctor :=
  rfl

end MndCase

/-! ## Monoidal categories -/

namespace MonCase

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]

variable (C) in
/-- The objects of `M^σ` for the lax-limit signature and the model of `C`. -/
abbrev SigObj : Type (max u v) :=
  ((monModel C).sigObj (LaxEx.oneSig SigEx.monSig) : Type (max u v))

/-- The underlying object of an object of `M^σ`. -/
def ob (z : SigObj C) : C := Ins.pt z ()

/-- The multiplication of an object of `M^σ`. -/
def mul (z : SigObj C) : ob z ⊗ ob z ⟶ ob z := Ins.cell z SigEx.MonFun.tens

/-- The unit of an object of `M^σ`. -/
def one (z : SigObj C) : 𝟙_ C ⟶ ob z := Ins.cell z SigEx.MonFun.unit

/-- The monoidal model interprets transformation symbols by its structure cells. -/
@[simp] lemma monModel_tr (a : SigEx.MonTr) : (monModel C).tr a = monCell C a := rfl

/-- A substituted sort term evaluates to the underlying object. -/
@[simp] lemma sigTm_obj_subS (a : SigEx.MonTr) (i : Fin (SigEx.monSig.trn a)) (z : SigObj C) :
    ((monModel C).sigTm (LaxEx.oneSig SigEx.monSig) (LaxEx.subS SigEx.monSig a i)).toFunctor.obj z =
      ob z := rfl

/-- The arrow of the transformation symbol `assoc` evaluates at `z ∈ M^σ` to
    `(α_ x x x).hom`, where `x = ob z`. -/
lemma arrCell_assoc_app (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.assoc
        (LaxEx.subS SigEx.monSig SigEx.MonTr.assoc))).toNatTrans.app z =
      (α_ (ob z) (ob z) (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, monModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `assocInv` evaluates at `z ∈ M^σ` to
    `(α_ x x x).inv`, where `x = ob z`. -/
lemma arrCell_assocInv_app (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.assocInv
        (LaxEx.subS SigEx.monSig SigEx.MonTr.assocInv))).toNatTrans.app z =
      (α_ (ob z) (ob z) (ob z)).inv := by
  rw [Model.arrCell_tr, Model.trAt, monModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `lunit` evaluates at `z ∈ M^σ` to
    `(λ_ x).hom`, where `x = ob z`. -/
lemma arrCell_lunit_app (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.lunit
        (LaxEx.subS SigEx.monSig SigEx.MonTr.lunit))).toNatTrans.app z =
      (λ_ (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, monModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, PreModel.interp_var, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    cat_finProd_π_obj, cat_finProd_lift_obj, sigTm_obj_subS]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `lunitInv` evaluates at `z ∈ M^σ` to
    `(λ_ x).inv`, where `x = ob z`. -/
lemma arrCell_lunitInv_app (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.lunitInv
        (LaxEx.subS SigEx.monSig SigEx.MonTr.lunitInv))).toNatTrans.app z =
      (λ_ (ob z)).inv := by
  rw [Model.arrCell_tr, Model.trAt, monModel_tr]
  simp only [Fin.isValue, PreModel.interp_var, PreModel.interp_app, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, cat_finProd_π_obj,
    cat_finProd_lift_obj, sigTm_obj_subS, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `runit` evaluates at `z ∈ M^σ` to
    `(ρ_ x).hom`, where `x = ob z`. -/
lemma arrCell_runit_app (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.runit
        (LaxEx.subS SigEx.monSig SigEx.MonTr.runit))).toNatTrans.app z =
      (ρ_ (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, monModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, PreModel.interp_var, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    cat_finProd_π_obj, cat_finProd_lift_obj, sigTm_obj_subS]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `runitInv` evaluates at `z ∈ M^σ` to
    `(ρ_ x).inv`, where `x = ob z`. -/
lemma arrCell_runitInv_app (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.runitInv
        (LaxEx.subS SigEx.monSig SigEx.MonTr.runitInv))).toNatTrans.app z =
      (ρ_ (ob z)).inv := by
  rw [Model.arrCell_tr, Model.trAt, monModel_tr]
  simp only [Fin.isValue, PreModel.interp_var, PreModel.interp_app, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, cat_finProd_π_obj,
    cat_finProd_lift_obj, sigTm_obj_subS, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The `T_Lax` equation of the transformation symbol `assoc`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `α_ ≫ (x ◁ µ) ≫ µ = (µ ▷ x) ≫ µ`. -/
lemma eqn_assoc (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.assoc
          (LaxEx.subS SigEx.monSig SigEx.MonTr.assoc))).toNatTrans.app z ≫
        semAt (monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.assoc).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.assoc)) =
      semAt (monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.assoc).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.assoc)) ↔
    (α_ (ob z) (ob z) (ob z)).hom ≫ MonoidalCategory.whiskerLeft (ob z) (mul z) ≫ mul z =
      MonoidalCategory.whiskerRight (mul z) (ob z) ≫ mul z := by
  rw [arrCell_assoc_app]
  change (α_ (ob z) (ob z) (ob z)).hom ≫
      ((𝟙 (ob z) ⊗ₘ ((𝟙 (ob z) ⊗ₘ 𝟙 (ob z)) ≫ mul z)) ≫ mul z) =
      ((((𝟙 (ob z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `assocInv`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `α_⁻¹ ≫ (µ ▷ x) ≫ µ = (x ◁ µ) ≫ µ`. -/
lemma eqn_assocInv (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.assocInv
          (LaxEx.subS SigEx.monSig SigEx.MonTr.assocInv))).toNatTrans.app z ≫
        semAt (monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.assocInv).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.assocInv)) =
      semAt (monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.assocInv).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.assocInv)) ↔
    (α_ (ob z) (ob z) (ob z)).inv ≫ MonoidalCategory.whiskerRight (mul z) (ob z) ≫ mul z =
      MonoidalCategory.whiskerLeft (ob z) (mul z) ≫ mul z := by
  rw [arrCell_assocInv_app]
  change (α_ (ob z) (ob z) (ob z)).inv ≫
      ((((𝟙 (ob z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) =
      ((𝟙 (ob z) ⊗ₘ ((𝟙 (ob z) ⊗ₘ 𝟙 (ob z)) ≫ mul z)) ≫ mul z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `lunit`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `λ_ x = (u ▷ x) ≫ µ`. -/
lemma eqn_lunit (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.lunit
          (LaxEx.subS SigEx.monSig SigEx.MonTr.lunit))).toNatTrans.app z ≫
        semAt (monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.lunit).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.lunit)) =
      semAt (monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.lunit).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.lunit)) ↔
    (λ_ (ob z)).hom = MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z := by
  rw [arrCell_lunit_app]
  change (λ_ (ob z)).hom ≫
      𝟙 (ob z) =
      (((𝟙 (𝟙_ C) ≫ one z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `lunitInv`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `(λ_ x)⁻¹ ≫ (u ▷ x) ≫ µ = 𝟙 x`. -/
lemma eqn_lunitInv (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.lunitInv
          (LaxEx.subS SigEx.monSig SigEx.MonTr.lunitInv))).toNatTrans.app z ≫
        semAt (monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.lunitInv).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.lunitInv)) =
      semAt (monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.lunitInv).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.lunitInv)) ↔
    (λ_ (ob z)).inv ≫ MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z = 𝟙 (ob z) := by
  rw [arrCell_lunitInv_app]
  change (λ_ (ob z)).inv ≫
      (((𝟙 (𝟙_ C) ≫ one z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) =
      𝟙 (ob z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `runit`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `ρ_ x = (x ◁ u) ≫ µ`. -/
lemma eqn_runit (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.runit
          (LaxEx.subS SigEx.monSig SigEx.MonTr.runit))).toNatTrans.app z ≫
        semAt (monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.runit).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.runit)) =
      semAt (monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.runit).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.runit)) ↔
    (ρ_ (ob z)).hom = MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z := by
  rw [arrCell_runit_app]
  change (ρ_ (ob z)).hom ≫
      𝟙 (ob z) =
      ((𝟙 (ob z) ⊗ₘ (𝟙 (𝟙_ C) ≫ one z)) ≫ mul z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `runitInv`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `(ρ_ x)⁻¹ ≫ (x ◁ u) ≫ µ = 𝟙 x`. -/
lemma eqn_runitInv (z : SigObj C) :
    ((monModel C).arrCell (LaxEx.oneSig SigEx.monSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.monSig) SigEx.MonTr.runitInv
          (LaxEx.subS SigEx.monSig SigEx.MonTr.runitInv))).toNatTrans.app z ≫
        semAt (monModel C) z ((SigEx.monSig.trtgt SigEx.MonTr.runitInv).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.runitInv)) =
      semAt (monModel C) z ((SigEx.monSig.trsrc SigEx.MonTr.runitInv).subst
          (LaxEx.subS SigEx.monSig SigEx.MonTr.runitInv)) ↔
    (ρ_ (ob z)).inv ≫ MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z = 𝟙 (ob z) := by
  rw [arrCell_runitInv_app]
  change (ρ_ (ob z)).inv ≫
      ((𝟙 (ob z) ⊗ₘ (𝟙 (𝟙_ C) ≫ one z)) ≫ mul z) =
      𝟙 (ob z) ↔ _
  simp

/-- **The defining condition of `M^{T_Lax}`** for the model of `C`: the axioms of a
monoid. -/
lemma mem_thy_iff (z : SigObj C) :
    ((monModel C).lhsCell (LaxEx.oneSig SigEx.monSig) (LaxEx.theory SigEx.monSig)).toNatTrans.app z
        =
        ((monModel C).rhsCell (LaxEx.oneSig SigEx.monSig)
          (LaxEx.theory SigEx.monSig)).toNatTrans.app z ↔
      (MonoidalCategory.whiskerRight (mul z) (ob z) ≫ mul z =
          (α_ (ob z) (ob z) (ob z)).hom ≫ MonoidalCategory.whiskerLeft (ob z) (mul z) ≫ mul z ∧
        MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z = (ρ_ (ob z)).hom ∧
        MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z = (λ_ (ob z)).hom) := by
  rw [mem_thy_iff_semAt]
  constructor
  · intro h
    exact ⟨((eqn_assoc z).1 (h SigEx.MonTr.assoc)).symm,
      ((eqn_runit z).1 (h SigEx.MonTr.runit)).symm,
      ((eqn_lunit z).1 (h SigEx.MonTr.lunit)).symm⟩
  · rintro ⟨h1, h2, h3⟩ a
    cases a
    · exact (eqn_assoc z).2 h1.symm
    · exact (eqn_assocInv z).2 (by rw [h1, Iso.inv_hom_id_assoc])
    · exact (eqn_lunit z).2 h3.symm
    · exact (eqn_lunitInv z).2 (by rw [h3, Iso.inv_hom_id])
    · exact (eqn_runit z).2 h2.symm
    · exact (eqn_runitInv z).2 (by rw [h2, Iso.inv_hom_id])

/-! ### Morphisms of `M^σ` -/

/-- The underlying morphism of `C` of a morphism of `M^σ`. -/
def bs {z z' : SigObj C} (f : z ⟶ z') : ob z ⟶ ob z' := f.base ()

/-- A morphism of `M^σ` is determined by its underlying morphism of `C`. -/
lemma bs_injective {z z' : SigObj C} {f g : z ⟶ z'} (h : bs f = bs g) : f = g := by
  apply Ins.hom_ext
  funext s
  cases s
  exact h

/-- The underlying morphism of a morphism of `M^σ` commutes with the multiplications. -/
lemma bs_mul {z z' : SigObj C} (f : z ⟶ z') : mul z ≫ bs f = (bs f ⊗ₘ bs f) ≫ mul z' :=
  congr($(f.w) SigEx.MonFun.tens)

/-- The underlying morphism of a morphism of `M^σ` commutes with the units. -/
lemma bs_one {z z' : SigObj C} (f : z ⟶ z') : one z ≫ bs f = one z' := by
  have h : one z ≫ bs f = 𝟙 (𝟙_ C) ≫ one z' := congr($(f.w) SigEx.MonFun.unit)
  simpa using h

/-- A morphism of `M^σ`, built from a morphism of `C` compatible with the multiplications and
the units. -/
def homMk {z z' : SigObj C} (g : ob z ⟶ ob z')
    (hm : mul z ≫ g = (g ⊗ₘ g) ≫ mul z') (he : one z ≫ g = one z') : z ⟶ z' where
  base := fun _ => g
  w := by
    funext f
    cases f
    · exact hm
    · exact he.trans (Category.id_comp _).symm

/-! ### The comparison functor -/

/-- The monoid structure of a `T_Lax`-bialgebra. -/
instance monObj (t : ThyObj (monModel C)) : MonObj (ob t.obj) where
  one := one t.obj
  mul := mul t.obj
  one_mul := ((mem_thy_iff t.obj).1 t.property).2.2
  mul_one := ((mem_thy_iff t.obj).1 t.property).2.1
  mul_assoc := ((mem_thy_iff t.obj).1 t.property).1

/-- A monoid of `C`, as an object of `M^σ`. -/
def ofSig (M : Mon C) : SigObj C where
  pt := fun _ => M.X
  cell := fun B => match B with
    | SigEx.MonFun.tens => (MonObj.mul : M.X ⊗ M.X ⟶ M.X)
    | SigEx.MonFun.unit => (MonObj.one : 𝟙_ C ⟶ M.X)

/-- A monoid of `C`, as an object of `M^{T_Lax}`. -/
def ofMon (M : Mon C) : ThyObj (monModel C) :=
  ⟨ofSig M, (mem_thy_iff (ofSig M)).2
    ⟨MonObj.mul_assoc M.X, MonObj.mul_one M.X, MonObj.one_mul M.X⟩⟩

variable (C) in
/-- **The comparison functor** from `M^{T_Lax}` to the category of monoids of `C`. -/
@[simps]
def comparison : ThyObj (monModel C) ⥤ Mon C where
  obj t := { X := ob t.obj }
  map {_ _} f :=
    { hom := bs f.hom
      isMonHom_hom :=
        { one_hom := bs_one f.hom
          mul_hom := bs_mul f.hom } }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor `M^{T_Lax} ⥤ Mon C` is faithful. -/
instance : (comparison C).Faithful where
  map_injective {_ _} f g h := by
    apply ObjectProperty.hom_ext
    apply bs_injective
    exact congrArg Mon.Hom.hom h

/-! ### The inverse functor: an isomorphism of categories over `C` -/

variable (C) in
/-- The strict inverse of the comparison functor: a monoid of `C`, as a `T_Lax`-bialgebra. -/
def inverseFunctor : Mon C ⥤ ThyObj (monModel C) where
  obj M := ofMon M
  map g := ObjectProperty.homMk (homMk g.hom (IsMonHom.mul_hom g.hom) (IsMonHom.one_hom g.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (C) in
/-- The comparison functor is a strict left inverse of `inverseFunctor`. -/
lemma inverseFunctor_comp_comparison : inverseFunctor C ⋙ comparison C = 𝟭 (Mon C) := rfl

/-- `inverseFunctor` is a strict left inverse of the comparison functor on objects. -/
lemma inverseFunctor_obj_comparison_obj (t : ThyObj (monModel C)) :
    (inverseFunctor C).obj ((comparison C).obj t) = t := by
  apply ObjectProperty.FullSubcategory.ext
  obtain ⟨⟨pt, cell⟩, h⟩ := t
  change Ins.mk pt _ = Ins.mk pt cell
  congr 1
  funext s
  cases s <;> rfl

variable (C) in
/-- `inverseFunctor` is a strict left inverse of the comparison functor. -/
lemma comparison_comp_inverseFunctor :
    comparison C ⋙ inverseFunctor C = 𝟭 (ThyObj (monModel C)) :=
  comp_eq_id_of_faithful _ _ (inverseFunctor_comp_comparison C) inverseFunctor_obj_comparison_obj

variable (C) in
/-- The comparison functor lies over `C`: it commutes with the forgetful functors to `C`, where
`M^{T_Lax}` lies over `C` through `U : M^{T_Lax} → M₀` and the projection `M₀ → C`. -/
lemma comparison_comp_forget :
    comparison C ⋙ Mon.forget C = ((monModel C).thyForget (LaxEx.oneSig SigEx.monSig)
      (LaxEx.theory SigEx.monSig)).toFunctor ⋙ (((monModel C).P0 (LaxEx.oneSig SigEx.monSig)).π
          ()).toFunctor :=
  rfl

end MonCase

end UlmerBialgebras.Paper.LaxLimit.Internal
