module

public import UlmerBialgebras.Proofs.Sec3.LaxLimitEquiv

/-!
# Comparisons for the lax-limit theories: symmetric monoidal categories

The comparison functor from the lax-limit bialgebras of a symmetric monoidal category `C` to
`CommMon C` and its strict inverse (Examples 3.20 (4)), continuing
`UlmerBialgebras/Proofs/Sec3/LaxLimitEquiv.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper.LaxLimit.Internal

open CategoryTheory MonoidalCategory

/-! ## Symmetric monoidal categories -/

namespace SMonCase

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

variable (C) in
/-- The objects of `M^σ` for the lax-limit signature and the model of `C`. -/
abbrev SigObj : Type (max u v) :=
  ((Loc.smonModel C).sigObj (LaxEx.oneSig SigEx.smonSig) : Type (max u v))

/-- The underlying object of an object of `M^σ`. -/
def ob (z : SigObj C) : C := Ins.pt z ()

/-- The multiplication of an object of `M^σ`. -/
def mul (z : SigObj C) : ob z ⊗ ob z ⟶ ob z := Ins.cell z SigEx.MonFun.tens

/-- The unit of an object of `M^σ`. -/
def one (z : SigObj C) : 𝟙_ C ⟶ ob z := Ins.cell z SigEx.MonFun.unit

/-- The symmetric monoidal model interprets transformation symbols by its structure cells. -/
@[simp] lemma smonModel_tr (a : SigEx.SMonTr) : (Loc.smonModel C).tr a = Loc.smonCell C a := rfl

/-- A substituted sort term evaluates to the underlying object. -/
@[simp] lemma sigTm_obj_subS (a : SigEx.SMonTr) (i : Fin (SigEx.smonSig.trn a)) (z : SigObj C) :
    ((Loc.smonModel C).sigTm (LaxEx.oneSig SigEx.smonSig) (LaxEx.subS SigEx.smonSig a
        i)).toFunctor.obj z =
      ob z := rfl

/-- The arrow of the transformation symbol `assoc` evaluates at `z ∈ M^σ` to
    `(α_ x x x).hom`, where `x = ob z`. -/
lemma arrCell_assoc_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.assoc
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assoc))).toNatTrans.app z =
      (α_ (ob z) (ob z) (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `assocInv` evaluates at `z ∈ M^σ` to
    `(α_ x x x).inv`, where `x = ob z`. -/
lemma arrCell_assocInv_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.assocInv
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assocInv))).toNatTrans.app z =
      (α_ (ob z) (ob z) (ob z)).inv := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `lunit` evaluates at `z ∈ M^σ` to
    `(λ_ x).hom`, where `x = ob z`. -/
lemma arrCell_lunit_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.lunit
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunit))).toNatTrans.app z =
      (λ_ (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, PreModel.interp_var, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    cat_finProd_π_obj, cat_finProd_lift_obj, sigTm_obj_subS]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `lunitInv` evaluates at `z ∈ M^σ` to
    `(λ_ x).inv`, where `x = ob z`. -/
lemma arrCell_lunitInv_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.lunitInv
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunitInv))).toNatTrans.app z =
      (λ_ (ob z)).inv := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_var, PreModel.interp_app, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, cat_finProd_π_obj,
    cat_finProd_lift_obj, sigTm_obj_subS, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `runit` evaluates at `z ∈ M^σ` to
    `(ρ_ x).hom`, where `x = ob z`. -/
lemma arrCell_runit_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.runit
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runit))).toNatTrans.app z =
      (ρ_ (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, PreModel.interp_var, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app,
    cat_finProd_π_obj, cat_finProd_lift_obj, sigTm_obj_subS]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `runitInv` evaluates at `z ∈ M^σ` to
    `(ρ_ x).inv`, where `x = ob z`. -/
lemma arrCell_runitInv_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.runitInv
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runitInv))).toNatTrans.app z =
      (ρ_ (ob z)).inv := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_var, PreModel.interp_app, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, cat_finProd_π_obj,
    cat_finProd_lift_obj, sigTm_obj_subS, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The arrow of the transformation symbol `sym` evaluates at `z ∈ M^σ` to
    `(β_ x x).hom`, where `x = ob z`. -/
lemma arrCell_sym_app (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
      (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.sym
        (LaxEx.subS SigEx.smonSig SigEx.SMonTr.sym))).toNatTrans.app z =
      (β_ (ob z) (ob z)).hom := by
  rw [Model.arrCell_tr, Model.trAt, smonModel_tr]
  simp only [Fin.isValue, PreModel.interp_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The `T_Lax` equation of the transformation symbol `assoc`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `α_ ≫ (x ◁ µ) ≫ µ = (µ ▷ x) ≫ µ`. -/
lemma eqn_assoc (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.assoc
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assoc))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.assoc).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assoc)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.assoc).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assoc)) ↔
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
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.assocInv
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assocInv))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.assocInv).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assocInv)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.assocInv).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.assocInv)) ↔
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
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.lunit
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunit))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.lunit).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunit)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.lunit).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunit)) ↔
    (λ_ (ob z)).hom = MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z := by
  rw [arrCell_lunit_app]
  change (λ_ (ob z)).hom ≫
      𝟙 (ob z) =
      (((𝟙 (𝟙_ C) ≫ one z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `lunitInv`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `(λ_ x)⁻¹ ≫ (u ▷ x) ≫ µ = 𝟙 x`. -/
lemma eqn_lunitInv (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.lunitInv
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunitInv))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.lunitInv).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunitInv)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.lunitInv).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.lunitInv)) ↔
    (λ_ (ob z)).inv ≫ MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z = 𝟙 (ob z) := by
  rw [arrCell_lunitInv_app]
  change (λ_ (ob z)).inv ≫
      (((𝟙 (𝟙_ C) ≫ one z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) =
      𝟙 (ob z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `runit`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `ρ_ x = (x ◁ u) ≫ µ`. -/
lemma eqn_runit (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.runit
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runit))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.runit).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runit)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.runit).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runit)) ↔
    (ρ_ (ob z)).hom = MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z := by
  rw [arrCell_runit_app]
  change (ρ_ (ob z)).hom ≫
      𝟙 (ob z) =
      ((𝟙 (ob z) ⊗ₘ (𝟙 (𝟙_ C) ≫ one z)) ≫ mul z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `runitInv`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `(ρ_ x)⁻¹ ≫ (x ◁ u) ≫ µ = 𝟙 x`. -/
lemma eqn_runitInv (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.runitInv
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runitInv))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.runitInv).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runitInv)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.runitInv).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.runitInv)) ↔
    (ρ_ (ob z)).inv ≫ MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z = 𝟙 (ob z) := by
  rw [arrCell_runitInv_app]
  change (ρ_ (ob z)).inv ≫
      ((𝟙 (ob z) ⊗ₘ (𝟙 (𝟙_ C) ≫ one z)) ≫ mul z) =
      𝟙 (ob z) ↔ _
  simp

/-- The `T_Lax` equation of the transformation symbol `sym`, evaluated at `z ∈ M^σ`, holds
    iff (`x = ob z`, `µ = mul z`, `u = one z`) `β_ x x ≫ µ = µ` (commutativity). -/
lemma eqn_sym (z : SigObj C) :
    ((Loc.smonModel C).arrCell (LaxEx.oneSig SigEx.smonSig)
        (OneSig.Arr.tr (sg := LaxEx.oneSig SigEx.smonSig) SigEx.SMonTr.sym
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.sym))).toNatTrans.app z ≫
        semAt (Loc.smonModel C) z ((SigEx.smonSig.trtgt SigEx.SMonTr.sym).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.sym)) =
      semAt (Loc.smonModel C) z ((SigEx.smonSig.trsrc SigEx.SMonTr.sym).subst
          (LaxEx.subS SigEx.smonSig SigEx.SMonTr.sym)) ↔
    (β_ (ob z) (ob z)).hom ≫ mul z = mul z := by
  rw [arrCell_sym_app]
  change (β_ (ob z) (ob z)).hom ≫
      ((𝟙 (ob z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) =
      ((𝟙 (ob z) ⊗ₘ 𝟙 (ob z)) ≫ mul z) ↔ _
  simp

/-- **The defining condition of `M^{T_Lax}`** for the model of `C`: the axioms of a
commutative monoid. -/
lemma mem_thy_iff (z : SigObj C) :
    ((Loc.smonModel C).lhsCell (LaxEx.oneSig SigEx.smonSig) (LaxEx.theory
        SigEx.smonSig)).toNatTrans.app z =
        ((Loc.smonModel C).rhsCell (LaxEx.oneSig SigEx.smonSig)
          (LaxEx.theory SigEx.smonSig)).toNatTrans.app z ↔
      (MonoidalCategory.whiskerRight (mul z) (ob z) ≫ mul z =
          (α_ (ob z) (ob z) (ob z)).hom ≫ MonoidalCategory.whiskerLeft (ob z) (mul z) ≫ mul z ∧
        MonoidalCategory.whiskerLeft (ob z) (one z) ≫ mul z = (ρ_ (ob z)).hom ∧
        MonoidalCategory.whiskerRight (one z) (ob z) ≫ mul z = (λ_ (ob z)).hom ∧
        (β_ (ob z) (ob z)).hom ≫ mul z = mul z) := by
  rw [mem_thy_iff_semAt]
  constructor
  · intro h
    exact ⟨((eqn_assoc z).1 (h SigEx.SMonTr.assoc)).symm,
      ((eqn_runit z).1 (h SigEx.SMonTr.runit)).symm,
      ((eqn_lunit z).1 (h SigEx.SMonTr.lunit)).symm, (eqn_sym z).1 (h SigEx.SMonTr.sym)⟩
  · rintro ⟨hassoc, hrunit, hlunit, hsym⟩ a
    cases a
    · exact (eqn_assoc z).2 hassoc.symm
    · exact (eqn_assocInv z).2 (by rw [hassoc, Iso.inv_hom_id_assoc])
    · exact (eqn_lunit z).2 hlunit.symm
    · exact (eqn_lunitInv z).2 (by rw [hlunit, Iso.inv_hom_id])
    · exact (eqn_runit z).2 hrunit.symm
    · exact (eqn_runitInv z).2 (by rw [hrunit, Iso.inv_hom_id])
    · exact (eqn_sym z).2 hsym

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
instance monObj (t : ThyObj (Loc.smonModel C)) : MonObj (ob t.obj) where
  one := one t.obj
  mul := mul t.obj
  one_mul := ((mem_thy_iff t.obj).1 t.property).2.2.1
  mul_one := ((mem_thy_iff t.obj).1 t.property).2.1
  mul_assoc := ((mem_thy_iff t.obj).1 t.property).1

/-- A `T_Lax`-bialgebra of the symmetric monoidal model is commutative. -/
instance commObj (t : ThyObj (Loc.smonModel C)) : IsCommMonObj (ob t.obj) where
  mul_comm := ((mem_thy_iff t.obj).1 t.property).2.2.2

/-- A commutative monoid of `C`, as an object of `M^σ`. -/
def ofSig (M : CommMon C) : SigObj C where
  pt := fun _ => M.X
  cell := fun B => match B with
    | SigEx.MonFun.tens => (MonObj.mul : M.X ⊗ M.X ⟶ M.X)
    | SigEx.MonFun.unit => (MonObj.one : 𝟙_ C ⟶ M.X)

/-- A commutative monoid of `C`, as an object of `M^{T_Lax}`. -/
def ofMon (M : CommMon C) : ThyObj (Loc.smonModel C) :=
  ⟨ofSig M, (mem_thy_iff (ofSig M)).2
    ⟨MonObj.mul_assoc M.X, MonObj.mul_one M.X, MonObj.one_mul M.X, IsCommMonObj.mul_comm M.X⟩⟩

variable (C) in
/-- **The comparison functor** from `M^{T_Lax}` to the category of commutative monoids of
`C`. -/
@[simps]
def comparison : ThyObj (Loc.smonModel C) ⥤ CommMon C where
  obj t := { X := ob t.obj }
  map {_ _} f := CommMon.homMk
    { hom := bs f.hom
      isMonHom_hom :=
        { one_hom := bs_one f.hom
          mul_hom := bs_mul f.hom } }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor `M^{T_Lax} ⥤ CommMon C` is faithful. -/
instance : (comparison C).Faithful where
  map_injective {_ _} f g h := by
    apply ObjectProperty.hom_ext
    apply bs_injective
    exact congrArg (fun k => Mon.Hom.hom (InducedCategory.Hom.hom k)) h

/-! ### The inverse functor: an isomorphism of categories over `C` -/

variable (C) in
/-- The strict inverse of the comparison functor: a commutative monoid of `C`, as a
`T_Lax`-bialgebra. -/
def inverseFunctor : CommMon C ⥤ ThyObj (Loc.smonModel C) where
  obj M := ofMon M
  map g := ObjectProperty.homMk (homMk g.hom.hom (IsMonHom.mul_hom g.hom.hom)
    (IsMonHom.one_hom g.hom.hom))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (C) in
/-- The comparison functor is a strict left inverse of `inverseFunctor`. -/
lemma inverseFunctor_comp_comparison : inverseFunctor C ⋙ comparison C = 𝟭 (CommMon C) := rfl

/-- `inverseFunctor` is a strict left inverse of the comparison functor on objects. -/
lemma inverseFunctor_obj_comparison_obj (t : ThyObj (Loc.smonModel C)) :
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
    comparison C ⋙ inverseFunctor C = 𝟭 (ThyObj (Loc.smonModel C)) :=
  comp_eq_id_of_faithful _ _ (inverseFunctor_comp_comparison C) inverseFunctor_obj_comparison_obj

variable (C) in
/-- The comparison functor lies over `C`: it commutes with the forgetful functors to `C`, where
`M^{T_Lax}` lies over `C` through `U : M^{T_Lax} → M₀` and the projection `M₀ → C`. -/
lemma comparison_comp_forget :
    comparison C ⋙ CommMon.forget C = ((Loc.smonModel C).thyForget (LaxEx.oneSig SigEx.smonSig)
      (LaxEx.theory SigEx.smonSig)).toFunctor ⋙ (((Loc.smonModel C).P0 (LaxEx.oneSig
          SigEx.smonSig)).π ()).toFunctor :=
  rfl

end SMonCase

end UlmerBialgebras.Paper.LaxLimit.Internal
