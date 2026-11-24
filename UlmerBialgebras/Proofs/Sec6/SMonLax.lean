module

public import UlmerBialgebras.Proofs.Sec6.Support.ModelEval
public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc

/-!
# A braided monoidal functor is a strong morphism of `Σ_SMon`-models

## Main results

* `UlmerBialgebras.Paper.Loc.smonLaxMor`: a braided monoidal functor `C ⥤ D` as a lax morphism of
  `Σ_SMon`-models.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 3.10
  and Lemma 6.10
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (F : C ⥤ D) [F.Braided]

/-- The lax data of a monoidal functor: `μ` and `ε`. -/
def smonLaxData : LaxData (smonPreModel C) (smonPreModel D) where
  cell := fun _ => F.toCatHom
  str := fun B =>
    match B with
    | .tens =>
      NatTrans.toCatHom₂ {
        app := fun p => μ F (MonEx.ev C p 0) (MonEx.ev C p 1)
        naturality := fun _ _ f => by
          dsimp [smonPreModel, MonEx.tensFunctor, MonEx.ev]
          exact Functor.LaxMonoidal.μ_natural F (MonEx.evMap C f 0) (MonEx.evMap C f 1) }
    | .unit =>
      NatTrans.toCatHom₂ {
        app := fun _ => ε F
        naturality := fun _ _ _ =>
          (Category.id_comp _).trans ((Category.comp_id _).symm.trans (ε F ≫= (F.map_id _).symm)) }

/-- Evaluating `smonLaxData.eta` on a variable gives the identity. -/
lemma smonLaxData_eta_var_app {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (v : V) (p : x) :
    ((smonLaxData F).eta ρ (Trm.var v)).toNatTrans.app p =
      𝟙 (F.obj ((ρ v).toFunctor.obj p)) := rfl

/-- Evaluating `smonLaxData.eta` on a tensor term tensors the argument evaluations and
postcomposes with `μ F`. -/
lemma smonLaxData_eta_tens_app {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v))
    (a b : Trm SigEx.smonSig.toFunSig vty ()) (p : x) :
    ((smonLaxData F).eta ρ (SigEx.monTens a b)).toNatTrans.app p =
      CategoryStruct.comp (obj := D)
        (MonoidalCategoryStruct.tensorHom (C := D)
          (((smonLaxData F).eta ρ a).toNatTrans.app p)
          (((smonLaxData F).eta ρ b).toNatTrans.app p))
        (μ F (((smonPreModel C).interp ρ a).toFunctor.obj p)
          (((smonPreModel C).interp ρ b).toFunctor.obj p)) :=
  (ModelEval.cat_eta_app_app (smonLaxData F) ρ SigEx.MonFun.tens ![a, b] p).trans
    (smonPreModel_fn_tens_map D _ =≫ _)

/-- Evaluating `smonLaxData.eta` on the unit term gives `ε F`. -/
lemma smonLaxData_eta_unit_app {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (p : x) :
    ((smonLaxData F).eta ρ SigEx.monUnit).toNatTrans.app p = ε F := by
  rw [ModelEval.cat_eta_app_app, smonPreModel_fn_unit_map]
  exact Category.id_comp (ε F)

/-- Evaluating `smonLaxData.eta` on a binary tensor of variables gives `μ F`. -/
lemma smonLaxData_eta_tens_var_var {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (i j : V) (p : x) :
    ((smonLaxData F).eta ρ (SigEx.monTens (Trm.var i) (Trm.var j))).toNatTrans.app p =
      μ F ((ρ i).toFunctor.obj p) ((ρ j).toFunctor.obj p) := by
  rw [smonLaxData_eta_tens_app, smonLaxData_eta_var_app, smonLaxData_eta_var_app]
  exact (id_tensorHom_id _ _ =≫ _).trans (Category.id_comp _)

/-- Evaluating `smonLaxData.eta` on `I ⊗ x` gives `(ε F ▷ F x) ≫ μ F I x`. -/
lemma smonLaxData_eta_tens_unit_var {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (i : V) (p : x) :
    ((smonLaxData F).eta ρ (SigEx.monTens SigEx.monUnit (Trm.var i))).toNatTrans.app p =
      (ε F ▷ F.obj ((ρ i).toFunctor.obj p)) ≫ μ F (𝟙_ C) ((ρ i).toFunctor.obj p) := by
  rw [smonLaxData_eta_tens_app, smonLaxData_eta_unit_app, smonLaxData_eta_var_app]
  exact tensorHom_id _ _ =≫ _

/-- Evaluating `smonLaxData.eta` on `x ⊗ I` gives `(F x ◁ ε F) ≫ μ F x I`. -/
lemma smonLaxData_eta_tens_var_unit {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (i : V) (p : x) :
    ((smonLaxData F).eta ρ (SigEx.monTens (Trm.var i) SigEx.monUnit)).toNatTrans.app p =
      (F.obj ((ρ i).toFunctor.obj p) ◁ ε F) ≫ μ F ((ρ i).toFunctor.obj p) (𝟙_ C) := by
  rw [smonLaxData_eta_tens_app, smonLaxData_eta_var_app, smonLaxData_eta_unit_app]
  exact id_tensorHom _ _ =≫ _

/-- Evaluating `smonLaxData.eta` on `x ⊗ (y ⊗ z)`. -/
lemma smonLaxData_eta_tens_var_tens {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (i j k : V) (p : x) :
    ((smonLaxData F).eta ρ
        (SigEx.monTens (Trm.var i) (SigEx.monTens (Trm.var j) (Trm.var k)))).toNatTrans.app p =
      (F.obj ((ρ i).toFunctor.obj p) ◁ μ F ((ρ j).toFunctor.obj p) ((ρ k).toFunctor.obj p)) ≫
        μ F ((ρ i).toFunctor.obj p)
          (MonoidalCategoryStruct.tensorObj (C := C)
            ((ρ j).toFunctor.obj p) ((ρ k).toFunctor.obj p)) := by
  rw [smonLaxData_eta_tens_app, smonLaxData_eta_var_app, smonLaxData_eta_tens_var_var]
  exact id_tensorHom _ _ =≫ _

/-- Evaluating `smonLaxData.eta` on `(x ⊗ y) ⊗ z`. -/
lemma smonLaxData_eta_tens_tens_var {V : Type} {vty : V → SigEx.smonSig.Cat} {x : Cat.{v, u}}
    (ρ : ∀ v, x ⟶ (smonPreModel C).obj (vty v)) (i j k : V) (p : x) :
    ((smonLaxData F).eta ρ
        (SigEx.monTens (SigEx.monTens (Trm.var i) (Trm.var j)) (Trm.var k))).toNatTrans.app p =
      (μ F ((ρ i).toFunctor.obj p) ((ρ j).toFunctor.obj p) ▷ F.obj ((ρ k).toFunctor.obj p)) ≫
        μ F (MonoidalCategoryStruct.tensorObj (C := C)
            ((ρ i).toFunctor.obj p) ((ρ j).toFunctor.obj p))
          ((ρ k).toFunctor.obj p) := by
  rw [smonLaxData_eta_tens_app, smonLaxData_eta_tens_var_var, smonLaxData_eta_var_app]
  exact tensorHom_id _ _ =≫ _

/-- **A braided monoidal functor is a lax morphism of `Σ_SMon`-models.** -/
def smonLaxMor : LaxMor (smonModel C) (smonModel D) where
  toLaxData := smonLaxData F
  tr_compat := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext p
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerRight_app]
    cases a
    case assoc =>
      exact (smonModel_trAt_assoc_app D _ p =≫ _).trans
        ((_ ≫= smonLaxData_eta_tens_var_tens F _ 0 1 2 p).trans
          (((Functor.LaxMonoidal.associativity F (p 0) (p 1) (p 2)).symm.trans
            (Category.assoc _ _ _).symm).trans
            (smonLaxData_eta_tens_tens_var F _ 0 1 2 p =≫ _).symm))
    case assocInv =>
      exact (smonModel_trAt_assocInv_app D _ p =≫ _).trans
        ((_ ≫= smonLaxData_eta_tens_tens_var F _ 0 1 2 p).trans
          (((Functor.LaxMonoidal.associativity_inv F (p 0) (p 1) (p 2)).symm.trans
            (Category.assoc _ _ _).symm).trans
            (smonLaxData_eta_tens_var_tens F _ 0 1 2 p =≫ _).symm))
    case lunit =>
      exact (smonModel_trAt_lunit_app D _ p =≫ _).trans
        ((Category.comp_id _).trans
          (((Functor.LaxMonoidal.left_unitality F (p 0)).trans
            (Category.assoc _ _ _).symm).trans
            (smonLaxData_eta_tens_unit_var F _ 0 p =≫ _).symm))
    case lunitInv =>
      exact (smonModel_trAt_lunitInv_app D _ p =≫ _).trans
        ((_ ≫= smonLaxData_eta_tens_unit_var F _ 0 p).trans
          ((Functor.LaxMonoidal.left_unitality_inv F (p 0)).trans (Category.id_comp _).symm))
    case runit =>
      exact (smonModel_trAt_runit_app D _ p =≫ _).trans
        ((Category.comp_id _).trans
          (((Functor.LaxMonoidal.right_unitality F (p 0)).trans
            (Category.assoc _ _ _).symm).trans
            (smonLaxData_eta_tens_var_unit F _ 0 p =≫ _).symm))
    case runitInv =>
      exact (smonModel_trAt_runitInv_app D _ p =≫ _).trans
        ((_ ≫= smonLaxData_eta_tens_var_unit F _ 0 p).trans
          ((Functor.LaxMonoidal.right_unitality_inv F (p 0)).trans (Category.id_comp _).symm))
    case sym =>
      exact (smonModel_trAt_sym_app D _ p =≫ _).trans
        ((_ ≫= smonLaxData_eta_tens_var_var F _ 1 0 p).trans
          ((Functor.Braided.braided (F := F) (p 0) (p 1)).symm.trans
            (smonLaxData_eta_tens_var_var F _ 0 1 p =≫ _).symm))

end UlmerBialgebras.Paper.Loc
