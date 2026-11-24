module

public import UlmerBialgebras.Proofs.Sec3.Support.LaxMonoidalComponents
public import UlmerBialgebras.Proofs.Sec3.MonModelCalc
public import UlmerBialgebras.Models.Induced
public import UlmerBialgebras.Examples.MonEquiv
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Lax monoidal functors and the syntactic theory of monoids

Corollary 3.24 by the paper's route. A lax monoidal functor `F : C ⥤ D` is a lax morphism of
`Σ_Mon`-models (its tensor and unit comparisons, compatible with the transformation symbols by the
lax monoidal laws). The theory of monoids is algebraic, so Corollary 3.23 (1) induces
`F^T : M^{T_Mon} → N^{T_Mon}` over `F^σ`. Read through Example 3.20 (1), this is
`F̄ : Mon(C) ⥤ Mon(D)`, and `F^σ` gives the formulas `μ_F ≫ F(m)` and `ε_F ≫ F(e)`. The objects of
bialgebras are formed in one `Cat.{w, w}`, so `C` and `D` are first lifted to a common size.

## Main results

* `UlmerBialgebras.MonEx.monoidalLaxMor`: a lax monoidal functor as a lax morphism of
  `Σ_Mon`-models.
* `UlmerBialgebras.MonEx.monF`: the induced functor `Mon(C) ⥤ Mon(D)`, at one size, with
  `UlmerBialgebras.MonEx.monF_forget`, `UlmerBialgebras.MonEx.monF_mul` and
  `UlmerBialgebras.MonEx.monF_one`.
* `UlmerBialgebras.MonEx.exists_monFunctor_of_laxMonoidal`: Corollary 3.24 at independent
  universes.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 3.20 (1), Corollaries 3.23 and 3.24
-/

@[expose] public section

universe w w' v u v' u'

namespace UlmerBialgebras.MonEx

open UlmerBialgebras.LaxMonoidalComponents

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

section Data

variable {C D : Type u} [Category.{v} C] [MonoidalCategory C]
  [Category.{v} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

/-- The tensor and unit comparisons of a lax monoidal functor as lax model data. -/
def monoidalLaxData : LaxData (monPreModel C) (monPreModel D) where
  cell := fun _ => F.toCatHom
  str := fun B =>
    match B with
    | .tens =>
      NatTrans.toCatHom₂ {
        app := fun p => μ F (ev C p 0) (ev C p 1)
        naturality := fun _ _ f => by
          dsimp [monPreModel, tensFunctor, ev]
          exact μ_natural F (evMap C f 0) (evMap C f 1) }
    | .unit =>
      NatTrans.toCatHom₂ {
        app := fun _ => ε F
        naturality := fun _ _ _ => by
          change 𝟙 (𝟙_ D) ≫ ε F = ε F ≫ F.map (𝟙 (𝟙_ C))
          simp }

/-- **A lax monoidal functor is a lax morphism of `Σ_Mon`-models.** The compatibility with the
transformation symbols is the associativity and unit laws of the lax structure. -/
def monoidalLaxMor : LaxMor (monModel C) (monModel D) where
  toLaxData := monoidalLaxData F
  tr_compat := by
    intro a
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext p
    cases a
    case assoc =>
      let X := ev C p 0
      let Y := ev C p 1
      let Z := ev C p 2
      change transportComponent (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          tensorComponent F (𝟙 _) (tensorComponent F (𝟙 _) (𝟙 _)) =
        tensorComponent F (tensorComponent F (𝟙 _) (𝟙 _)) (𝟙 _) ≫ F.map (α_ X Y Z).hom
      simp [tensorComponent, transportComponent, Category.assoc]
    case lunit =>
      let X := ev C p 0
      change transportComponent (λ_ (F.obj X)).hom ≫ 𝟙 _ =
        tensorComponent F (unitComponent F) (𝟙 _) ≫ F.map (λ_ X).hom
      simp [tensorComponent, unitComponent, transportComponent, Category.assoc]
    case runit =>
      let X := ev C p 0
      change transportComponent (ρ_ (F.obj X)).hom ≫ 𝟙 _ =
        tensorComponent F (𝟙 _) (unitComponent F) ≫ F.map (ρ_ X).hom
      simp [tensorComponent, unitComponent, transportComponent, Category.assoc]

/-- The codomains of the operations and equations of the monoid theory are sorts. -/
lemma monTheory_isAlgebraic : monTheory.IsAlgebraic :=
  ⟨fun _ => trivial, fun _ => trivial⟩

end Data

section Core

/-! ## The induced functor at one size -/

variable {C D : Type (max u v)} [Category.{v} C] [MonoidalCategory C]
  [Category.{v} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

/-- The inverse of a morphism equal to an `eqToHom`. -/
lemma inv_eq_eqToHom' {A : Type*} [Category A] {X Y : A} {f : X ⟶ Y} {h : X = Y}
    (hf : f = eqToHom h) {i : IsIso f} : @inv _ _ _ _ f i = eqToHom h.symm := by
  subst hf; simp

/-- `Ψ` at the sort term is an `eqToHom`: `η` is the identity at a variable. -/
lemma psi_sTm : (monoidalLaxMor F).Psi oneSig sTm = eqToHom
    (((monoidalLaxMor F).sig_src_eq oneSig sTm).trans
      (show (monModel C).u oneSig ≫ ((monModel C).tm oneSig sTm ≫ (monoidalLaxMor F).cell ()) = _
        by rw [← Category.assoc, ← Model.sigTm_eq])) := by
  rw [LaxMor.Psi]
  have : (monoidalLaxMor F).etaTm oneSig sTm = 𝟙 _ := rfl
  rw [this, Bicategory.whiskerLeft_id, Category.id_comp, eqToHom_trans]

/-- The functor `F^σ : M^σ → N^σ` of Lemma 3.21 (1) for `F`. -/
noncomputable abbrev sigF : SigObj C ⥤ SigObj D :=
  ((monoidalLaxMor F).sigMor oneSig
    (fun f => (monoidalLaxMor F).toLaxData.eta_isVar _ (monTheory_isAlgebraic.1 f))).toFunctor

/-- The structure maps of `F^σ z` are the components of the 2-cell (3.4). -/
lemma cell_sigF (z : SigObj C) (f : FnSym) :
    ((sigF F).obj z).cell f = ((monoidalLaxMor F).sigStr oneSig
      (fun f => (monoidalLaxMor F).toLaxData.eta_isVar _
        (monTheory_isAlgebraic.1 f))).toNatTrans.app z f := rfl

/-- The multiplication and unit of `F^σ z` are `μ_F ≫ F(m)` and `ε_F ≫ F(e)`. -/
lemma mul_one_sigF (z : SigObj C) :
    mul ((sigF F).obj z) = μ F (ob z) (ob z) ≫ F.map (mul z) ∧
      one ((sigF F).obj z) = ε F ≫ F.map (one z) := by
  constructor
  · rw [mul, cell_sigF, LaxMor.sigStr, cat_lift₂_app]
    dsimp only [oneSig]
    rw [inv_eq_eqToHom' (psi_sTm F)]
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      LaxMor.Psi, LaxMor.etaTm, tens, LaxData.eta, LaxData.strAt, PreModel.appCell,
      Category.assoc, Cat.eqToHom_app, Cat.Hom₂.id_app, eqToHom_refl]
    let X := F.obj (ob z)
    let m : ob z ⊗ ob z ⟶ ob z :=
      ((monModel C).arrCell oneSig (OneSig.Arr.fn (sg := oneSig) FnSym.mul)).toNatTrans.app z
    change 𝟙 _ ≫ 𝟙 _ ≫ ((𝟙 X ≫ 𝟙 X ≫ 𝟙 X) ⊗ₘ (𝟙 X ≫ 𝟙 X ≫ 𝟙 X)) ≫
      𝟙 _ ≫ μ F (ob z) (ob z) ≫ 𝟙 _ ≫ 𝟙 _ ≫ F.map m ≫ 𝟙 _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id, id_tensorHom_id, m, arrCell_fn_mul_app]
  · rw [one, cell_sigF, LaxMor.sigStr, cat_lift₂_app]
    dsimp only [oneSig]
    rw [inv_eq_eqToHom' (psi_sTm F)]
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      LaxMor.Psi, LaxMor.etaTm, unitT, LaxData.eta, LaxData.strAt, PreModel.appCell,
      Category.assoc, Cat.eqToHom_app, Cat.Hom₂.id_app, eqToHom_refl]
    let e : 𝟙_ C ⟶ ob z :=
      ((monModel C).arrCell oneSig (OneSig.Arr.fn (sg := oneSig) FnSym.one)).toNatTrans.app z
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 (𝟙_ D) ≫ 𝟙 _ ≫ ε F ≫ 𝟙 _ ≫ 𝟙 _ ≫
      F.map e ≫ 𝟙 _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id, e, arrCell_fn_one_app]

/-- The multiplication of `F^σ z` is `μ_F ≫ F(m)`. -/
lemma mul_sigF (z : SigObj C) : mul ((sigF F).obj z) = μ F (ob z) (ob z) ≫ F.map (mul z) :=
  (mul_one_sigF F z).1

/-- The unit of `F^σ z` is `ε_F ≫ F(e)`. -/
lemma one_sigF (z : SigObj C) : one ((sigF F).obj z) = ε F ≫ F.map (one z) :=
  (mul_one_sigF F z).2

/-- The functor `M^{T_Mon} → N^{T_Mon}` induced by Corollary 3.23 (1). -/
noncomputable def thyF : ThyObj C ⥤ ThyObj D :=
  ((monoidalLaxMor F).exists_unique_thyMor_of_algebraic oneSig monTheory
    monTheory_isAlgebraic).exists.choose.toFunctor

/-- `F^T` lies over `F^σ`. -/
lemma thyF_e : thyF F ⋙ ((monModel D).e oneSig monTheory).toFunctor =
    ((monModel C).e oneSig monTheory).toFunctor ⋙ sigF F :=
  congrArg Cat.Hom.toFunctor ((monoidalLaxMor F).exists_unique_thyMor_of_algebraic oneSig
    monTheory monTheory_isAlgebraic).exists.choose_spec

/-- The functor `Mon(C) → Mon(D)` of Corollary 3.24, through `M^{T_Mon}`. -/
noncomputable def monF : Mon C ⥤ Mon D := inverseFunctor C ⋙ thyF F ⋙ comparison D

/-- The underlying `σ_Mon`-structure of `F̄ M` is `F^σ` of that of `M`. -/
lemma monF_obj_obj (M : Mon C) :
    ((thyF F).obj ((inverseFunctor C).obj M)).obj = (sigF F).obj (ofMonSig M) :=
  Functor.congr_obj (thyF_e F) ((inverseFunctor C).obj M)

/-- The multiplication of `F̄ M` is `μ_F ≫ F(m)`. -/
lemma monF_mul (M : Mon C) : HEq (MonObj.mul (X := ((monF F).obj M).X))
    (μ F M.X M.X ≫ F.map (MonObj.mul (X := M.X))) := by
  change HEq (mul ((thyF F).obj ((inverseFunctor C).obj M)).obj) _
  rw [monF_obj_obj]
  exact heq_of_eq (mul_sigF F _)

/-- The unit of `F̄ M` is `ε_F ≫ F(e)`. -/
lemma monF_one (M : Mon C) : HEq (MonObj.one (X := ((monF F).obj M).X))
    (ε F ≫ F.map (MonObj.one (X := M.X))) := by
  change HEq (one ((thyF F).obj ((inverseFunctor C).obj M)).obj) _
  rw [monF_obj_obj]
  exact heq_of_eq (one_sigF F _)

/-- `F̄` lies over `F`. -/
lemma monF_forget : monF F ⋙ Mon.forget D = Mon.forget C ⋙ F := by
  have h : thyF F ⋙ ((monModel D).thyForget oneSig monTheory).toFunctor ⋙
      (((monModel D).P0 oneSig).π ()).toFunctor =
      ((monModel C).thyForget oneSig monTheory).toFunctor ⋙
        (((monModel C).P0 oneSig).π ()).toFunctor ⋙ F := by
    have := congrArg Cat.Hom.toFunctor (congrArg
      (fun g : (monModel C).sigObj oneSig ⟶ ((monModel D).P0 oneSig).pt =>
        g ≫ ((monModel D).P0 oneSig).π ())
      ((monoidalLaxMor F).sigMor_u oneSig
        (fun f => (monoidalLaxMor F).toLaxData.eta_isVar _ (monTheory_isAlgebraic.1 f))))
    change thyF F ⋙ ((monModel D).e oneSig monTheory).toFunctor ⋙
      ((monModel D).u oneSig).toFunctor ⋙ (((monModel D).P0 oneSig).π ()).toFunctor = _
    rw [← Functor.assoc, thyF_e, Functor.assoc]
    exact (congrArg (fun G => ((monModel C).e oneSig monTheory).toFunctor ⋙ G) this).trans rfl
  change inverseFunctor C ⋙ thyF F ⋙ (comparison D ⋙ Mon.forget D) = _
  rw [comparison_comp_forget]
  exact (congrArg (fun G => inverseFunctor C ⋙ G) h).trans rfl

end Core

/-! ## Lifting to a common size -/

attribute [local instance] uliftCategory

section Lift
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- `C` with objects and morphisms lifted to universe `w`. -/
abbrev Lifted : Type (max u w) := ULiftHom.{w} (ULift.{w} C)

/-- The equivalence `C ≌ Lifted C`. -/
abbrev liftEquiv : C ≌ Lifted.{w} C := ULift.equivalence.trans ULiftHom.equiv

/-- The monoidal structure of `C`, lifted. -/
@[instance_reducible]
def liftedStruct : MonoidalCategoryStruct (Lifted.{w} C) where
  tensorObj X Y :=
    (liftEquiv C).functor.obj ((liftEquiv C).inverse.obj X ⊗ (liftEquiv C).inverse.obj Y)
  whiskerLeft X _ _ f :=
    (liftEquiv C).functor.map ((liftEquiv C).inverse.obj X ◁ (liftEquiv C).inverse.map f)
  whiskerRight f X :=
    (liftEquiv C).functor.map ((liftEquiv C).inverse.map f ▷ (liftEquiv C).inverse.obj X)
  tensorHom f g :=
    (liftEquiv C).functor.map ((liftEquiv C).inverse.map f ⊗ₘ (liftEquiv C).inverse.map g)
  tensorUnit := (liftEquiv C).functor.obj (𝟙_ C)
  associator X Y Z := (liftEquiv C).functor.mapIso
    (α_ ((liftEquiv C).inverse.obj X) ((liftEquiv C).inverse.obj Y) ((liftEquiv C).inverse.obj Z))
  leftUnitor X := (liftEquiv C).functor.mapIso (λ_ ((liftEquiv C).inverse.obj X))
  rightUnitor X := (liftEquiv C).functor.mapIso (ρ_ ((liftEquiv C).inverse.obj X))

attribute [local instance] liftedStruct

/-- The lifted monoidal structure. -/
@[instance_reducible]
def liftedMonoidal : MonoidalCategory (Lifted.{w} C) where
  tensorHom_def _ _ := (liftEquiv C).inverse.map_injective (tensorHom_def _ _)
  id_tensorHom_id _ _ := (liftEquiv C).inverse.map_injective (id_tensorHom_id _ _)
  tensorHom_comp_tensorHom _ _ _ _ :=
    (liftEquiv C).inverse.map_injective (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id _ _ := (liftEquiv C).inverse.map_injective (whiskerLeft_id _ _)
  id_whiskerRight _ _ := (liftEquiv C).inverse.map_injective (id_whiskerRight _ _)
  associator_naturality _ _ _ :=
    (liftEquiv C).inverse.map_injective (associator_naturality _ _ _)
  leftUnitor_naturality _ := (liftEquiv C).inverse.map_injective (leftUnitor_naturality _)
  rightUnitor_naturality _ := (liftEquiv C).inverse.map_injective (rightUnitor_naturality _)
  pentagon _ _ _ _ := (liftEquiv C).inverse.map_injective (pentagon _ _ _ _)
  triangle _ _ := (liftEquiv C).inverse.map_injective (triangle _ _)

attribute [local instance] liftedMonoidal

/-- A monoid of `C`, as a monoid of `Lifted C`. -/
def toLiftedObj (M : Mon C) : Mon (Lifted.{w} C) where
  X := (liftEquiv C).functor.obj M.X
  mon :=
    { one := (liftEquiv C).functor.map (MonObj.one (X := M.X))
      mul := (liftEquiv C).functor.map (MonObj.mul (X := M.X))
      one_mul := (liftEquiv C).inverse.map_injective (MonObj.one_mul M.X)
      mul_one := (liftEquiv C).inverse.map_injective (MonObj.mul_one M.X)
      mul_assoc := (liftEquiv C).inverse.map_injective (MonObj.mul_assoc M.X) }

/-- Monoids of `C` as monoids of `Lifted C`. -/
def toLifted : Mon C ⥤ Mon (Lifted.{w} C) where
  obj := toLiftedObj C
  map {M N} f := Mon.Hom.mk' (M := toLiftedObj C M) (N := toLiftedObj C N)
    ((liftEquiv C).functor.map f.hom)
    ((liftEquiv C).inverse.map_injective (IsMonHom.one_hom f.hom))
    ((liftEquiv C).inverse.map_injective (IsMonHom.mul_hom f.hom))

/-- A monoid of `Lifted C`, as a monoid of `C`. -/
def fromLiftedObj (M : Mon (Lifted.{w} C)) : Mon C where
  X := (liftEquiv C).inverse.obj M.X
  mon :=
    { one := (liftEquiv C).inverse.map (MonObj.one (X := M.X))
      mul := (liftEquiv C).inverse.map (MonObj.mul (X := M.X))
      one_mul := congrArg (liftEquiv C).inverse.map (MonObj.one_mul M.X)
      mul_one := congrArg (liftEquiv C).inverse.map (MonObj.mul_one M.X)
      mul_assoc := congrArg (liftEquiv C).inverse.map (MonObj.mul_assoc M.X) }

/-- Monoids of `Lifted C` as monoids of `C`. -/
def fromLifted : Mon (Lifted.{w} C) ⥤ Mon C where
  obj := fromLiftedObj C
  map {M N} f := Mon.Hom.mk' (M := fromLiftedObj C M) (N := fromLiftedObj C N)
    ((liftEquiv C).inverse.map f.hom)
    (congrArg (liftEquiv C).inverse.map (IsMonHom.one_hom f.hom))
    (congrArg (liftEquiv C).inverse.map (IsMonHom.mul_hom f.hom))

end Lift

attribute [local instance] liftedStruct liftedMonoidal

section LiftFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

/-- `F` between the lifted categories. -/
abbrev liftF : Lifted.{w} C ⥤ Lifted.{w'} D :=
  (liftEquiv C).inverse ⋙ F ⋙ (liftEquiv D).functor

/-- The lax monoidal structure of `F`, lifted. -/
@[instance_reducible]
def liftFLax : (liftF.{w, w'} F).LaxMonoidal where
  ε := (liftEquiv D).functor.map (ε F)
  μ X Y :=
    (liftEquiv D).functor.map (μ F ((liftEquiv C).inverse.obj X) ((liftEquiv C).inverse.obj Y))
  μ_natural_left _ _ := (liftEquiv D).inverse.map_injective (μ_natural_left F _ _)
  μ_natural_right _ _ := (liftEquiv D).inverse.map_injective (μ_natural_right F _ _)
  associativity _ _ _ := (liftEquiv D).inverse.map_injective (associativity F _ _ _)
  left_unitality _ := (liftEquiv D).inverse.map_injective (left_unitality F _)
  right_unitality _ := (liftEquiv D).inverse.map_injective (right_unitality F _)

end LiftFunctor

/-- **Corollary 3.24 by the paper's route**: a lax monoidal functor `F : C ⥤ D` induces
`F̄ : Mon(C) ⥤ Mon(D)` over `F`, with multiplication `μ_F ≫ F(m)` and unit `ε_F ≫ F(e)`. It is the
functor of Corollary 3.23 (1) for the lax morphism `monoidalLaxMor` of `Σ_Mon`-models, read through
Example 3.20 (1), after lifting `C` and `D` to a common size. -/
theorem exists_monFunctor_of_laxMonoidal (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (D : Type u')
    [Category.{v'} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] :
    ∃ G : Mon C ⥤ Mon D, G ⋙ Mon.forget D = Mon.forget C ⋙ F ∧
      ∀ M : Mon C,
        HEq (MonObj.mul (X := (G.obj M).X))
            (Functor.LaxMonoidal.μ F M.X M.X ≫ F.map (MonObj.mul (X := M.X))) ∧
          HEq (MonObj.one (X := (G.obj M).X))
            (Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one (X := M.X))) := by
  let _ := liftFLax.{max u v u' v', max u v u' v'} F
  let F' := liftF.{max u v u' v', max u v u' v'} F
  have hF := monF_forget.{max u v u' v', max u v u' v'} F'
  refine ⟨toLifted.{max u v u' v'} C ⋙ monF.{max u v u' v', max u v u' v'} F' ⋙
    fromLifted.{max u v u' v'} D, ?_, fun M => ⟨?_, ?_⟩⟩
  · change toLifted C ⋙ (monF F' ⋙ Mon.forget _) ⋙ (liftEquiv D).inverse = _
    rw [hF]
    rfl
  · have h := Functor.congr_obj hF ((toLifted C).obj M)
    exact (UlmerBialgebras.Paper.MonModel.heq_map (liftEquiv D).inverse
      (congrArg (fun x => x ⊗ x) h) h (monF_mul F' _)).trans (heq_of_eq rfl)
  · have h := Functor.congr_obj hF ((toLifted C).obj M)
    exact (UlmerBialgebras.Paper.MonModel.heq_map (liftEquiv D).inverse rfl h
      (monF_one F' _)).trans (heq_of_eq rfl)


end UlmerBialgebras.MonEx
