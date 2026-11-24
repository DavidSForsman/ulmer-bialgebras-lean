module

public import Companion.Proofs.ClassicalModels

/-!
# Classical models: commutative monoids and groups

The isomorphisms between the models of the theories of commutative monoids and of groups in a
cartesian monoidal category and its commutative monoid and group objects, continuing
`Companion/Proofs/ClassicalModels.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
-/

@[expose] public section

universe v u w u₁ u₂

namespace UlmerBialgebras.Paper.ClassicalModels

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MSLanguage

/-! ## Commutative monoids -/

section CMon

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local instance] monStructure BraidedCategory.ofCartesianMonoidalCategory

/-- Evaluating `x * y` in any structure for the language of monoids. -/
lemma ev_monMul_gen (M : monLanguage.Sorts → C) [monLanguage.Structure M] {Y : C} {n : ℕ}
    (x : ∀ _ : Fin n, Y ⟶ M pt) (a b : monLanguage.Term (fun _ : Fin n => ()) ()) :
    ev M x (monMul a b) =
      Pi.lift (C := C) (f := fun _ : Fin 2 => M pt) ![ev M x a, ev M x b] ≫
        funMap (M := M) mulSym :=
  (congr(Pi.lift $(funext fun j => by fin_cases j <;> rfl)) =≫ funMap (M := M) mulSym)

variable (C) in
/-- The model of the theory of monoids underlying a model of the theory of commutative
monoids. -/
noncomputable abbrev cmonReduct : cmonTheory.ModelCat C ⥤ monTheory.ModelCat C :=
  monCMonMorphism.modelFunctor C

/-- The multiplication of the reduct is that of the model. -/
lemma reduct_homMul (A : cmonTheory.ModelCat C) {Y : C} (f g : Y ⟶ A.Carrier pt) :
    homMul (A := (cmonReduct C).obj A) f g =
      Pi.lift (C := C) (f := fun _ : Fin 2 => A.Carrier pt) ![f, g] ≫
          funMap (M := A.Carrier) mulSym :=
  (Pi.lift _ ≫= ((Pi.lift_π =≫ funMap (M := A.Carrier) mulSym).trans
    (Category.id_comp _)))

/-- The unit of the reduct is that of the model. -/
lemma reduct_homOne (A : cmonTheory.ModelCat C) (Y : C) :
    homOne (A := (cmonReduct C).obj A) Y =
      Pi.lift (C := C) (f := fun _ : Fin 0 => A.Carrier pt) (fun i => i.elim0) ≫
        funMap (M := A.Carrier) oneSym :=
  (Pi.lift _ ≫= ((Pi.lift_π =≫ funMap (M := A.Carrier) oneSym).trans
    (Category.id_comp _)))

/-- The multiplication of a model of the theory of commutative monoids commutes. -/
lemma cmon_comm (A : cmonTheory.ModelCat C) {Y : C} (f g : Y ⟶ A.Carrier pt) :
    Pi.lift (C := C) (f := fun _ : Fin 2 => A.Carrier pt) ![g, f] ≫ funMap (M := A.Carrier) mulSym =
      Pi.lift (C := C) (f := fun _ : Fin 2 => A.Carrier pt) ![f, g] ≫
        funMap (M := A.Carrier) mulSym := by
  have h := ev_eq_of_realize A.Carrier (A.is_model.realize_of_mem _ (Set.mem_insert _ _))
    (![f, g] : ∀ _ : Fin 2, Y ⟶ A.Carrier pt)
  simp only [mulCommEquation, ev_monMul_gen] at h
  exact h

/-- The monoid object of a model of the theory of commutative monoids is commutative. -/
lemma isCommMonObj (A : cmonTheory.ModelCat C) :
    @IsCommMonObj C _ _ _ (X ((cmonReduct C).obj A)) (monObj ((cmonReduct C).obj A)) := by
  let := monObj ((cmonReduct C).obj A)
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun Y => ⟨⟨fun f g => ?_⟩⟩
  rw [Hom.mul_def, Hom.mul_def, monObj_lift_mul, monObj_lift_mul]
  exact (reduct_homMul A f g).trans ((cmon_comm A g f).trans (reduct_homMul A g f).symm)

variable (C) in
/-- Models of the theory of commutative monoids to commutative monoid objects. -/
noncomputable def modelToCMon : cmonTheory.ModelCat C ⥤ CommMon C where
  obj A := @CommMon.mk C _ _ _ (X ((cmonReduct C).obj A)) (monObj ((cmonReduct C).obj A))
    (isCommMonObj A)
  map g := InducedCategory.homMk ((modelToMon C).map ((cmonReduct C).map g))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The commutative monoid object of a model `A` is the reduct's object, with the reduct's monoid
structure. -/
lemma modelToCMon_obj (A : cmonTheory.ModelCat C) :
    (modelToCMon C).obj A = @CommMon.mk C _ _ _ (X ((cmonReduct C).obj A))
      (monObj ((cmonReduct C).obj A)) (isCommMonObj A) := rfl

/-- A commutative monoid object is a model of the theory of commutative monoids. -/
lemma cmonStructure_model (M : CommMon C) :
    (fun _ : monLanguage.Sorts => M.X) ⊨ cmonTheory := by
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with rfl | hφ
  · rw [Equation.Realize, realize_eq_ev, realize_eq_ev]
    simp only [mulCommEquation, ev_monMul_ofMon]
    exact ((isCommMonObj_iff_isMulCommutative M.X).mp inferInstance _).is_comm.comm _ _
  · exact (monStructure_model M.X).realize_of_mem φ hφ

variable (C) in
/-- The model of the theory of commutative monoids of a commutative monoid object. -/
noncomputable def ofCMon (M : CommMon C) : cmonTheory.ModelCat C :=
  haveI := cmonStructure_model M
  ⟨fun _ : monLanguage.Sorts => M.X⟩

variable (C) in
/-- Commutative monoid objects to models of the theory of commutative monoids. -/
noncomputable def cmonToModel : CommMon C ⥤ cmonTheory.ModelCat C where
  obj M := ofCMon C M
  map f := homOfMon f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

end CMon

section CMonLaws

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local instance] monStructure BraidedCategory.ofCartesianMonoidalCategory

/-- The underlying morphism of an `eqToHom` between commutative monoid objects is the `eqToHom` of
the underlying objects. -/
lemma cmon_eqToHom_hom {M N : CommMon C} (h : M = N) :
    (eqToHom h).hom.hom = eqToHom (congrArg CommMon.X h) := by
  subst h
  rfl

/-- The underlying morphism of a composite of morphisms of commutative monoid objects is the
composite of the underlying morphisms. -/
lemma cmon_comp_hom {M N P : CommMon C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom.hom = f.hom.hom ≫ g.hom.hom := rfl

/-- A model of the theory of commutative monoids is recovered from its commutative monoid object. -/
lemma ofCMon_modelToCMon (M : monLanguage.Sorts → C) [monLanguage.Structure M]
    [M ⊨ cmonTheory] : ofCMon C ((modelToCMon C).obj ⟨M⟩) = ⟨M⟩ := by
  refine MSLanguage.modelCat_mk_eq _ _ (fun f => ?_) _ _
  obtain ⟨⟨⟨⟩, op⟩, h⟩ := f
  cases op
  · refine (monObj_lift_mul (A := (cmonReduct C).obj ⟨M⟩) (Pi.π (fun _ : Fin 2 => M pt) 0)
      (Pi.π (fun _ : Fin 2 => M pt) 1)).trans ((reduct_homMul ⟨M⟩ _ _).trans ?_)
    exact ((piLift_two_π (M pt)) =≫ funMap (M := M) mulSym).trans (Category.id_comp _)
  · refine (monObj_toUnit_one (A := (cmonReduct C).obj ⟨M⟩) _).trans
      ((reduct_homOne ⟨M⟩ _).trans ?_)
    exact (congrArg (· ≫ funMap (M := M) oneSym) (piLift_zero_eq _ (𝟙 _))).trans
      (Category.id_comp _)
  · exact absurd rfl h

variable (C) in
/-- Passing from models of the theory of commutative monoids to commutative monoid objects and back
is the identity functor. -/
lemma modelToCMon_cmonToModel : modelToCMon C ⋙ cmonToModel C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun A => by
    obtain ⟨M⟩ := A
    exact ofCMon_modelToCMon M)
  (fun A B g => MSLanguage.Hom.ext (funext fun s => by
    refine Eq.trans ?_ (MSLanguage.comp_toFun _ _ s).symm
    refine Eq.trans ?_ (((MSLanguage.modelCat_eqToHom_toFun _ s) =≫ _).symm)
    refine Eq.trans ?_ ((_ ≫= (MSLanguage.comp_toFun _ _ s)).symm)
    refine Eq.trans ?_ (congr(_ ≫ _ ≫ $((MSLanguage.modelCat_eqToHom_toFun _ s).symm)))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

/-- A commutative monoid object is recovered from its model of the theory of commutative monoids. -/
lemma modelToCMon_ofCMon (M : C) [inst : MonObj M] [IsCommMonObj M] :
    (modelToCMon C).obj (ofCMon C (CommMon.mk M)) = CommMon.mk M := by
  have hm : monObj ((cmonReduct C).obj (ofCMon C (CommMon.mk M))) = inst := by
    refine MonObj.ext _ _ ?_
    refine (Category.id_comp _).symm.trans ?_
    refine (((lift_fst_snd (X := M) (Y := M)) =≫
      (monObj ((cmonReduct C).obj (ofCMon C (CommMon.mk M)))).mul).symm).trans ?_
    refine (monObj_lift_mul (A := (cmonReduct C).obj (ofCMon C (CommMon.mk M))) (fst M M)
      (snd M M)).trans ((reduct_homMul (ofCMon C (CommMon.mk M)) _ _).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (((piLift_two_lift _ _).trans lift_fst_snd) =≫ μ[M]).trans
      (Category.id_comp _)
  rw [modelToCMon_obj]
  generalize isCommMonObj (ofCMon C (CommMon.mk M)) = c
  revert c
  rw [hm]
  intro c
  rfl

variable (C) in
/-- Passing from commutative monoid objects to models of the theory of commutative monoids and back
is the identity functor. -/
lemma cmonToModel_modelToCMon : cmonToModel C ⋙ modelToCMon C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun M => by
    obtain ⟨M⟩ := M
    exact modelToCMon_ofCMon M)
  (fun M N f => InducedCategory.hom_ext (Mon.Hom.ext (by
    refine Eq.trans ?_ (cmon_comp_hom _ _).symm
    refine Eq.trans ?_ (((cmon_eqToHom_hom _) =≫ _).symm)
    refine Eq.trans ?_ ((_ ≫= (cmon_comp_hom _ _)).symm)
    refine Eq.trans ?_ (congr(_ ≫ _ ≫ $((cmon_eqToHom_hom _).symm)))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm)))

end CMonLaws

/-! ## Groups -/

section Grp

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local instance] monStructure

/-- The symbol `mul` of the language of groups. -/
abbrev gMul : (grpLanguage Unit).Functions := ((), .mul)

/-- The symbol `one` of the language of groups. -/
abbrev gOne : (grpLanguage Unit).Functions := ((), .one)

/-- The symbol `inv` of the language of groups. -/
abbrev gInv : (grpLanguage Unit).Functions := ((), .inv)

/-- The sort of the language of groups at `Unit`. -/
abbrev gpt : (grpLanguage Unit).Sorts := ()

variable (C) in
/-- The model of the theory of monoids underlying a model of the theory of groups. -/
noncomputable abbrev grpReduct : (grpEqTheory Unit).ModelCat C ⥤ monTheory.ModelCat C :=
  monGrpMorphism.modelFunctor C

/-- The multiplication of the monoid reduct of a model of the theory of groups is that of the
model. -/
lemma grpReduct_homMul (A : (grpEqTheory Unit).ModelCat C) {Y : C} (f g : Y ⟶ A.Carrier gpt) :
    homMul (A := (grpReduct C).obj A) f g =
      Pi.lift (C := C) (f := fun _ : Fin 2 => A.Carrier gpt) ![f, g] ≫
          funMap (M := A.Carrier) gMul :=
  (Pi.lift _ ≫= ((Pi.lift_π =≫ funMap (M := A.Carrier) gMul).trans
    (Category.id_comp _)))

/-- The unit of the monoid reduct of a model of the theory of groups is that of the model. -/
lemma grpReduct_homOne (A : (grpEqTheory Unit).ModelCat C) (Y : C) :
    homOne (A := (grpReduct C).obj A) Y =
      Pi.lift (C := C) (f := fun _ : Fin 0 => A.Carrier gpt) (fun i => i.elim0) ≫
        funMap (M := A.Carrier) gOne :=
  (Pi.lift _ ≫= ((Pi.lift_π =≫ funMap (M := A.Carrier) gOne).trans
    (Category.id_comp _)))

/-- The inverse of a model of the theory of groups. -/
noncomputable def gInvMap (A : (grpEqTheory Unit).ModelCat C) : A.Carrier gpt ⟶ A.Carrier gpt :=
  Pi.lift (C := C) (f := fun _ : Fin 1 => A.Carrier gpt) ![𝟙 _] ≫ funMap (M := A.Carrier) gInv

/-- Each defining equation of the theory of groups holds in a model, evaluated at any generalized
elements. -/
lemma grp_eq (A : (grpEqTheory Unit).ModelCat C) (e : Cart.GrpEqn) {Y : C}
    (x : ∀ _ : Fin (grpEquation Unit ((), e)).ctxLen, Y ⟶ A.Carrier gpt) :
    ev A.Carrier x (grpEquation Unit ((), e)).lhs = ev A.Carrier x (grpEquation Unit ((), e)).rhs :=
  ev_eq_of_realize A.Carrier (A.is_model.realize_of_mem _ ⟨((), e), rfl⟩) x

/-- Evaluating `a * b` in any structure for the language of groups: the pair of the evaluations
followed by the multiplication symbol. -/
lemma ev_grpMul (M : (grpLanguage Unit).Sorts → C) [(grpLanguage Unit).Structure M] {Y : C}
    {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M gpt) (a b : (grpLanguage Unit).Term (fun _ : Fin n => ()) ()) :
    ev M x (grpMul () a b) =
      Pi.lift (C := C) (f := fun _ : Fin 2 => M gpt) ![ev M x a, ev M x b] ≫ funMap (M := M) gMul :=
  (congr(Pi.lift $(funext fun j => by fin_cases j <;> rfl)) =≫ funMap (M := M) gMul)

/-- Evaluating `1` in any structure for the language of groups: the empty tuple followed by the unit
symbol. -/
lemma ev_grpOne (M : (grpLanguage Unit).Sorts → C) [(grpLanguage Unit).Structure M] {Y : C}
    {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M gpt) :
    ev M x (grpOne (Γ := fun _ : Fin n => ()) ()) =
      Pi.lift (C := C) (f := fun _ : Fin 0 => M gpt) (fun i => i.elim0) ≫ funMap (M := M) gOne :=
  (congr(Pi.lift $(funext fun j => j.elim0)) =≫ funMap (M := M) gOne)

/-- Evaluating `a⁻¹` in any structure for the language of groups: the evaluation of `a` followed by
the inverse symbol. -/
lemma ev_grpInv (M : (grpLanguage Unit).Sorts → C) [(grpLanguage Unit).Structure M] {Y : C}
    {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M gpt) (a : (grpLanguage Unit).Term (fun _ : Fin n => ()) ()) :
    ev M x (grpInv () a) =
      Pi.lift (C := C) (f := fun _ : Fin 1 => M gpt) ![ev M x a] ≫ funMap (M := M) gInv :=
  (congr(Pi.lift $(funext fun j => by fin_cases j; rfl)) =≫ funMap (M := M) gInv)

variable (C) in
/-- **The group object of a model of the theory of groups.** -/
@[implicit_reducible]
noncomputable def grpObj (A : (grpEqTheory Unit).ModelCat C) : GrpObj (X ((grpReduct C).obj A)) :=
  { monObj ((grpReduct C).obj A) with
    inv := gInvMap A
    left_inv := by
      refine (monObj_lift_mul (A := (grpReduct C).obj A) _ _).trans
        ((grpReduct_homMul A _ _).trans ?_)
      refine Eq.trans ?_ ((monObj_toUnit_one (A := (grpReduct C).obj A) _).trans
        (grpReduct_homOne A _)).symm
      have h := grp_eq A Cart.GrpEqn.invMul (![𝟙 _] : ∀ _ : Fin 1, A.Carrier gpt ⟶ A.Carrier gpt)
      simp only [grpEquation, ev_grpMul, ev_grpInv, ev_grpOne] at h
      exact h
    right_inv := by
      refine (monObj_lift_mul (A := (grpReduct C).obj A) _ _).trans
        ((grpReduct_homMul A _ _).trans ?_)
      refine Eq.trans ?_ ((monObj_toUnit_one (A := (grpReduct C).obj A) _).trans
        (grpReduct_homOne A _)).symm
      have h := grp_eq A Cart.GrpEqn.mulInv (![𝟙 _] : ∀ _ : Fin 1, A.Carrier gpt ⟶ A.Carrier gpt)
      simp only [grpEquation, ev_grpMul, ev_grpInv, ev_grpOne] at h
      exact h }

end Grp

section GrpOf

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

/-- The interpretation of the language of groups by a group object. -/
@[implicit_reducible]
noncomputable def grpStructure (M : C) [GrpObj M] :
    (grpLanguage Unit).Structure (C := C) fun _ => M where
  funMap
    | ((), .mul) => show (∏ᶜ fun _ : Fin 2 => M) ⟶ M from
        lift (Pi.π (fun _ : Fin 2 => M) 0) (Pi.π (fun _ : Fin 2 => M) 1) ≫ μ
    | ((), .one) => toUnit _ ≫ η
    | ((), .inv) => show (∏ᶜ fun _ : Fin 1 => M) ⟶ M from Pi.π (fun _ : Fin 1 => M) 0 ≫ ι

attribute [local instance] grpStructure

/-- In the structure of a group object `M`, the multiplication symbol is
`lift (π 0) (π 1) ≫ μ[M]` on the product of two copies of `M`. -/
lemma grpStructure_mul (M : C) [GrpObj M] :
    funMap (M := fun _ => M) gMul =
      lift (Pi.π (fun _ : Fin 2 => M) 0) (Pi.π (fun _ : Fin 2 => M) 1) ≫ μ[M] := rfl

/-- In the structure of a group object `M`, the inverse symbol is `π 0 ≫ ι[M]` on the product of
one copy of `M`. -/
lemma grpStructure_inv (M : C) [GrpObj M] :
    funMap (M := fun _ => M) gInv = Pi.π (fun _ : Fin 1 => M) 0 ≫ ι[M] := rfl

/-- In the structure of a group object, `a * b` evaluates to the product of the evaluations. -/
lemma ev_grpMul_of (M : C) [GrpObj M] {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M)
    (a b : (grpLanguage Unit).Term (fun _ : Fin n => ()) ()) :
    ev (fun _ => M) x (grpMul () a b) = ev (fun _ => M) x a * ev (fun _ => M) x b := by
  rw [ev_grpMul, grpStructure_mul, ← Category.assoc, piLift_two_lift, Hom.mul_def]

/-- In the structure of a group object, `1` evaluates to the unit `1`. -/
lemma ev_grpOne_of (M : C) [GrpObj M] {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M) :
    ev (fun _ => M) x (grpOne (Γ := fun _ : Fin n => ()) ()) = 1 := by
  rw [ev_grpOne, Hom.one_def]
  exact comp_toUnit_assoc _ η[M]

/-- In the structure of a group object, `a⁻¹` evaluates to the inverse of the evaluation of `a`. -/
lemma ev_grpInv_of (M : C) [GrpObj M] {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M)
    (a : (grpLanguage Unit).Term (fun _ : Fin n => ()) ()) :
    ev (fun _ => M) x (grpInv () a) = (ev (fun _ => M) x a)⁻¹ := by
  rw [ev_grpInv, grpStructure_inv, ← Category.assoc, Pi.lift_comp_π]
  rfl

/-- A group object is a model of the theory of groups. -/
lemma grpStructure_model (M : C) [GrpObj M] :
    (fun _ : (grpLanguage Unit).Sorts => M) ⊨ grpEqTheory Unit := by
  refine ⟨?_⟩
  rintro _ ⟨⟨⟨⟩, e⟩, rfl⟩
  rw [Equation.Realize, realize_eq_ev, realize_eq_ev]
  cases e <;> simp only [grpEquation, ev_grpMul_of, ev_grpOne_of, ev_grpInv_of]
  · exact mul_assoc _ _ _
  · exact mul_one _
  · exact one_mul _
  · exact inv_mul_cancel _
  · exact mul_inv_cancel _

variable (C) in
/-- The model of the theory of groups of a group object. -/
noncomputable def ofGrp (M : Grp C) : (grpEqTheory Unit).ModelCat C :=
  haveI := grpStructure_model M.X
  ⟨fun _ : (grpLanguage Unit).Sorts => M.X⟩

/-- A homomorphism of group objects is a homomorphism of the models. -/
noncomputable def homOfGrp {M N : Grp C} (f : M ⟶ N) : ofGrp C M ⟶ ofGrp C N where
  toFun _ := f.hom.hom
  map_fun'
    | ((), .mul) => by
      change (lift (Pi.π (fun _ : Fin 2 => M.X) 0) (Pi.π (fun _ : Fin 2 => M.X) 1) ≫ μ)
          ≫ f.hom.hom =
        Limits.Pi.map (fun _ => f.hom.hom) ≫
          lift (Pi.π (fun _ : Fin 2 => N.X) 0) (Pi.π (fun _ : Fin 2 => N.X) 1) ≫ μ
      rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, ← Category.assoc, lift_map,
        comp_lift, Limits.Pi.map_π, Limits.Pi.map_π]
    | ((), .one) =>
      (Category.assoc _ _ _).trans ((toUnit _ ≫= IsMonHom.one_hom f.hom.hom).trans
        (comp_toUnit_assoc _ _).symm)
    | ((), .inv) => by
      change (Pi.π (fun _ : Fin 1 => M.X) 0 ≫ ι) ≫ f.hom.hom =
        Limits.Pi.map (fun _ => f.hom.hom) ≫ Pi.π (fun _ : Fin 1 => N.X) 0 ≫ ι
      rw [Category.assoc, GrpObj.inv_hom, ← Category.assoc, ← Category.assoc, Limits.Pi.map_π]

variable (C) in
/-- Models of the theory of groups to group objects. -/
noncomputable def modelToGrp : (grpEqTheory Unit).ModelCat C ⥤ Grp C where
  obj A := @Grp.mk C _ _ (X ((grpReduct C).obj A)) (grpObj C A)
  map g := InducedCategory.homMk ((modelToMon C).map ((grpReduct C).map g))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The group object of a model `A` is the reduct's object, with the group structure
`grpObj C A`. -/
lemma modelToGrp_obj (A : (grpEqTheory Unit).ModelCat C) :
    (modelToGrp C).obj A = @Grp.mk C _ _ (X ((grpReduct C).obj A)) (grpObj C A) := rfl

variable (C) in
/-- Group objects to models of the theory of groups. -/
noncomputable def grpToModel : Grp C ⥤ (grpEqTheory Unit).ModelCat C where
  obj M := ofGrp C M
  map f := homOfGrp f
  map_id _ := rfl
  map_comp _ _ := rfl

end GrpOf

section GrpLaws

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local instance] grpStructure

/-- The underlying morphism of an `eqToHom` between group objects is the `eqToHom` of the underlying
objects. -/
lemma grp_eqToHom_hom {M N : Grp C} (h : M = N) :
    (eqToHom h).hom.hom = eqToHom (congrArg Grp.X h) := by
  subst h
  rfl

/-- The underlying morphism of a composite of morphisms of group objects is the composite of the
underlying morphisms. -/
lemma grp_comp_hom {M N P : Grp C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom.hom = f.hom.hom ≫ g.hom.hom := rfl

omit [CartesianMonoidalCategory C] in
/-- For a product over `Fin 1`, the projection followed by the lift of `𝟙 Z` is the identity. -/
lemma piLift_one_π (Z : C) :
    Pi.π (C := C) (fun _ : Fin 1 => Z) 0 ≫
        Pi.lift (C := C) (f := fun _ : Fin 1 => Z) ![𝟙 Z] = 𝟙 _ :=
  Pi.hom_ext _ _ fun j => by fin_cases j; simp

/-- A model of the theory of groups is recovered from its group object. -/
lemma ofGrp_modelToGrp (M : (grpLanguage Unit).Sorts → C) [(grpLanguage Unit).Structure M]
    [M ⊨ grpEqTheory Unit] : ofGrp C ((modelToGrp C).obj ⟨M⟩) = ⟨M⟩ := by
  refine MSLanguage.modelCat_mk_eq _ _ (fun f => ?_) _ _
  obtain ⟨⟨⟩, op⟩ := f
  cases op with
  | mul =>
    refine (monObj_lift_mul (A := (grpReduct C).obj ⟨M⟩) (Pi.π (fun _ : Fin 2 => M gpt) 0)
      (Pi.π (fun _ : Fin 2 => M gpt) 1)).trans ((grpReduct_homMul ⟨M⟩ _ _).trans ?_)
    exact ((piLift_two_π (M gpt)) =≫ funMap (M := M) gMul).trans (Category.id_comp _)
  | one =>
    refine (monObj_toUnit_one (A := (grpReduct C).obj ⟨M⟩) _).trans
      ((grpReduct_homOne ⟨M⟩ _).trans ?_)
    exact (congrArg (· ≫ funMap (M := M) gOne) (piLift_zero_eq _ (𝟙 _))).trans
      (Category.id_comp _)
  | inv =>
    exact (Category.assoc _ _ _).symm.trans
      (((piLift_one_π (M gpt)) =≫ funMap (M := M) gInv).trans (Category.id_comp _))

variable (C) in
/-- Passing from models of the theory of groups to group objects and back is the identity
functor. -/
lemma modelToGrp_grpToModel : modelToGrp C ⋙ grpToModel C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun A => by
    obtain ⟨M⟩ := A
    exact ofGrp_modelToGrp M)
  (fun A B g => MSLanguage.Hom.ext (funext fun s => by
    refine Eq.trans ?_ (MSLanguage.comp_toFun _ _ s).symm
    refine Eq.trans ?_ (((MSLanguage.modelCat_eqToHom_toFun _ s) =≫ _).symm)
    refine Eq.trans ?_ ((_ ≫= (MSLanguage.comp_toFun _ _ s)).symm)
    refine Eq.trans ?_ (congr(_ ≫ _ ≫ $((MSLanguage.modelCat_eqToHom_toFun _ s).symm)))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

/-- A group object is recovered from its model of the theory of groups. -/
lemma modelToGrp_ofGrp (M : C) [GrpObj M] :
    (modelToGrp C).obj (ofGrp C (Grp.mk M)) = Grp.mk M := by
  rw [modelToGrp_obj]
  congr 1
  refine GrpObj.ext _ _ (MonObj.ext _ _ ?_)
  refine (Category.id_comp _).symm.trans ?_
  refine (((lift_fst_snd (X := M) (Y := M)) =≫
    (monObj ((grpReduct C).obj (ofGrp C (Grp.mk M)))).mul).symm).trans ?_
  refine (monObj_lift_mul (A := (grpReduct C).obj (ofGrp C (Grp.mk M))) (fst M M)
    (snd M M)).trans ((grpReduct_homMul (ofGrp C (Grp.mk M)) _ _).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (((piLift_two_lift _ _).trans lift_fst_snd) =≫ μ[M]).trans (Category.id_comp _)

variable (C) in
/-- Passing from group objects to models of the theory of groups and back is the identity
functor. -/
lemma grpToModel_modelToGrp : grpToModel C ⋙ modelToGrp C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun M => by
    obtain ⟨M⟩ := M
    exact modelToGrp_ofGrp M)
  (fun M N f => InducedCategory.hom_ext (Mon.Hom.ext (by
    refine Eq.trans ?_ (grp_comp_hom _ _).symm
    refine Eq.trans ?_ (((grp_eqToHom_hom _) =≫ _).symm)
    refine Eq.trans ?_ ((_ ≫= (grp_comp_hom _ _)).symm)
    refine Eq.trans ?_ (congr(_ ≫ _ ≫ $((grp_eqToHom_hom _).symm)))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm)))

end GrpLaws

end UlmerBialgebras.Paper.ClassicalModels
