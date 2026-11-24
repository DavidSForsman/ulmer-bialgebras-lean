module

public import Companion.Statements.DefsClassical
public import Companion.Proofs.ExtrasTheoryMorphism
public import UlmerBialgebras.Proofs.Sec5.ExtrasAlgTheory
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Models of the classical theories as Mathlib's internal monoids and groups

Helpers for `Companion/Proofs/ExtrasClassical.lean`. A model of the theory of monoids in a cartesian
category `C` makes each hom-set `Y ⟶ X` a monoid, naturally in `Y`; Mathlib's
`MonObj.ofRepresentableBy` turns this into a monoid object. Conversely, a monoid object
interprets `mul` and `one` through Mathlib's monoid structure on hom-sets (`Hom.monoid`), and the
equations become monoid identities.

* `ev x t`: a term evaluated at generalized elements `x i : Y ⟶ M (Γ i)`; `lift_realize`.

Commutative monoids and groups are in `Companion/Proofs/ClassicalModelsCMonGrp.lean`.

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapter 1
-/

@[expose] public section

universe v u w u₁ u₂

namespace UlmerBialgebras.Paper.ClassicalModels

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MSLanguage

/-! ## Terms at generalized elements -/

section Ev

variable {L : MSLanguage.{u₁, u₂}} {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  (M : L.Sorts → C) [L.Structure M]

/-- A term evaluated at generalized elements `x i : Y ⟶ M (Γ i)`. -/
noncomputable def ev {Y : C} {n : ℕ} {Γ : Fin n → L.Sorts} (x : ∀ i, Y ⟶ M (Γ i)) :
    ∀ {s : L.Sorts}, L.Term Γ s → (Y ⟶ M s)
  | _, .var i => x i
  | _, .func f ts => Pi.lift (fun j => ev x (ts j)) ≫ funMap f

/-- A variable evaluates to its generalized element. -/
@[simp] lemma ev_var {Y : C} {n : ℕ} {Γ : Fin n → L.Sorts} (x : ∀ i, Y ⟶ M (Γ i)) (i : Fin n) :
    ev M x (.var i) = x i := rfl

/-- A function symbol applied to terms evaluates to the tuple of their evaluations followed by
the interpretation of the symbol. -/
lemma ev_func {Y : C} {n : ℕ} {Γ : Fin n → L.Sorts} (x : ∀ i, Y ⟶ M (Γ i)) (f : L.Functions)
    (ts : ∀ j, L.Term Γ (L.argSorts f j)) :
    ev M x (.func f ts) = Pi.lift (fun j => ev M x (ts j)) ≫ funMap f := rfl

/-- Realizing a term and precomposing with a tuple is evaluating at the tuple. -/
lemma lift_realize {Y : C} {n : ℕ} {Γ : Fin n → L.Sorts} (x : ∀ i, Y ⟶ M (Γ i)) :
    ∀ {s : L.Sorts} (t : L.Term Γ s), Pi.lift x ≫ t.realize M = ev M x t
  | _, .var i => Pi.lift_comp_π _ i
  | _, .func f ts => by
    rw [Term.realize, ← Category.assoc, ev]
    congr 1
    exact Pi.hom_ext _ _ fun j => by simp [lift_realize x (ts j)]

omit [L.Structure M] in
/-- A tuple followed by a product of maps. -/
lemma piLift_map {Y : C} {n : ℕ} {P Q : Fin n → C} (x : ∀ i, Y ⟶ P i) (g : ∀ i, P i ⟶ Q i) :
    Pi.lift x ≫ Limits.Pi.map g = Pi.lift (fun i => x i ≫ g i) :=
  Pi.hom_ext _ _ fun j => by simp

/-- An equation realized in `M` holds at all generalized elements. -/
lemma ev_eq_of_realize {φ : L.Equation} (h : φ.Realize M) {Y : C} (x : ∀ i, Y ⟶ M (φ.ctx i)) :
    ev M x φ.lhs = ev M x φ.rhs := by
  rw [← lift_realize, ← lift_realize]
  exact (Pi.lift x ≫= h)

/-- The realization of a term is its evaluation at the projections. -/
lemma realize_eq_ev {n : ℕ} {Γ : Fin n → L.Sorts} {s : L.Sorts} (t : L.Term Γ s) :
    t.realize M = ev M (Pi.π _) t := by
  rw [← lift_realize, Pi.lift_π, Category.id_comp]

end Ev

/-! ## Models of the theory of monoids give monoid objects -/

section MonModel

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (A : monTheory.ModelCat C)

/-- The symbol `mul` of the language of monoids. -/
abbrev mulSym : monLanguage.Functions := ⟨((), .mul), nofun⟩

/-- The symbol `one` of the language of monoids. -/
abbrev oneSym : monLanguage.Functions := ⟨((), .one), nofun⟩

/-- The sort of the language of monoids. -/
abbrev pt : monLanguage.Sorts := ()

/-- The carrier of a model of the theory of monoids. -/
abbrev X : C := A.Carrier pt

variable {A}

/-- The product of two generalized elements of a model. -/
noncomputable def homMul {Y : C} (f g : Y ⟶ X A) : Y ⟶ X A :=
  Pi.lift (C := C) (f := fun _ : Fin 2 => X A) ![f, g] ≫ funMap (M := A.Carrier) mulSym

/-- The unit as a generalized element of a model. -/
noncomputable def homOne (Y : C) : Y ⟶ X A :=
  Pi.lift (C := C) (f := fun _ : Fin 0 => X A) (fun i => i.elim0) ≫ funMap (M := A.Carrier) oneSym

/-- Evaluating a product term gives the product of the evaluations. -/
lemma ev_monMul {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ X A)
    (a b : monLanguage.Term (fun _ : Fin n => ()) ()) :
    ev A.Carrier x (monMul a b) = homMul (ev A.Carrier x a) (ev A.Carrier x b) := by
  refine ((congrArg Pi.lift (funext fun j => ?_)) =≫ funMap (M := A.Carrier) mulSym)
  fin_cases j <;> rfl

/-- Evaluating the unit term gives the unit. -/
lemma ev_monOne {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ X A) :
    ev A.Carrier x (monOne (Γ := fun _ : Fin n => ())) = homOne Y :=
  ((congrArg Pi.lift (funext fun j => j.elim0)) =≫ funMap (M := A.Carrier) oneSym)

/-- A model satisfies the monoid equations on generalized elements. -/
lemma monEq (e : MonEqn) {Y : C} (x : ∀ _ : Fin (monEquation e).ctxLen, Y ⟶ X A) :
    ev A.Carrier x (monEquation e).lhs = ev A.Carrier x (monEquation e).rhs :=
  ev_eq_of_realize A.Carrier (A.is_model.realize_of_mem _ ⟨e, rfl⟩) x

/-- The unit is a left unit for the product of generalized elements. -/
lemma homOne_mul {Y : C} (f : Y ⟶ X A) : homMul (homOne Y) f = f := by
  have := monEq (A := A) .one_mul ![f]
  simp only [monEquation, ev_monMul, ev_monOne] at this
  exact this

/-- The unit is a right unit for the product of generalized elements. -/
lemma homMul_one {Y : C} (f : Y ⟶ X A) : homMul f (homOne Y) = f := by
  have := monEq (A := A) .mul_one ![f]
  simp only [monEquation, ev_monMul, ev_monOne] at this
  exact this

/-- The product of generalized elements is associative. -/
lemma homMul_assoc {Y : C} (f g h : Y ⟶ X A) :
    homMul (homMul f g) h = homMul f (homMul g h) := by
  have := monEq (A := A) .mul_assoc ![f, g, h]
  simp only [monEquation, ev_monMul] at this
  exact this

/-- Precomposition distributes over the product of generalized elements. -/
lemma comp_homMul {Y Y' : C} (u : Y' ⟶ Y) (f g : Y ⟶ X A) :
    u ≫ homMul f g = homMul (u ≫ f) (u ≫ g) :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ funMap (M := A.Carrier) mulSym)
        (Pi.hom_ext _ _ fun j => by fin_cases j <;> simp))

/-- Precomposition preserves the unit generalized element. -/
lemma comp_homOne {Y Y' : C} (u : Y' ⟶ Y) : u ≫ homOne (A := A) Y = homOne Y' :=
  (Category.assoc _ _ _).symm.trans
    (((Pi.hom_ext _ _ fun j => j.elim0) =≫ funMap (M := A.Carrier) oneSym))

variable (A) in
/-- The monoid of generalized elements of a model of the theory of monoids. -/
@[implicit_reducible]
noncomputable def homMonoid (Y : C) : Monoid (Y ⟶ X A) where
  mul := homMul
  one := homOne Y
  mul_assoc := homMul_assoc
  one_mul := homOne_mul
  mul_one := homMul_one

variable (A) in
/-- The presheaf of monoids of generalized elements. -/
noncomputable def homPresheaf : Cᵒᵖ ⥤ MonCat.{v} where
  obj Y := @MonCat.of (Y.unop ⟶ X A) (homMonoid A Y.unop)
  map {Y Y'} u :=
    letI := homMonoid A Y.unop
    letI := homMonoid A Y'.unop
    MonCat.ofHom
      { toFun f := u.unop ≫ f
        map_one' := comp_homOne u.unop
        map_mul' f g := comp_homMul u.unop f g }

variable (A) in
/-- The carrier represents the presheaf of generalized elements. -/
noncomputable def homPresheafRepresentableBy :
    (homPresheaf A ⋙ forget _).RepresentableBy (X A) where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

variable (A) in
/-- **The monoid object of a model of the theory of monoids.** -/
@[implicit_reducible]
noncomputable def monObj : MonObj (X A) :=
  MonObj.ofRepresentableBy (X A) (homPresheaf A) (homPresheafRepresentableBy A)

end MonModel

section MonObjLemmas

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A : monTheory.ModelCat C}

open scoped MonObj

/-- The multiplication of `monObj A` is `homMul` of the two projections. -/
lemma monObj_mul : (monObj A).mul = homMul (fst (X A) (X A)) (snd (X A) (X A)) := rfl

/-- The multiplication of `monObj A` on generalized elements is `homMul`. -/
lemma monObj_lift_mul {Y : C} (f g : Y ⟶ X A) :
    lift f g ≫ (monObj A).mul = homMul f g := by
  rw [monObj_mul, comp_homMul, lift_fst, lift_snd]

/-- The unit of `monObj A` on generalized elements is `homOne`. -/
lemma monObj_toUnit_one (Y : C) :
    toUnit Y ≫ (monObj A).one = homOne Y :=
  comp_homOne (toUnit Y)

end MonObjLemmas

/-! ## Monoid objects give models of the theory of monoids -/

section OfMon

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

/-- The interpretation of the language of monoids by a monoid object. -/
@[implicit_reducible]
noncomputable def monStructure (M : C) [MonObj M] : monLanguage.Structure (C := C) fun _ => M where
  funMap
    | ⟨((), .mul), _⟩ => show (∏ᶜ fun _ : Fin 2 => M) ⟶ M from
        lift (Pi.π (fun _ : Fin 2 => M) 0) (Pi.π (fun _ : Fin 2 => M) 1) ≫ μ
    | ⟨((), .one), _⟩ => toUnit _ ≫ η
    | ⟨((), .inv), h⟩ => absurd rfl h

/-- The monoid object interprets `mul` as its multiplication `μ`. -/
lemma monStructure_mul (M : C) [MonObj M] :
    (monStructure M).funMap mulSym =
      lift (Pi.π (fun _ : Fin 2 => M) 0) (Pi.π (fun _ : Fin 2 => M) 1) ≫ μ := rfl

/-- The monoid object interprets `one` as its unit `η`. -/
lemma monStructure_one (M : C) [MonObj M] :
    (monStructure M).funMap oneSym = toUnit _ ≫ η := rfl

attribute [local instance] monStructure

/-- For the interpretation by a monoid object, evaluating a product term gives the product of the
evaluations in the monoid `Y ⟶ M`. -/
lemma ev_monMul_ofMon (M : C) [MonObj M] {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M)
    (a b : monLanguage.Term (fun _ : Fin n => ()) ()) :
    ev (fun _ => M) x (monMul a b) = ev (fun _ => M) x a * ev (fun _ => M) x b := by
  refine (ev_func (fun _ => M) (Γ := fun _ => pt) x _ _).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (((comp_lift _ _ _).trans
      congr(lift $(Pi.lift_comp_π (fun j => ev (fun _ => M) x (![a, b] j)) 0)
        $(Pi.lift_comp_π (fun j => ev (fun _ => M) x (![a, b] j)) 1))) =≫ μ[M])

/-- For the interpretation by a monoid object, evaluating the unit term gives `1` in the monoid
`Y ⟶ M`. -/
lemma ev_monOne_ofMon (M : C) [MonObj M] {Y : C} {n : ℕ} (x : ∀ _ : Fin n, Y ⟶ M) :
    ev (fun _ => M) x (monOne (Γ := fun _ : Fin n => ())) = 1 := by
  refine (ev_func (fun _ => M) (Γ := fun _ => pt) x _ _).trans ?_
  rw [monStructure_one, ← Category.assoc, comp_toUnit]
  rfl

/-- A monoid object is a model of the theory of monoids. -/
lemma monStructure_model (M : C) [MonObj M] :
    (fun _ : monLanguage.Sorts => M) ⊨ monTheory := by
  refine ⟨?_⟩
  rintro _ ⟨e, rfl⟩
  change Term.realize _ _ = Term.realize _ _
  rw [realize_eq_ev, realize_eq_ev]
  cases e <;> simp only [monEquation, ev_monMul_ofMon, ev_monOne_ofMon]
  · exact one_mul _
  · exact mul_one _
  · exact mul_assoc _ _ _

variable (C) in
/-- The model of the theory of monoids of a monoid object. -/
noncomputable def ofMon (M : Mon C) : monTheory.ModelCat C :=
  haveI := monStructure_model M.X
  ⟨fun _ : monLanguage.Sorts => M.X⟩

end OfMon

/-! ## The isomorphism `Mod_C(T_Mon) ≅ Mon C` -/

section MonIso

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local instance] monStructure

/-- A homomorphism of models preserves the product of generalized elements. -/
lemma homMul_comp {A B : monTheory.ModelCat C} (g : A ⟶ B) {Y : C} (f₁ f₂ : Y ⟶ X A) :
    homMul f₁ f₂ ≫ g.toFun pt = homMul (f₁ ≫ g.toFun pt) (f₂ ≫ g.toFun pt) :=
  (Category.assoc _ _ _).trans ((_ ≫= g.map_fun' mulSym).trans
    ((Category.assoc _ _ _).symm.trans ((((piLift_map (Y := Y) ![f₁, f₂] _).trans
        (congrArg Pi.lift (funext fun j => by fin_cases j <;> rfl))) =≫
          funMap (M := B.Carrier) mulSym))))

/-- A homomorphism of models preserves the unit generalized element. -/
lemma homOne_comp {A B : monTheory.ModelCat C} (g : A ⟶ B) (Y : C) :
    homOne (A := A) Y ≫ g.toFun pt = homOne Y :=
  (Category.assoc _ _ _).trans ((_ ≫= g.map_fun' oneSym).trans
    ((Category.assoc _ _ _).symm.trans (((Pi.hom_ext _ _ fun j => j.elim0) =≫
      funMap (M := B.Carrier) oneSym))))

/-- A homomorphism of models is a homomorphism of the monoid objects. -/
lemma isMonHom_of_hom {A B : monTheory.ModelCat C} (g : A ⟶ B) :
    @IsMonHom C _ _ (X A) (X B) (monObj A) (monObj B) (g.toFun pt) := by
  let := monObj A
  let := monObj B
  refine ⟨?_, ?_⟩
  · rw [← Category.id_comp (monObj A).one, ← Category.id_comp (monObj B).one,
      ← toUnit_unique (toUnit (𝟙_ C)) (𝟙 _), monObj_toUnit_one, monObj_toUnit_one, homOne_comp]
  · rw [← Category.id_comp (monObj A).mul, ← Category.id_comp (g.toFun pt ⊗ₘ g.toFun pt),
      ← lift_fst_snd, monObj_lift_mul, homMul_comp, lift_map, monObj_lift_mul]

variable (C) in
/-- Models of the theory of monoids to monoid objects. -/
noncomputable def modelToMon : monTheory.ModelCat C ⥤ Mon C where
  obj A := @Mon.mk C _ _ (X A) (monObj A)
  map g := @Mon.Hom.mk C _ _ _ _ (g.toFun pt) (isMonHom_of_hom g)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `modelToMon C` sends a model to its carrier with the monoid object `monObj A`. -/
lemma modelToMon_obj (A : monTheory.ModelCat C) :
    (modelToMon C).obj A = @Mon.mk C _ _ (X A) (monObj A) := rfl

/-- A homomorphism of monoid objects is a homomorphism of the models. -/
noncomputable def homOfMon {M N : Mon C} (f : M ⟶ N) : ofMon C M ⟶ ofMon C N where
  toFun _ := f.hom
  map_fun'
    | ⟨((), .mul), _⟩ => by
      change (lift (Pi.π (fun _ : Fin 2 => M.X) 0) (Pi.π (fun _ : Fin 2 => M.X) 1) ≫ μ) ≫ f.hom =
        Limits.Pi.map (fun _ => f.hom) ≫
          lift (Pi.π (fun _ : Fin 2 => N.X) 0) (Pi.π (fun _ : Fin 2 => N.X) 1) ≫ μ
      rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, ← Category.assoc, lift_map,
        comp_lift, Limits.Pi.map_π, Limits.Pi.map_π]
    | ⟨((), .one), _⟩ => by
      change (toUnit _ ≫ η) ≫ f.hom = Limits.Pi.map (fun _ => f.hom) ≫ toUnit _ ≫ η
      rw [Category.assoc, IsMonHom.one_hom, ← Category.assoc, comp_toUnit]
    | ⟨((), .inv), h⟩ => absurd rfl h

variable (C) in
/-- Monoid objects to models of the theory of monoids. -/
noncomputable def monToModel : Mon C ⥤ monTheory.ModelCat C where
  obj M := ofMon C M
  map f := homOfMon f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `monToModel C` sends a monoid object to its model `ofMon C M`. -/
lemma monToModel_obj (M : Mon C) : (monToModel C).obj M = ofMon C M := rfl

end MonIso

section MonIsoLaws

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local instance] monStructure

/-- The components of an `eqToHom` between monoid objects. -/
lemma mon_eqToHom_hom {M N : Mon C} (h : M = N) :
    (eqToHom h).hom = eqToHom (congrArg Mon.X h) := by
  subst h
  rfl

/-- The tuple of the two projections of a power indexed by `Fin 2` is the identity. -/
lemma piLift_two_π (Y : C) :
    Pi.lift (C := C) (f := fun _ : Fin 2 => Y) ![Pi.π _ 0, Pi.π _ 1] = 𝟙 _ :=
  Pi.hom_ext _ _ fun j => by fin_cases j <;> simp

/-- The projection `0` of the tuple `![a, b]` is `a`. -/
lemma piLift_two_π0 {Y Z : C} (a b : Y ⟶ Z) :
    Pi.lift (C := C) (f := fun _ : Fin 2 => Z) ![a, b] ≫ Pi.π (fun _ : Fin 2 => Z) 0 = a :=
  Pi.lift_comp_π _ _

/-- The projection `1` of the tuple `![a, b]` is `b`. -/
lemma piLift_two_π1 {Y Z : C} (a b : Y ⟶ Z) :
    Pi.lift (C := C) (f := fun _ : Fin 2 => Z) ![a, b] ≫ Pi.π (fun _ : Fin 2 => Z) 1 = b :=
  Pi.lift_comp_π _ _

/-- The tuple `![a, b]` followed by the comparison of the power indexed by `Fin 2` with the binary
product is `lift a b`. -/
lemma piLift_two_lift {Y Z : C} (a b : Y ⟶ Z) :
    Pi.lift (C := C) (f := fun _ : Fin 2 => Z) ![a, b] ≫
      lift (Pi.π (fun _ : Fin 2 => Z) 0) (Pi.π (fun _ : Fin 2 => Z) 1) = lift a b := by
  rw [comp_lift, piLift_two_π0, piLift_two_π1]

/-- Any two morphisms into a power indexed by `Fin 0` are equal. -/
lemma piLift_zero_eq {Y Z : C} (a b : Y ⟶ ∏ᶜ fun _ : Fin 0 => Z) : a = b :=
  Pi.hom_ext _ _ fun j => j.elim0

/-- The model of the monoid object of a model of the theory of monoids is the model itself. -/
lemma ofMon_modelToMon (M : monLanguage.Sorts → C) [monLanguage.Structure M] [M ⊨ monTheory] :
    ofMon C ((modelToMon C).obj ⟨M⟩) = ⟨M⟩ := by
  refine MSLanguage.modelCat_mk_eq _ _ (fun f => ?_) _ _
  obtain ⟨⟨⟨⟩, op⟩, h⟩ := f
  cases op
  · refine (monObj_lift_mul (A := ⟨M⟩) (Pi.π (fun _ : Fin 2 => M pt) 0)
      (Pi.π (fun _ : Fin 2 => M pt) 1)).trans ?_
    exact (((piLift_two_π (M pt)) =≫ funMap (M := M) mulSym)).trans (Category.id_comp _)
  · refine (monObj_toUnit_one (A := ⟨M⟩) _).trans ?_
    exact (congrArg (· ≫ funMap (M := M) oneSym) (piLift_zero_eq _ (𝟙 _))).trans
      (Category.id_comp _)
  · exact absurd rfl h

variable (C) in
/-- `modelToMon C` followed by `monToModel C` is the identity functor. -/
lemma modelToMon_monToModel : modelToMon C ⋙ monToModel C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun A => by
    obtain ⟨M⟩ := A
    exact ofMon_modelToMon M)
  (fun A B g => MSLanguage.Hom.ext (funext fun s => by
    refine Eq.trans ?_ (MSLanguage.comp_toFun _ _ s).symm
    refine Eq.trans ?_ ((MSLanguage.modelCat_eqToHom_toFun _ s).symm =≫ _)
    refine Eq.trans ?_ (_ ≫= (MSLanguage.comp_toFun _ _ s).symm)
    refine Eq.trans ?_ ((_ ≫= _ ≫= (MSLanguage.modelCat_eqToHom_toFun _ s).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

variable (C) in
/-- `monToModel C` followed by `modelToMon C` is the identity functor. -/
lemma monToModel_modelToMon : monToModel C ⋙ modelToMon C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun M => by
    obtain ⟨M⟩ := M
    rw [Functor.comp_obj, monToModel_obj, modelToMon_obj, Functor.id_obj]
    congr 1
    refine MonObj.ext _ _ ?_
    refine (Category.id_comp _).symm.trans ?_
    refine (((lift_fst_snd (X := M) (Y := M)).symm =≫ (monObj (ofMon C ⟨M⟩)).mul)).trans ?_
    refine (monObj_lift_mul (A := ofMon C ⟨M⟩) (fst M M) (snd M M)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact ((piLift_two_lift _ _).trans lift_fst_snd =≫ μ[M]).trans
        (Category.id_comp _))
  (fun M N f => Mon.Hom.ext (by
    refine Eq.trans ?_ (Mon.comp_hom _ _).symm
    refine Eq.trans ?_ ((mon_eqToHom_hom _).symm =≫ _)
    refine Eq.trans ?_ (_ ≫= (Mon.comp_hom _ _).symm)
    refine Eq.trans ?_ ((_ ≫= _ ≫= (mon_eqToHom_hom _).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

end MonIsoLaws

/-! ## From models to `Σ_Cart`-models -/

section CartThy

/-- An isomorphism of `Mod_C(T)` with a category over `C` gives one of `C^{T'}`, by
`modelCat_iso_cartThy_univ`. -/
lemma cartThy_iso_of (C : Type (max v w)) [Category.{v} C] [CartesianMonoidalCategory C]
    {D : Type*} [Category D]
    (U : D ⥤ C) {L : MSLanguage.{0, 0}} (T : L.Theory) (x : L.Sorts)
    (F : T.ModelCat C ⥤ D) (G : D ⥤ T.ModelCat C) (h₁ : F ⋙ G = 𝟭 _) (h₂ : G ⋙ F = 𝟭 _)
    (h₃ : F ⋙ U = Theory.ModelCat.forget C T ⋙ Pi.eval (fun _ => C) x) :
    ∃ (F' : Theory.cartThy.{v, w, 0} C T ⥤ D) (G' : D ⥤ Theory.cartThy.{v, w, 0} C T),
      F' ⋙ G' = 𝟭 _ ∧ G' ⋙ F' = 𝟭 _ ∧
        F' ⋙ U = Theory.cartThyForget.{v, w, 0} C T ⋙ Pi.eval (fun _ => C) x := by
  obtain ⟨F₁, G₁, k₁, k₂, k₃⟩ := modelCat_iso_cartThy_univ.{v, w, 0} C T
  refine ⟨G₁ ⋙ F, G ⋙ F₁, ?_, ?_, ?_⟩
  · calc (G₁ ⋙ F) ⋙ G ⋙ F₁ = G₁ ⋙ (F ⋙ G) ⋙ F₁ := rfl
      _ = 𝟭 _ := by rw [h₁]; exact k₂
  · calc (G ⋙ F₁) ⋙ G₁ ⋙ F = G ⋙ (F₁ ⋙ G₁) ⋙ F := rfl
      _ = 𝟭 _ := by rw [k₁]; exact h₂
  · calc (G₁ ⋙ F) ⋙ U = G₁ ⋙ (F ⋙ U) := rfl
      _ = G₁ ⋙ (F₁ ⋙ Theory.cartThyForget.{v, w, 0} C T) ⋙ Pi.eval (fun _ => C) x := by
          rw [h₃, k₃]
      _ = (G₁ ⋙ F₁) ⋙ Theory.cartThyForget.{v, w, 0} C T ⋙ Pi.eval (fun _ => C) x := rfl
      _ = _ := by rw [k₂]; rfl

end CartThy

end UlmerBialgebras.Paper.ClassicalModels
