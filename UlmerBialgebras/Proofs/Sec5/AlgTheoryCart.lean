module

public import UlmerBialgebras.Paper.Sec6DefsAlgTheory
public import UlmerBialgebras.Proofs.Sec5.CartSigCalc
public import UlmerBialgebras.Proofs.Sec5.AlgTheoryTransport

/-!
# Models of an equational theory as `Σ_Cart`-models

For a cartesian monoidal category `B` (objects in `max s v w`, morphisms in `max s v`, above the
size `s`) and an equational theory `T` over a language `L : MSLanguage.{s, s}`, the category of
models of `T` in `B` is isomorphic, over `B^S`, to the category `B^{T'}` of models of the translated
`Σ_Cart`-theory `T'` in the `Σ_Cart`-model `B`.

* The term `prodTrm Γ` evaluates at `x : S → B` to `x(Γ₀) ⊗ (x(Γ₁) ⊗ ⋯)`, a product of the
  `x(Γᵢ)` with the projections built from `fst` and `snd` (`isLimit`); `cmp` compares it with the
  chosen product `∏ᶜ`.
* The path of a term evaluates to its realization (`interpPath_toPath`).

## Main results

* `UlmerBialgebras.Paper.MSLanguage.CartIso.modelCat_iso_cartThy`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19 and Definition 3.14
-/

@[expose] public section


universe s v w

namespace UlmerBialgebras.Paper.MSLanguage.CartIso

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Cart
  Cart.SigCalc

attribute [local instance] catOfSizeHom
attribute [local implicit_reducible] toCartSig

variable {B : Type (max s v w)} [Category.{max s v} B] [CartesianMonoidalCategory B]
  {L : MSLanguage.{s, s}}

section Monoidal

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- An `eqToHom` between tensor products with a common left factor is `𝟙 ⊗ₘ eqToHom`. -/
lemma eqToHom_tensor_left {X Y Y' : D} (h : X ⊗ Y = X ⊗ Y') (h₂ : Y = Y') :
    eqToHom h = 𝟙 X ⊗ₘ eqToHom h₂ := by
  subst h₂; simp

end Monoidal

section InsFullSubcategory

variable {C' D' : Type*} [Category C'] [Category D'] {F' G' : C' ⥤ D'}
  {Q : ObjectProperty (Ins F' G')}

/-- In a full subcategory of an inserter category, the underlying morphism of `eqToHom h` is the
`eqToHom` of the equality of the underlying objects. -/
lemma fullSubcategory_eqToHom_hom_base {X Y : Q.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom.base = eqToHom (congrArg (fun X : Q.FullSubcategory => X.obj.pt) h) := by
  subst h
  rfl

end InsFullSubcategory

/-! ## The product `x(Γ₀) ⊗ (x(Γ₁) ⊗ ⋯)` -/

variable (x : L.Sorts → B)

/-- The object of `prodTrm Γ` at `x`. -/
def P {n : ℕ} (Γ : Fin n → L.Sorts) : B :=
  ((cartModel B).tm L.toCartSig (prodTrm Γ)).toFunctor.obj x

/-- The projections of `P x Γ`. -/
def prodπ : ∀ {n : ℕ} (Γ : Fin n → L.Sorts) (i : Fin n), P x Γ ⟶ x (Γ i)
  | 0, _, i => i.elim0
  | 1, _, ⟨0, _⟩ => 𝟙 _
  | _ + 2, Γ, ⟨0, _⟩ => fst (x (Γ 0)) (P x (Fin.tail Γ))
  | _ + 2, Γ, ⟨k + 1, h⟩ => snd (x (Γ 0)) (P x (Fin.tail Γ)) ≫ prodπ (Fin.tail Γ) ⟨k, by omega⟩

/-- The morphism into `P x Γ` induced by a family of morphisms. -/
def prodLift {Y : B} : ∀ {n : ℕ} {Γ : Fin n → L.Sorts}, (∀ i, Y ⟶ x (Γ i)) → (Y ⟶ P x Γ)
  | 0, _, _ => toUnit Y
  | 1, _, g => g 0
  | _ + 2, _, g => lift (g 0) (prodLift (fun i => g i.succ))

/-- `prodLift g` followed by the `i`-th projection is `g i`. -/
@[reassoc (attr := simp)]
lemma prodLift_π {Y : B} : ∀ {n : ℕ} {Γ : Fin n → L.Sorts} (g : ∀ i, Y ⟶ x (Γ i)) (i : Fin n),
    prodLift x g ≫ prodπ x Γ i = g i
  | 0, _, _, i => i.elim0
  | 1, _, _, ⟨0, _⟩ => Category.comp_id _
  | _ + 2, _, g, ⟨0, _⟩ => lift_fst (g 0) _
  | _ + 2, _, g, ⟨k + 1, h⟩ =>
      (lift_snd_assoc (g 0) _ _).trans (prodLift_π (fun i => g i.succ) ⟨k, by omega⟩)

/-- Morphisms into `P x Γ` agreeing on all projections are equal. -/
lemma prodπ_ext {Y : B} : ∀ {n : ℕ} {Γ : Fin n → L.Sorts} {f g : Y ⟶ P x Γ},
    (∀ i, f ≫ prodπ x Γ i = g ≫ prodπ x Γ i) → f = g
  | 0, _, _, _, _ => toUnit_unique _ _
  | 1, _, f, g, h => by
      have h0 : f ≫ 𝟙 _ = g ≫ 𝟙 _ := h 0
      simpa using h0
  | _ + 2, Γ, f, g, h => by
      refine CartesianMonoidalCategory.hom_ext _ _ (h 0) (prodπ_ext (fun i => ?_))
      have hi : f ≫ (snd _ _ ≫ prodπ x (Fin.tail Γ) i) = g ≫ (snd _ _ ≫ prodπ x (Fin.tail Γ) i) :=
        h i.succ
      exact (Category.assoc _ _ _).trans (hi.trans (Category.assoc _ _ _).symm)

/-- `P x Γ`, with the projections `prodπ`, is a product of the `x (Γ i)`. -/
def isLimit {n : ℕ} (Γ : Fin n → L.Sorts) :
    IsLimit (Fan.mk (P x Γ) (prodπ x Γ)) :=
  Fan.IsLimit.mk _ (fun c => prodLift x c.proj) (fun c i => prodLift_π x c.proj i)
    (fun c _m hm => prodπ_ext x (fun i => (hm i).trans (prodLift_π x c.proj i).symm))

/-- The comparison of `P x Γ` with the chosen product `∏ᶜ`. -/
noncomputable def cmp {n : ℕ} (Γ : Fin n → L.Sorts) : P x Γ ≅ ∏ᶜ fun i => x (Γ i) :=
  (isLimit x Γ).conePointUniqueUpToIso (limit.isLimit _)

/-- `cmp` is compatible with the projections. -/
@[reassoc (attr := simp)]
lemma cmp_hom_π {n : ℕ} (Γ : Fin n → L.Sorts) (i : Fin n) :
    (cmp x Γ).hom ≫ Pi.π _ i = prodπ x Γ i :=
  (isLimit x Γ).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨i⟩

/-- `cmp⁻¹` is compatible with the projections. -/
@[reassoc (attr := simp)]
lemma cmp_inv_π {n : ℕ} (Γ : Fin n → L.Sorts) (i : Fin n) :
    (cmp x Γ).inv ≫ prodπ x Γ i = Pi.π _ i :=
  (isLimit x Γ).conePointUniqueUpToIso_inv_comp (limit.isLimit _) ⟨i⟩

/-! ## Evaluating the paths of the translation -/

variable {x}

variable (z : SigObj B L.toCartSig)

/-- The family of objects of `z ∈ M^σ`. -/
def base : L.Sorts → B := Ins.pt z

/-- The structure map of `z ∈ M^σ` at a function symbol. -/
def cell (f : L.Functions) : P (base z) (L.argSorts f) ⟶ base z (L.resSort f) := Ins.cell z f

/-- The object of a term at `z ∈ M^σ` is its object at the underlying family `base z`. -/
lemma hz {n : ℕ} (Γ : Fin n → L.Sorts) : interpTerm z (prodTrm Γ) = P (base z) Γ :=
  Functor.congr_obj (Cat.Hom.ext_iff.mp ((cartModel B).sigTm_eq L.toCartSig (prodTrm Γ))) z

/-- The projection path `prodTrm Γ → Γᵢ` evaluates to the projection `prodπ`. -/
lemma interpPath_projPath : ∀ {n : ℕ} (Γ : Fin n → L.Sorts) (i : Fin n),
    interpPath (projPath Γ i) z = eqToHom (hz z (Γ)) ≫ prodπ (base z) Γ i
  | 0, _, i => i.elim0
  | 1, Γ, ⟨0, _⟩ => (interpPath_nil z (prodTrm Γ)).trans (Category.comp_id _).symm
  | _ + 2, Γ, ⟨0, _⟩ => by
      have E := eqToHom_tensor_left (X := show B from (base z) (Γ 0)) (hz z (Γ))
        (hz z ((Fin.tail Γ)))
      exact (interpPath_fstPath z (.var (Γ 0)) (prodTrm (Fin.tail Γ))).trans
        ((Category.comp_id _).symm.trans ((tensorHom_fst _ _).symm.trans
          (E.symm =≫ fst _ _)))
  | _ + 2, Γ, ⟨k + 1, h⟩ => by
      have h₁ := interpPath_comp z (sndPath (.var (Γ 0)) (prodTrm (Fin.tail Γ)))
        (projPath (Fin.tail Γ) ⟨k, by omega⟩)
      have h₂ := interpPath_sndPath z (.var (Γ 0)) (prodTrm (Fin.tail Γ))
      have h₃ := interpPath_projPath (Fin.tail Γ) ⟨k, by omega⟩
      rw [h₂, h₃] at h₁
      have E := eqToHom_tensor_left (X := show B from (base z) (Γ 0)) (hz z (Γ))
        (hz z ((Fin.tail Γ)))
      exact h₁.trans ((tensorHom_snd_assoc _ _ _).symm.trans
        (E.symm =≫ snd _ _ ≫ prodπ (base z) (Fin.tail Γ) ⟨k, by omega⟩))

/-- The tupling path evaluates to `prodLift` of the evaluations. -/
lemma interpPath_tuplePath {u : L.toCartSig.CTrm ()} : ∀ {m : ℕ} {b : Fin m → L.Sorts}
    (ps : ∀ j, L.toCartSig.Path u (.var (b j))),
    interpPath (tuplePath ps) z =
      prodLift (base z) (fun j => interpPath (ps j) z) ≫ eqToHom (hz z b).symm
  | 0, _, _ => (interpPath_toUnitPath z u).trans (Category.comp_id _).symm
  | 1, _, ps => (Category.comp_id (interpPath (ps 0) z)).symm
  | _ + 2, b, ps => by
      have h₁ := interpPath_liftPath z (ps 0) (tuplePath (fun j => ps j.succ))
      have h₂ := interpPath_tuplePath (fun j => ps j.succ)
      rw [h₂] at h₁
      have E := eqToHom_tensor_left (X := show B from base z (b 0))
        (hz z b).symm
        (hz z (Fin.tail b)).symm
      exact h₁.trans (((lift_map (interpPath (ps 0) z)
          (prodLift (base z) fun j => interpPath (ps j.succ) z) (𝟙 _)
          (eqToHom (hz z (Fin.tail b)).symm)).trans
          congr(lift $(Category.comp_id (interpPath (ps 0) z)) _)).symm.trans
        (_ ≫= E.symm))

/-- The arrow of a function symbol evaluates to the cell of `z`, up to `hz`. -/
lemma interpArr_fn (f : L.Functions) :
    interpArr ((cartModel B).arrCell L.toCartSig (OneSig.Arr.fn (sg := L.toCartSig) f)) z =
      eqToHom (hz z ((L.argSorts f))) ≫ cell z f := by
  rw [Model.arrCell_fn]
  simp only [interpArr, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app]
  exact (eqToHom _ ≫= Category.comp_id (cell z f))

/-! ## The structure of an object of `M^σ` and its terms -/

variable (x) in
/-- `prodLift` of a family precomposed with `g` is `g ≫ prodLift`. -/
lemma prodLift_comp {Y Y' : B} {n : ℕ} {Γ : Fin n → L.Sorts} (g : Y' ⟶ Y)
    (h : ∀ i, Y ⟶ x (Γ i)) : prodLift x (fun i => g ≫ h i) = g ≫ prodLift x h :=
  prodπ_ext x (fun i => by rw [prodLift_π, Category.assoc, prodLift_π])

variable (x) in
/-- `prodLift` is `Pi.lift` followed by the comparison `cmp⁻¹`. -/
lemma prodLift_eq {Y : B} {n : ℕ} {Γ : Fin n → L.Sorts} (h : ∀ i, Y ⟶ x (Γ i)) :
    prodLift x h = Pi.lift h ≫ (cmp x Γ).inv :=
  prodπ_ext x (fun i => by
    rw [prodLift_π, Category.assoc, cmp_inv_π, limit.lift_π]
    rfl)

/-- The `L`-structure of `z ∈ M^σ`: `funMap f = cmp⁻¹ ≫ z_f`. -/
noncomputable instance struc : L.Structure (base z) where
  funMap f := (cmp (base z) (L.argSorts f)).inv ≫ cell z f

/-- **The path of a term evaluates to its realization**, up to `hz` and `cmp`. -/
lemma interpPath_toPath {n : ℕ} {Γ : Fin n → L.Sorts} : ∀ {a : L.Sorts} (u : L.Term Γ a),
    interpPath u.toPath z =
      eqToHom (hz z (Γ)) ≫ (cmp (base z) Γ).hom ≫ u.realize (base z)
  | _, .var i => by
      rw [Term.toPath, interpPath_projPath, Term.realize, cmp_hom_π]
  | _, .func f ts => by
      refine (interpPath_comp z (tuplePath (fun j => (ts j).toPath))
        (arrPath (OneSig.Arr.fn (sg := L.toCartSig) f))).trans ?_
      calc
        _ = (prodLift (base z) (fun j => interpPath (ts j).toPath z) ≫
              eqToHom (hz z (L.argSorts f)).symm) ≫ (eqToHom (hz z (L.argSorts f)) ≫ cell z f) :=
            congrArg₂ (· ≫ ·) (interpPath_tuplePath z _)
              ((interpPath_arrPath z _).trans (interpArr_fn z f))
        _ = prodLift (base z) (fun j => interpPath (ts j).toPath z) ≫ cell z f := by
            rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        _ = prodLift (base z) (fun j => eqToHom (hz z Γ) ≫ (cmp (base z) Γ).hom ≫
              (ts j).realize (base z)) ≫ cell z f :=
            congr(prodLift (base z) fun j => $(interpPath_toPath (ts j))) =≫ cell z f
        _ = eqToHom (hz z Γ) ≫ (cmp (base z) Γ).hom ≫
              Pi.lift (fun j => (ts j).realize (base z)) ≫
                (cmp (base z) (L.argSorts f)).inv ≫ cell z f := by
            rw [prodLift_comp, prodLift_comp, prodLift_eq]
            simp only [Category.assoc]

/-- The realization of a variable, read on `P`: a projection. -/
lemma cmp_hom_realize_var {n : ℕ} {Γ : Fin n → L.Sorts} (i : Fin n) :
    (cmp (base z) Γ).hom ≫ (Term.var i : L.Term Γ (Γ i)).realize (base z) = prodπ (base z) Γ i :=
  cmp_hom_π _ Γ i

/-- The realization of `f(t₀, …)`, read on `P`: the tuple of the realizations of the `tᵢ`
followed by the cell of `f`. -/
lemma cmp_hom_realize_func {n : ℕ} {Γ : Fin n → L.Sorts} (f : L.Functions)
    (ts : ∀ i : Fin (L.arity f), L.Term Γ (L.argSorts f i)) :
    (cmp (base z) Γ).hom ≫ (Term.func f ts).realize (base z) =
      prodLift (base z) (fun j => (cmp (base z) Γ).hom ≫ (ts j).realize (base z)) ≫ cell z f := by
  rw [prodLift_comp, prodLift_eq, Category.assoc, Category.assoc]
  rfl

/-! ## The defining condition of `M^{T'}` -/

variable {T : L.Theory}

/-- The component at `z` and `φ` of the left-hand cell of `M^{T'}` evaluates the path of the
left-hand side of `φ`. -/
lemma lhsCell_app (φ : T.toCartTheory.Eqn) :
    ((cartModel B).lhsCell L.toCartSig T.toCartTheory).toNatTrans.app z φ =
      interpPath φ.1.lhs.toPath z := by
  rw [Model.lhsCell]
  simp only [catOfSize_lift₂_app, Cat.Hom.comp_toFunctor, Cat.Hom.toNatTrans_comp,
      Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The component at `z` and `φ` of the right-hand cell of `M^{T'}` evaluates the path of the
right-hand side of `φ`. -/
lemma rhsCell_app (φ : T.toCartTheory.Eqn) :
    ((cartModel B).rhsCell L.toCartSig T.toCartTheory).toNatTrans.app z φ =
      interpPath φ.1.rhs.toPath z := by
  rw [Model.rhsCell]
  simp only [catOfSize_lift₂_app, Cat.Hom.comp_toFunctor, Cat.Hom.toNatTrans_comp,
      Cat.Hom₂.eqToHom_toNatTrans, NatTrans.comp_app, Functor.comp_obj, eqToHom_app]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- **The defining condition of `M^{T'}`**: `z ∈ M^σ` lies in `M^{T'}` iff its induced
structure is a model of `T`. -/
lemma equifProp_iff :
    ((cartModel B).lhsCell L.toCartSig T.toCartTheory).toNatTrans.app z =
        ((cartModel B).rhsCell L.toCartSig T.toCartTheory).toNatTrans.app z ↔ (base z) ⊨ T := by
  refine funext_iff.trans ⟨fun h => ⟨fun φ hφ => ?_⟩, fun h φ => ?_⟩
  · have hφ' := ((lhsCell_app.{s, v, w} z ⟨φ, hφ⟩).symm.trans (h ⟨φ, hφ⟩)).trans
      (rhsCell_app.{s, v, w} z ⟨φ, hφ⟩)
    rw [interpPath_toPath.{s, v, w}, interpPath_toPath.{s, v, w}] at hφ'
    exact (cancel_epi _).1 ((cancel_epi _).1 hφ')
  · refine (lhsCell_app.{s, v, w} z φ).trans (Eq.trans ?_ (rhsCell_app.{s, v, w} z φ).symm)
    rw [interpPath_toPath.{s, v, w}, interpPath_toPath.{s, v, w}, h.realize_of_mem φ.1 φ.2]

/-! ## Naturality of the comparison -/

variable {y : L.Sorts → B}

/-- The morphism `P x Γ ⟶ P y Γ` induced by a family of morphisms. -/
def Pmap (h : ∀ a, x a ⟶ y a) {n : ℕ} (Γ : Fin n → L.Sorts) : P x Γ ⟶ P y Γ :=
  ((cartModel B).tm L.toCartSig (prodTrm Γ)).toFunctor.map (X := x) (Y := y) h

/-- `Pmap` commutes with the projections. -/
@[reassoc]
lemma pmap_π (h : ∀ a, x a ⟶ y a) : ∀ {n : ℕ} (Γ : Fin n → L.Sorts) (i : Fin n),
    Pmap h Γ ≫ prodπ y Γ i = prodπ x Γ i ≫ h (Γ i)
  | 0, _, i => i.elim0
  | 1, _, ⟨0, _⟩ => (Category.comp_id _).trans (Category.id_comp _).symm
  | _ + 2, Γ, ⟨0, _⟩ => tensorHom_fst _ _
  | _ + 2, Γ, ⟨k + 1, hk⟩ =>
      (tensorHom_snd_assoc _ _ _).trans
        ((snd _ _ ≫= pmap_π h (Fin.tail Γ) ⟨k, by omega⟩).trans
          (Category.assoc _ _ _).symm)

/-- `cmp` is natural. -/
@[reassoc]
lemma pmap_cmp (h : ∀ a, x a ⟶ y a) {n : ℕ} (Γ : Fin n → L.Sorts) :
    Pmap h Γ ≫ (cmp y Γ).hom = (cmp x Γ).hom ≫ Limits.Pi.map (fun i => h (Γ i)) := by
  refine Pi.hom_ext _ _ (fun i => ?_)
  rw [Category.assoc, cmp_hom_π, pmap_π, Category.assoc, Pi.map_π, cmp_hom_π_assoc]

/-- A cell commuting with `Pmap` gives, after `cmp⁻¹`, a map commuting with `Pi.map`. -/
lemma cmp_inv_comp_of_comm (h : ∀ a, x a ⟶ y a) {n : ℕ} {Γ : Fin n → L.Sorts} {r : L.Sorts}
    {c : P x Γ ⟶ x r} {c' : P y Γ ⟶ y r} (hw : c ≫ h r = Pmap h Γ ≫ c') :
    ((cmp x Γ).inv ≫ c) ≫ h r = Limits.Pi.map (fun i => h (Γ i)) ≫ (cmp y Γ).inv ≫ c' := by
  rw [Category.assoc, hw, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq]
  exact ((Iso.eq_comp_inv _).2 (pmap_cmp h Γ)).trans (Category.assoc _ _ _)

/-! ## The isomorphism -/

variable (B T)

/-- The model of `T'` of a model of `T`: the family with the cells `cmp ≫ funMap f`. -/
noncomputable def toCartObj (A : T.ModelCat B) : T.cartThy B where
  obj := ⟨A.Carrier, fun f => (cmp A.Carrier (L.argSorts f)).hom ≫ A.struc.funMap f⟩
  property := by
    refine (equifProp_iff.{s, v, w} (B := B) (T := T) ⟨A.Carrier, _⟩).2 ?_
    have h : struc ⟨A.Carrier, fun f => (cmp A.Carrier (L.argSorts f)).hom ≫ A.struc.funMap f⟩ =
        A.struc := by
      obtain @⟨A, S, _⟩ := A
      obtain ⟨g⟩ := S
      exact congrArg Structure.mk (funext fun f => Iso.inv_hom_id_assoc _ (g f))
    exact (congrArg (fun S => @Theory.Model L B _ _ A.Carrier S T) h).mpr A.is_model

/-- **From models of `T` to models of `T'`.** -/
noncomputable def toCart : T.ModelCat B ⥤ T.cartThy B where
  obj := toCartObj B T
  map {A A'} g := ObjectProperty.homMk
    { base := fun a => g.toFun a
      w := funext fun f => by
        refine (Category.assoc _ _ _).trans (((cmp A.Carrier _).hom ≫= g.map_fun' f).trans ?_)
        exact ((pmap_cmp_assoc (fun a => g.toFun a) (L.argSorts f) _).symm) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **From models of `T'` to models of `T`.** -/
noncomputable def ofCart : T.cartThy B ⥤ T.ModelCat B where
  obj t := @Theory.ModelCat.mk L B _ _ T (base t.obj) (struc t.obj)
    ((equifProp_iff.{s, v, w} (T := T) t.obj).1 t.property)
  map {t t'} g :=
    { toFun := fun a => g.hom.base a
      map_fun' := fun f => by
        have hw : cell t.obj f ≫ g.hom.base (L.resSort f) =
            Pmap (fun a => g.hom.base a) (L.argSorts f) ≫ cell t'.obj f :=
          congr($(g.hom.w) f)
        exact cmp_inv_comp_of_comm _ hw }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `ofCart` is a left inverse of `toCart`. -/
lemma toCart_ofCart : toCart B T ⋙ ofCart B T = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) (fun A A' g => ?_)
  · obtain @⟨M, ⟨g⟩, hM⟩ := A
    exact modelCat_eq _ _ (fun f => Iso.inv_hom_id_assoc _ (g f))
  · refine Hom.ext (funext fun a => ?_)
    rw [comp_toFun, comp_toFun]
    refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (eqToHom_toFun _ a).symm
      ((_ ≫= eqToHom_toFun _ a).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- `ofCart` is a right inverse of `toCart`. -/
lemma ofCart_toCart : ofCart B T ⋙ toCart B T = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun t t' g => ?_)
  · obtain ⟨⟨x, c⟩, hp⟩ := t
    refine ObjectProperty.FullSubcategory.ext (Ins.obj_ext rfl ?_)
    exact (funext fun f => Iso.hom_inv_id_assoc _ (c f)).trans
      ((Category.id_comp _).trans (Category.comp_id _)).symm
  · obtain ⟨⟨x, c⟩, hp⟩ := t
    obtain ⟨⟨x', c'⟩, hp'⟩ := t'
    refine ObjectProperty.hom_ext _ (Ins.hom_ext ?_)
    refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (fullSubcategory_eqToHom_hom_base _).symm
      ((_ ≫= fullSubcategory_eqToHom_hom_base _).symm))
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- `toCart` lies over the forgetful functors to `B^S`. -/
lemma toCart_forget : toCart B T ⋙ T.cartThyForget B = Theory.ModelCat.forget B T := by
  exact CategoryTheory.Functor.ext (fun A => rfl)
    (fun A A' g => ((Category.id_comp _).trans (Category.comp_id _)).symm)

/-- **Models of `T` in `B` are the models of `T'` in the `Σ_Cart`-model `B`**, over `B^S`. -/
theorem modelCat_iso_cartThy :
    ∃ (F : T.ModelCat B ⥤ T.cartThy B) (G : T.cartThy B ⥤ T.ModelCat B),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧ F ⋙ T.cartThyForget B = Theory.ModelCat.forget B T :=
  ⟨toCart B T, ofCart B T, toCart_ofCart B T, ofCart_toCart B T, toCart_forget B T⟩

end UlmerBialgebras.Paper.MSLanguage.CartIso
