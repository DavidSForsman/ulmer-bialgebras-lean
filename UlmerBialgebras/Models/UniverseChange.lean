module

public import UlmerBialgebras.Models.CatPIE
public import UlmerBialgebras.Models.CatCells
public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Basic.ConjEq
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Change of universe for Σ-models in `CAT`

The change of universe `Cat.{v, max u v} → Cat.{max u v, max u v}` keeps the objects of a
category and lifts its morphisms with `ULiftHom` (`UlmerBialgebras.UnivChange.upCat`). It acts on
functors and natural transformations (`upHom`, `upCell`), and it commutes with the chosen finite
products of `CAT` up to the comparison functor `piUp`, which is the identity on objects.

A Σ-model `M` in `Cat.{v, max u v}` gives a Σ-model `upModel M` in `Cat.{max u v, max u v}`.

## Main definitions

* `UlmerBialgebras.UnivChange.upCat`, `upHom`, `upCell`: the change of universe.
* `UlmerBialgebras.UnivChange.piUp`: the comparison of products.
* `UlmerBialgebras.UnivChange.upModel`: the Σ-model with lifted morphisms.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], §3
-/

@[expose] public section

universe w v u u₁ u₂ u₃

namespace UlmerBialgebras

/-- Two models with equal premodels and heterogeneously equal transformation cells are equal. -/
lemma Model.ext_heq {Sg : TwoSig} {Obj : Type*} [CategoryTheory.Bicategory Obj]
    [CategoryTheory.Bicategory.Strict Obj]
    [HasChosenFinProducts Obj] {M N : Model Sg Obj} (hP : M.toPreModel = N.toPreModel)
    (htr : ∀ a, HEq (M.tr a) (N.tr a)) : M = N := by
  obtain ⟨P, t⟩ := M
  obtain ⟨Q, t'⟩ := N
  dsimp only at hP htr
  subst hP
  obtain rfl : t = t' := funext fun a => eq_of_heq (htr a)
  rfl

end UlmerBialgebras

namespace UlmerBialgebras.UnivChange

open CategoryTheory
open scoped CategoryTheory.Bicategory

/-! ## Categories, functors and natural transformations -/

/-- The change of universe of a category: the same objects, morphisms lifted to
`Type (max u v)`. -/
abbrev upCat (C : Cat.{v, max u v}) : Cat.{max u v, max u v} := Cat.of (ULiftHom.{max u v} C)

variable {C D E : Cat.{v, max u v}}

/-- The change of universe of a functor. -/
def upHom (F : C ⟶ D) : upCat C ⟶ upCat D :=
  Functor.toCatHom
    { obj := fun x => F.toFunctor.obj x
      map := fun f => ULift.up (F.toFunctor.map f.down)
      map_id := fun x => ULift.ext (F.toFunctor.map_id x)
      map_comp := fun f g => ULift.ext (F.toFunctor.map_comp f.down g.down) }

/-- The change of universe of functors preserves composition. -/
lemma upHom_comp (F : C ⟶ D) (G : D ⟶ E) : upHom (F ≫ G) = upHom F ≫ upHom G := rfl

/-- The change of universe of a natural transformation. -/
def upCell {F G : C ⟶ D} (α : F ⟶ G) : upHom F ⟶ upHom G :=
  NatTrans.toCatHom₂
    { app := fun x => ULift.up (α.toNatTrans.app x)
      naturality := fun _ _ f => ULift.ext (α.toNatTrans.naturality f.down) }

/-- The lift of a category, as a functor into the lifted category. -/
def upFunctor (C : Cat.{v, max u v}) : C ⥤ upCat C where
  obj x := x
  map f := ULift.up f

/-- The inverse of `upFunctor`. -/
def downFunctor (C : Cat.{v, max u v}) : upCat C ⥤ C where
  obj x := x
  map f := f.down

/-! ## Products -/

/-- The comparison from the product of the lifted categories to the lifted product: the identity
on objects. -/
def piUp {n : ℕ} (c : Fin n → Cat.{v, max u v}) :
    (HasChosenFinProducts.finProd (fun i => upCat (c i))).pt ⟶
      upCat (HasChosenFinProducts.finProd c).pt :=
  Functor.toCatHom
    { obj := fun x => x
      map := fun f => ULift.up (fun i => (f i).down)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }


/-- The comparison of products commutes with the projections. -/
lemma piUp_π {n : ℕ} (c : Fin n → Cat.{v, max u v}) (i : Fin n) :
    piUp c ≫ upHom ((HasChosenFinProducts.finProd c).π i) =
      (HasChosenFinProducts.finProd (fun i => upCat (c i))).π i := rfl

/-- The comparison of products commutes with the lifts. -/
lemma lift_piUp {n : ℕ} (c : Fin n → Cat.{v, max u v}) {x : Cat.{v, max u v}}
    {y : Cat.{max u v, max u v}} (φ : y ⟶ upCat x) (g : ∀ i, x ⟶ c i) :
    (HasChosenFinProducts.finProd (fun i => upCat (c i))).lift (fun i => φ ≫ upHom (g i)) ≫
      piUp c = φ ≫ upHom ((HasChosenFinProducts.finProd c).lift g) := rfl

/-! ## The lifted model -/

variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-- The premodel with lifted morphisms. -/
def upPreModel (M : PreModel Sg Cat.{v, max u v}) : PreModel Sg Cat.{max u v, max u v} where
  obj c := upCat (M.obj c)
  fn B := piUp (fun i => M.obj (Sg.art B i)) ≫ upHom (M.fn B)

/-- The interpretation of a term in the lifted premodel, at an environment lifted from `M`. -/
lemma upPreModel_interp (M : PreModel Sg Cat.{v, max u v}) {V : Type} {vty : V → Sg.Cat}
    {x : Cat.{v, max u v}} {y : Cat.{max u v, max u v}} (φ : y ⟶ upCat x)
    (ρ : ∀ w, x ⟶ M.obj (vty w)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    (upPreModel M).interp (fun w => φ ≫ upHom (ρ w)) t = φ ≫ upHom (M.interp ρ t) := by
  induction t with
  | var w => rfl
  | app B args ih =>
    rw [PreModel.interp_app, PreModel.interp_app, funext ih]
    exact lift_piUp _ φ _ =≫ upHom (M.fn B)

/-- The lifted Σ-model: the same objects, morphisms lifted to `Type (max u v)`. -/
def upModel (M : Model Sg Cat.{v, max u v}) : Model Sg Cat.{max u v, max u v} where
  toPreModel := upPreModel M.toPreModel
  tr a := eqToHom (upPreModel_interp M.toPreModel (piUp _) (M.Pctx a).π (Sg.trsrc a)) ≫
    (piUp _ ◁ upCell (M.tr a)) ≫
    eqToHom (upPreModel_interp M.toPreModel (piUp _) (M.Pctx a).π (Sg.trtgt a)).symm


/-- The transformation cells of the lifted model are the lifted ones of `M`. -/
lemma upModel_tr (M : Model Sg Cat.{v, max u v}) (a : Sg.Tr) :
    (upModel.{v, u} M).tr a =
      eqToHom (upPreModel_interp M.toPreModel (piUp _) (M.Pctx a).π (Sg.trsrc a)) ≫
        (piUp _ ◁ upCell (M.tr a)) ≫
        eqToHom (upPreModel_interp M.toPreModel (piUp _) (M.Pctx a).π (Sg.trtgt a)).symm :=
  rfl

/-! ## Products of size `0` -/

/-- The comparison from the product of the lifted categories to the lifted product, for the
products of size `0`: the identity on objects. -/
def piUpS {ι : Type} (c : ι → Cat.{v, max u v}) :
    (HasChosenProductsOfSize.prod (fun i => upCat (c i))).pt ⟶
      upCat (HasChosenProductsOfSize.prod c).pt :=
  Functor.toCatHom
    { obj := fun x => x
      map := fun f => ULift.up (fun i => (f i).down)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }

/-- The inverse comparison of products of size `0`. -/
def piDownS {ι : Type} (c : ι → Cat.{v, max u v}) :
    upCat (HasChosenProductsOfSize.prod c).pt ⟶
      (HasChosenProductsOfSize.prod (fun i => upCat (c i))).pt :=
  Functor.toCatHom
    { obj := fun x => x
      map := fun f => fun i => ULift.up (f.down i)
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }

/-- The comparison `piUpS c` followed by its inverse `piDownS c` is the identity. -/
lemma piUpS_piDownS {ι : Type} (c : ι → Cat.{v, max u v}) : piUpS c ≫ piDownS c = 𝟙 _ := rfl

/-- The inverse comparison `piDownS c` followed by `piUpS c` is the identity. -/
lemma piDownS_piUpS {ι : Type} (c : ι → Cat.{v, max u v}) : piDownS c ≫ piUpS c = 𝟙 _ := rfl

/-- The comparison of products of size `0` commutes with the projections. -/
lemma piUpS_π {ι : Type} (c : ι → Cat.{v, max u v}) (i : ι) :
    piUpS c ≫ upHom ((HasChosenProductsOfSize.prod c).π i) =
      (HasChosenProductsOfSize.prod (fun i => upCat (c i))).π i := rfl

/-- The comparison of products of size `0` commutes with the lifts. -/
lemma lift_piUpS {ι : Type} (c : ι → Cat.{v, max u v}) {x : Cat.{v, max u v}}
    {y : Cat.{max u v, max u v}} (φ : y ⟶ upCat x) (g : ∀ i, x ⟶ c i) :
    (HasChosenProductsOfSize.prod (fun i => upCat (c i))).lift (fun i => φ ≫ upHom (g i)) ≫
      piUpS c = φ ≫ upHom ((HasChosenProductsOfSize.prod c).lift g) := rfl

/-! ## Terms and arities of the lifted model -/

namespace Model

variable (M : Model Sg Cat.{v, max u v}) (sg : OneSig.{u₁, u₂, u₃, 0, 0} Sg)

/-- The closed terms of the lifted model are the lifted closed terms of `M`, after the comparison
of products. -/
lemma upModel_tm {c : Sg.Cat} (t : sg.CTrm c) :
    (upModel M).tm sg t = piUpS _ ≫ upHom (M.tm sg t) :=
  upPreModel_interp M.toPreModel (piUpS _) (M.P0 sg).π t

/-- The arities of the lifted model are the lifted arities of `M`, after the comparisons of
products. -/
lemma upModel_domCell :
    (upModel M).domCell sg ≫ piUpS _ = piUpS _ ≫ upHom (M.domCell sg) := by
  unfold UlmerBialgebras.Model.domCell
  simp only [upModel_tm]
  rfl

/-- The coarities of the lifted model are the lifted coarities of `M`, after the comparisons of
products. -/
lemma upModel_codCell :
    (upModel M).codCell sg ≫ piUpS _ = piUpS _ ≫ upHom (M.codCell sg) := by
  unfold UlmerBialgebras.Model.codCell
  simp only [upModel_tm]
  rfl

end Model


/-! ## Inserters -/

section Ins

variable {C₁ : Type*} [Category C₁] {D₁ : Type*} [Category D₁] {C₂ : Type*} [Category C₂]
  {D₂ : Type*} [Category D₂] {F G : C₁ ⥤ D₁} {F' G' : C₂ ⥤ D₂}

/-- The functor between inserters induced by a commuting square of functors. -/
def insMap (α : C₁ ⥤ C₂) (β : D₁ ⥤ D₂) (hF : F ⋙ β = α ⋙ F') (hG : G ⋙ β = α ⋙ G') :
    Ins F G ⥤ Ins F' G' :=
  Ins.liftFunctor (Ins.forget F G ⋙ α)
    (eqToHom (by rw [Functor.assoc, ← hF]; rfl) ≫ Functor.whiskerRight (Ins.cellNat F G) β ≫
      eqToHom (by rw [Functor.assoc, hG]; rfl))

/-- The underlying object of the image of `z` under `insMap` is the image under `α` of the
underlying object of `z`. -/
@[simp] lemma insMap_obj_pt (α : C₁ ⥤ C₂) (β : D₁ ⥤ D₂) (hF : F ⋙ β = α ⋙ F')
    (hG : G ⋙ β = α ⋙ G') (z : Ins F G) : ((insMap α β hF hG).obj z).pt = α.obj z.pt := rfl

/-- The underlying morphism of the image of `g` under `insMap` is the image under `α` of the
underlying morphism of `g`. -/
@[simp] lemma insMap_map_base (α : C₁ ⥤ C₂) (β : D₁ ⥤ D₂) (hF : F ⋙ β = α ⋙ F')
    (hG : G ⋙ β = α ⋙ G') {z z' : Ins F G} (g : z ⟶ z') :
    ((insMap α β hF hG).map g).base = α.map g.base := rfl

/-- The structure morphism of the image of `z` under `insMap` is the image under `β` of the
structure morphism of `z`, conjugated by `eqToHom`s. -/
lemma insMap_obj_cell (α : C₁ ⥤ C₂) (β : D₁ ⥤ D₂) (hF : F ⋙ β = α ⋙ F')
    (hG : G ⋙ β = α ⋙ G') (z : Ins F G) :
    ((insMap α β hF hG).obj z).cell =
      eqToHom (Functor.congr_obj hF z.pt).symm ≫ β.map z.cell ≫
        eqToHom (Functor.congr_obj hG z.pt) := by
  simp [insMap]

/-- The structure morphism of the image of `z` under `insMap` is `ConjEq` to the image under `β` of
the structure morphism of `z`. -/
lemma insMap_cell_conjEq (α : C₁ ⥤ C₂) (β : D₁ ⥤ D₂) (hF : F ⋙ β = α ⋙ F')
    (hG : G ⋙ β = α ⋙ G') (z : Ins F G) :
    ConjEq ((insMap α β hF hG).obj z).cell (β.map z.cell) := by
  rw [insMap_obj_cell]
  exact ConjEq.conj _ _ _

end Ins

section InsUp

variable {C D : Cat.{v, max u v}}

/-- The inserter of lifted functors is the lifted inserter: one direction. -/
def insDown (F G : C ⟶ D) :
    Ins (upHom F).toFunctor (upHom G).toFunctor ⥤
      ULiftHom.{max u v} (Ins F.toFunctor G.toFunctor) where
  obj z := (⟨z.pt, z.cell.down⟩ : Ins F.toFunctor G.toFunctor)
  map g := ULift.up ⟨g.base.down, ULift.ext_iff.mp g.w⟩

/-- The inserter of lifted functors is the lifted inserter: the other direction. -/
def insUp (F G : C ⟶ D) :
    ULiftHom.{max u v} (Ins F.toFunctor G.toFunctor) ⥤
      Ins (upHom F).toFunctor (upHom G).toFunctor where
  obj z := ⟨(z : Ins F.toFunctor G.toFunctor).pt, ULift.up (z : Ins F.toFunctor G.toFunctor).cell⟩
  map g := ⟨ULift.up g.down.base, ULift.ext g.down.w⟩

/-- `insDown F G` followed by `insUp F G` is the identity functor. -/
lemma insDown_insUp (F G : C ⟶ D) : insDown F G ⋙ insUp F G = 𝟭 _ := rfl

/-- `insUp F G` followed by `insDown F G` is the identity functor. -/
lemma insUp_insDown (F G : C ⟶ D) : insUp F G ⋙ insDown F G = 𝟭 _ := rfl

end InsUp



/-! ## `ConjEq` for lifted morphisms and components -/

section ConjEqUp

/-- Functors preserve `ConjEq`. -/
lemma conjEq_map {C : Type*} [Category C] {D : Type*} [Category D] (Φ : C ⥤ D) {X Y X' Y' : C}
    {a : X ⟶ Y} {b : X' ⟶ Y'} (h : ConjEq a b) : ConjEq (Φ.map a) (Φ.map b) := by
  obtain ⟨p, q, rfl⟩ := h
  subst p q
  exact ConjEq.of_eq (by simp)

/-- The underlying morphism of an `eqToHom` of the lifted category is an `eqToHom`. -/
lemma ulift_eqToHom_down {C : Type*} [Category C] {X Y : ULiftHom.{w} C} (e : X = Y) :
    (eqToHom e).down = eqToHom (congrArg ULiftHom.objDown e) := by
  subst e; rfl

/-- In a lifted category of families, `ConjEq` passes to the components of the underlying
families. -/
lemma conjEq_down_proj {I : Type*} {C : I → Type*} [∀ i, Category (C i)]
    {X Y X' Y' : ULiftHom.{w} (∀ i, C i)} {a : X ⟶ Y} {b : X' ⟶ Y'} (h : ConjEq a b) (i : I) :
    ConjEq (a.down i) (b.down i) := by
  obtain ⟨p, q, rfl⟩ := h
  subst p q
  exact ConjEq.of_eq (by rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- Components of a 2-cell at equal objects are `ConjEq`. -/
lemma conjEq_app_congr {A B : Cat.{v, u}} {F G : A ⟶ B} (α : F ⟶ G) {x y : A} (h : x = y) :
    ConjEq (α.toNatTrans.app x) (α.toNatTrans.app y) := by
  subst h
  exact ConjEq.of_eq rfl

/-- The component of a conjugate by `eqToHom`s of a 2-cell of `Cat` is `ConjEq` to the
component of the 2-cell. -/
lemma conjEq_app {A B : Cat.{v, u}} {F F' G' G : A ⟶ B} (p : F = F') (q : G' = G)
    (X : F' ⟶ G') (z : A) :
    ConjEq ((eqToHom p ≫ X ≫ eqToHom q).toNatTrans.app z) (X.toNatTrans.app z) := by
  subst p q
  exact ConjEq.of_eq (by simp)

/-- In a category of families, `ConjEq` holds as soon as it holds componentwise. -/
lemma conjEq_pi {I : Type*} {C : I → Type*} [∀ i, Category (C i)] {X Y X' Y' : ∀ i, C i}
    {a : X ⟶ Y} {b : X' ⟶ Y'} (h : ∀ i, ConjEq (a i) (b i)) : ConjEq a b := by
  choose p q hpq using h
  obtain rfl : X = X' := funext p
  obtain rfl : Y = Y' := (funext q).symm
  exact ConjEq.of_eq (funext fun i => (hpq i).trans (by simp))

/-- A component of an `eqToHom` 2-cell of `Cat` is `ConjEq` to any `eqToHom` with the same
source. -/
lemma conjEq_eqToHom_app {A B : Cat.{v, u}} {F G : A ⟶ B} (h : F = G) (x : A) {Y Y' : B}
    (q : Y = Y') (hx : F.toFunctor.obj x = Y) :
    ConjEq ((eqToHom h).toNatTrans.app x) (eqToHom q) := by
  subst h hx q
  exact ConjEq.of_eq (by simp)

/-- Objects of an inserter are equal if their underlying objects are and their structure
morphisms are `ConjEq`. -/
lemma Ins.obj_ext_of_conjEq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {x y : Ins F G} (h : x.pt = y.pt) (hc : ConjEq x.cell y.cell) : x = y :=
  Ins.obj_ext h (by obtain ⟨p, q, e⟩ := hc; exact e)

/-- The underlying morphism of a morphism of inserters conjugated by `eqToHom`s is its underlying
morphism conjugated by the induced `eqToHom`s. -/
lemma ins_conj_base {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {x x' y y' : Ins F G} (e₁ : x = x') (g : x' ⟶ y') (e₂ : y' = y) :
    (eqToHom e₁ ≫ g ≫ eqToHom e₂).base =
      eqToHom (congrArg Ins.pt e₁) ≫ g.base ≫ eqToHom (congrArg Ins.pt e₂) := by
  subst e₁ e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- In the lifted category of an inserter, the underlying morphism of a morphism conjugated by
`eqToHom`s is its underlying morphism conjugated by the induced `eqToHom`s. -/
lemma uliftIns_conj_base {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {x x' y y' : ULiftHom.{w} (Ins F G)} (e₁ : x = x') (g : x' ⟶ y') (e₂ : y' = y) :
    (eqToHom e₁ ≫ g ≫ eqToHom e₂).down.base =
      eqToHom (congrArg (fun z => (ULiftHom.objDown z).pt) e₁) ≫ g.down.base ≫
        eqToHom (congrArg (fun z => (ULiftHom.objDown z).pt) e₂) := by
  subst e₁ e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- A morphism is equal to its conjugate by `eqToHom`s of self-equalities. -/
lemma eq_conj_eqToHom_self {C : Type*} [Category C] {X Y : C} (p : X = X) (m : X ⟶ Y)
    (q : Y = Y) : m = eqToHom p ≫ m ≫ eqToHom q := by
  simp

/-- In a full subcategory of an inserter, the underlying morphism of a morphism conjugated by
`eqToHom`s is its underlying morphism conjugated by the induced `eqToHom`s. -/
lemma equifIns_conj_base {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {P : ObjectProperty (Ins F G)} {x x' y y' : P.FullSubcategory} (e₁ : x = x') (g : x' ⟶ y')
    (e₂ : y' = y) :
    (eqToHom e₁ ≫ g ≫ eqToHom e₂).hom.base =
      eqToHom (congrArg (fun z => z.obj.pt) e₁) ≫ g.hom.base ≫
        eqToHom (congrArg (fun z => z.obj.pt) e₂) := by
  subst e₁ e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- In the lifted category of a full subcategory of an inserter, the underlying morphism of a
morphism conjugated by `eqToHom`s is its underlying morphism conjugated by the induced `eqToHom`s.
-/
lemma uliftEquifIns_conj_base {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    {P : ObjectProperty (Ins F G)} {x x' y y' : ULiftHom.{w} P.FullSubcategory} (e₁ : x = x')
    (g : x' ⟶ y') (e₂ : y' = y) :
    (eqToHom e₁ ≫ g ≫ eqToHom e₂).down.hom.base =
      eqToHom (congrArg (fun z => (ULiftHom.objDown z).obj.pt) e₁) ≫ g.down.hom.base ≫
        eqToHom (congrArg (fun z => (ULiftHom.objDown z).obj.pt) e₂) := by
  subst e₁ e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end ConjEqUp

/-- The components of the transformation cells of the lifted model. -/
lemma upModel_tr_app (M : Model Sg Cat.{v, max u v}) (a : Sg.Tr)
    (w : ((upModel.{v, u} M).Pctx a).pt) :
    ConjEq (((upModel.{v, u} M).tr a).toNatTrans.app w)
      ((upCell (M.tr a)).toNatTrans.app ((piUp.{v, u} _).toFunctor.obj w)) := by
  rw [upModel_tr]
  exact conjEq_app _ _ _ w

end UlmerBialgebras.UnivChange
