module

public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Models.CatPIE
public import UlmerBialgebras.Basic.HomCat

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The representable model `K(x, M)`

For a `Σ`-model `M` in a 2-category `K` and an object `x` of `K`, the `Σ`-model `K(x, M)` in
`CAT` sends a category symbol `c` to the hom-category `K(x, M_c)` and a functor symbol `B` to the
functor `(h₁, …, hₙ) ↦ ⟨h₁, …, hₙ⟩ ≫ M(B)`. A transformation symbol `α` goes to the natural
transformation whose component at an environment `ρ` is `M(α)` at `ρ` (`Model.trAt`).

This is the model in Remark 3.17 of [forsman2026syntactic]: `M^T` is characterized by an
isomorphism of categories `K(x, M^T) ≅ K(x, M)^T`, natural in `x`.

## Main definitions

* `UlmerBialgebras.PreModel.homPreModel M x`: the interpretation of the category and functor
  symbols in `K(x, M)`.
* `UlmerBialgebras.Model.homModel M x`: the `Σ`-model `K(x, M)` in `Cat.{w, v}`.

## Main results

* `UlmerBialgebras.PreModel.homPreModel_interp_obj`: a term is interpreted in `K(x, M)`, at an
  environment `ρ`, as it is interpreted in `M` at `ρ`.
* `UlmerBialgebras.PreModel.homPreModel_interp_map`: on 2-cells, as `PreModel.interpCell`.
* `UlmerBialgebras.PreModel.homPreModel_interp_obj_env`: the same on objects, at any environment
  of functors.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17
-/


universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace PreModel

variable (M : PreModel Sg Obj) (x : Obj)

/-- The functor `K(x, M_{c₁}) × ⋯ × K(x, M_{cₙ}) ⥤ K(x, M_d)`, `(hᵢ) ↦ ⟨hᵢ⟩ ≫ M(B)`, of a
functor symbol `B : c₁ ⋯ cₙ → d`. -/
@[simps]
def homFn (B : Sg.Fun) : (∀ i, (x ⟶ M.obj (Sg.art B i))) ⥤ (x ⟶ M.obj (Sg.fcod B)) where
  obj p := (M.P B).lift p ≫ M.fn B
  map γ := M.appCell B γ
  map_id p := M.appCell_id B p
  map_comp γ δ := (M.appCell_comp B γ δ).symm

/-- The interpretation of the category and functor symbols in the model `K(x, M)` of
Remark 3.17 ([forsman2026syntactic]). -/
def homPreModel : PreModel Sg Cat.{w, v} where
  obj c := Cat.of (x ⟶ M.obj c)
  fn B := (M.homFn x B).toCatHom

/-- `appCell B` of a family of 2-cells conjugated by `eqToHom`s is the conjugate of
`appCell B`. -/
lemma appCell_conj (B : Sg.Fun) {x : Obj} {g₁ g₂ g₁' g₂' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (h : g₁ = g₂) (h' : g₁' = g₂') (δ : ∀ i, g₂ i ⟶ g₂' i) :
    M.appCell B (fun i => eqToHom (congr_fun h i) ≫ δ i ≫ eqToHom (congr_fun h' i).symm) =
      eqToHom (by rw [h]) ≫ M.appCell B δ ≫ eqToHom (by rw [h']) := by
  subst h h'
  simp

/-- The environment in `M` given by an object `ρ` of a product of hom-categories `K(x, M_{cᵢ})`:
its components. -/
def homEnv {n : ℕ} {vty : Fin n → Sg.Cat}
    (P : Product (fun i => (M.homPreModel x).obj (vty i))) (ρ : (P.pt : Type v)) :
    ∀ i, x ⟶ M.obj (vty i) :=
  fun i => (P.π i).toFunctor.obj ρ

/-- The family of 2-cells in `M` given by a morphism `γ : ρ ⟶ ρ'` of a product of
hom-categories: its components. -/
def homEnvMap {n : ℕ} {vty : Fin n → Sg.Cat}
    (P : Product (fun i => (M.homPreModel x).obj (vty i))) {ρ ρ' : (P.pt : Type v)}
    (γ : ρ ⟶ ρ') : ∀ i, M.homEnv x P ρ i ⟶ M.homEnv x P ρ' i :=
  fun i => (P.π i).toFunctor.map γ

/-- At an object, `B(args)` is interpreted in `K(x, M)` as the lift of its arguments followed by
`M(B)`. -/
lemma homPreModel_interp_app_obj {V : Type uᵥ} {vty : V → Sg.Cat} {D : Cat.{w, v}}
    (ρ : ∀ i, D ⟶ (M.homPreModel x).obj (vty i)) (d : (D : Type v)) (B : Sg.Fun)
    (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    ((M.homPreModel x).interp ρ (Trm.app B args)).toFunctor.obj d =
      (M.P B).lift (fun i => ((M.homPreModel x).interp ρ (args i)).toFunctor.obj d) ≫ M.fn B :=
  rfl

/-- On a morphism, `B(args)` is interpreted in `K(x, M)` as `appCell B` of the interpretations of
its arguments. -/
lemma homPreModel_interp_app_map {V : Type uᵥ} {vty : V → Sg.Cat} {D : Cat.{w, v}}
    (ρ : ∀ i, D ⟶ (M.homPreModel x).obj (vty i)) {d d' : (D : Type v)} (γ : d ⟶ d') (B : Sg.Fun)
    (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    ((M.homPreModel x).interp ρ (Trm.app B args)).toFunctor.map γ =
      M.appCell B (fun i => ((M.homPreModel x).interp ρ (args i)).toFunctor.map γ) :=
  rfl

/-- A term is interpreted in `K(x, M)`, at an environment of functors `ρ_i : D ⥤ K(x, M_{c_i})` and
an object `d` of `D`, as it is interpreted in `M` at the environment `ρ_i(d)`. -/
lemma homPreModel_interp_obj_env {V : Type uᵥ} {vty : V → Sg.Cat} {D : Cat.{w, v}}
    (ρ : ∀ i, D ⟶ (M.homPreModel x).obj (vty i)) (d : (D : Type v)) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    ((M.homPreModel x).interp ρ t).toFunctor.obj d =
      M.interp (fun i => (ρ i).toFunctor.obj d) t := by
  induction t with
  | var i => rfl
  | app B args ih =>
      rw [homPreModel_interp_app_obj, funext ih]
      rfl

/-- A term is interpreted in `K(x, M)`, at an environment `ρ`, as it is interpreted in `M`
at `ρ`. -/
lemma homPreModel_interp_obj {n : ℕ} {vty : Fin n → Sg.Cat}
    (P : Product (fun i => (M.homPreModel x).obj (vty i))) (ρ : (P.pt : Type v))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    ((M.homPreModel x).interp P.π t).toFunctor.obj ρ = M.interp (M.homEnv x P ρ) t :=
  M.homPreModel_interp_obj_env x P.π ρ t

/-- On 2-cells, a term is interpreted in `K(x, M)` as `PreModel.interpCell`. -/
lemma homPreModel_interp_map {n : ℕ} {vty : Fin n → Sg.Cat}
    (P : Product (fun i => (M.homPreModel x).obj (vty i))) {ρ ρ' : (P.pt : Type v)} (γ : ρ ⟶ ρ')
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    ((M.homPreModel x).interp P.π t).toFunctor.map γ =
      eqToHom (M.homPreModel_interp_obj x P ρ t) ≫ M.interpCell (M.homEnvMap x P γ) t ≫
        eqToHom (M.homPreModel_interp_obj x P ρ' t).symm := by
  induction t with
  | var i =>
      rw [M.interpCell_var]
      -- The transports at a variable are identities, up to unfolding.
      exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  | app B args ih =>
      rw [homPreModel_interp_app_map, M.appCell_congr B ih]
      refine (M.appCell_conj B (funext fun i => M.homPreModel_interp_obj x P ρ (args i))
        (funext fun i => M.homPreModel_interp_obj x P ρ' (args i)) _).trans ?_
      rw [interpCell_app_appCell]
      rfl

end PreModel

/-- A commutative square conjugated by `eqToHom`s along its four corners commutes. -/
lemma _root_.CategoryTheory.eqToHom_conj_square {C : Type*} [Category C]
    {S S' T T' Sm Sm' Tm Tm' : C}
    (es : S = Sm) (es' : S' = Sm') (et : T = Tm) (et' : T' = Tm') {i : Sm ⟶ Sm'} {j : Tm ⟶ Tm'}
    {r : Sm ⟶ Tm} {r' : Sm' ⟶ Tm'} (h : i ≫ r' = r ≫ j) :
    (eqToHom es ≫ i ≫ eqToHom es'.symm) ≫ (eqToHom es' ≫ r' ≫ eqToHom et'.symm) =
      (eqToHom es ≫ r ≫ eqToHom et.symm) ≫ (eqToHom et ≫ j ≫ eqToHom et'.symm) := by
  subst es es' et et'
  simpa using h

namespace Model

variable (M : Model Sg Obj) (x : Obj)

/-- Naturality of the transformation component `homTr` in `K(x, M)`. -/
lemma homTr_naturality (a : Sg.Tr) {ρ ρ' : ((M.homPreModel x).Pctx a).pt}
    (γ : ρ ⟶ ρ') :
    (((M.homPreModel x).interp ((M.homPreModel x).Pctx a).π (Sg.trsrc a)).toFunctor.map γ) ≫
      (eqToHom (M.homPreModel_interp_obj x ((M.homPreModel x).Pctx a) ρ' (Sg.trsrc a)) ≫
        M.trAt a (M.homEnv x ((M.homPreModel x).Pctx a) ρ') ≫
        eqToHom (M.homPreModel_interp_obj x ((M.homPreModel x).Pctx a) ρ' (Sg.trtgt a)).symm) =
    (eqToHom (M.homPreModel_interp_obj x ((M.homPreModel x).Pctx a) ρ (Sg.trsrc a)) ≫
        M.trAt a (M.homEnv x ((M.homPreModel x).Pctx a) ρ) ≫
        eqToHom (M.homPreModel_interp_obj x ((M.homPreModel x).Pctx a) ρ (Sg.trtgt a)).symm) ≫
      (((M.homPreModel x).interp ((M.homPreModel x).Pctx a).π (Sg.trtgt a)).toFunctor.map γ) := by
  rw [M.homPreModel_interp_map x ((M.homPreModel x).Pctx a) γ (Sg.trsrc a),
    M.homPreModel_interp_map x ((M.homPreModel x).Pctx a) γ (Sg.trtgt a)]
  exact eqToHom_conj_square (M.homPreModel_interp_obj x _ ρ (Sg.trsrc a))
    (M.homPreModel_interp_obj x _ ρ' (Sg.trsrc a))
    (M.homPreModel_interp_obj x _ ρ (Sg.trtgt a))
    (M.homPreModel_interp_obj x _ ρ' (Sg.trtgt a))
    (M.trAt_nat a (M.homEnvMap x ((M.homPreModel x).Pctx a) γ))

/-- The 2-cell of a transformation symbol in `K(x, M)`: at an environment `ρ`, the component
of `M(α)` at `ρ` (`Model.trAt`). -/
def homTr (a : Sg.Tr) :
    (M.homPreModel x).interp ((M.homPreModel x).Pctx a).π (Sg.trsrc a) ⟶
      (M.homPreModel x).interp ((M.homPreModel x).Pctx a).π (Sg.trtgt a) where
  toNatTrans :=
    { app := fun ρ : (((M.homPreModel x).Pctx a).pt : Type v) =>
        eqToHom (M.homPreModel_interp_obj x ((M.homPreModel x).Pctx a) ρ (Sg.trsrc a)) ≫
          M.trAt a (M.homEnv x ((M.homPreModel x).Pctx a) ρ) ≫
          eqToHom (M.homPreModel_interp_obj x ((M.homPreModel x).Pctx a) ρ (Sg.trtgt a)).symm
      naturality := fun _ _ γ => homTr_naturality M x a γ }

/-- **The `Σ`-model `K(x, M)` in `CAT`** of Remark 3.17 ([forsman2026syntactic]): `c ↦ K(x, M_c)`,
`B ↦ ⟨-⟩ ≫ M(B)`, and `α ↦ M(α)` componentwise. -/
def homModel : Model Sg Cat.{w, v} where
  toPreModel := M.homPreModel x
  tr := M.homTr x


/-- In `CAT`, the projection `π_i` of a product sends the image under `lift g` of an object `d` to
`g_i(d)`. -/
lemma _root_.UlmerBialgebras.Product.cat_lift_π_obj {ι : Type*} {c : ι → Cat.{w, v}}
    (P : Product c) {D : Cat.{w, v}} (g : ∀ i, D ⟶ c i) (i : ι) (d : (D : Type v)) :
    (P.π i).toFunctor.obj ((P.lift g).toFunctor.obj d) = (g i).toFunctor.obj d :=
  congrArg (fun F : D ⟶ c i => F.toFunctor.obj d) (P.lift_π g i)

end Model

end UlmerBialgebras
