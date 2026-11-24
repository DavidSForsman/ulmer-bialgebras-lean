module

public import UlmerBialgebras.Syntax.Syntax

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Semantics: Σ-models and the interpretation of terms

This file formalises Definition 3.8 (Σ-models) of *A Syntactic Approach to Ulmer's
Bialgebras*, Section 3.3.

Terms are interpreted in an *environment*: given a Σ-model `M` in a 2-category
with chosen finite products and a family of 1-cells `ρ v : x ⟶ M.obj (vty v)`, a term `t : c` in
the variables `V` is interpreted as a 1-cell `M.interp ρ t : x ⟶ M.obj c`.  Taking for `ρ`
the projections of the product `M_x̄` recovers the term 1-cells `M_x̄(t)` of the paper, and
taking the projections of `M₀` recovers the 1-cells `M(t) : M₀ → M_c`.

## Main results

* `UlmerBialgebras.PreModel`, `UlmerBialgebras.Model`: Σ-models (Definition 3.8).
* `UlmerBialgebras.PreModel.interp`: the interpretation of a term in an environment.
* `UlmerBialgebras.PreModel.interp_subst`: interpretation commutes with substitution.
* `UlmerBialgebras.PreModel.interpCell`: the 2-cell between interpretations induced by a family of
  2-cells between environments.
* `UlmerBialgebras.Model.trAt`: the 2-cell interpreting a transformation symbol at an environment.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 3.8,
  Lemma 3.18
-/

universe u v w uᵥ u𝓌

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]

/-- The part of a Σ-model given by the interpretation of category and functor symbols. -/
structure PreModel (Sg : TwoSig) (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    [HasChosenFinProducts.{u, v, w} Obj] where
  /-- The object interpreting a category symbol. -/
  obj : Sg.Cat → Obj
  /-- The 1-cell interpreting a functor symbol, defined on the product of its arity. -/
  fn : ∀ B : Sg.Fun,
    (HasChosenFinProducts.finProd (fun i => obj (Sg.art B i))).pt ⟶ obj (Sg.fcod B)

namespace PreModel

variable {Sg : TwoSig} (M : PreModel Sg Obj)

/-- The chosen product of the arity of a functor symbol. -/
abbrev P (B : Sg.Fun) : Product (fun i => M.obj (Sg.art B i)) := HasChosenFinProducts.finProd _

/-- The chosen product of the context of a transformation symbol. -/
abbrev Pctx (a : Sg.Tr) : Product (fun i => M.obj (Sg.trt a i)) := HasChosenFinProducts.finProd _

/-- The interpretation of a term in an environment `ρ`. -/
@[implicit_reducible]
def interp {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v)) :
    ∀ {c : Sg.Cat}, Trm Sg.toFunSig vty c → (x ⟶ M.obj c)
  | _, .var v => ρ v
  | _, .app B args => (M.P B).lift (fun i => interp ρ (args i)) ≫ M.fn B
/-- The interpretation of a variable `v` in the environment `ρ` is `ρ v`. -/
@[simp] lemma interp_var {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (vty v)) (v : V) : M.interp ρ (Trm.var v) = ρ v := rfl

/-- The interpretation of `B(args)` is `⟨interp args⟩ ≫ M(B)`. -/
@[simp] lemma interp_app {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (vty v)) (B : Sg.Fun)
    (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    M.interp ρ (Trm.app B args) = (M.P B).lift (fun i => M.interp ρ (args i)) ≫ M.fn B := rfl


/-- Interpretation respects pointwise equal environments. -/
lemma interp_congr {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (h : ∀ v, ρ v = ρ' v) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) : M.interp ρ t = M.interp ρ' t := by
  have : ρ = ρ' := funext h
  subst this; rfl

/-- Interpretation is compatible with precomposition of the environment. -/
lemma interp_comp {V : Type uᵥ} {vty : V → Sg.Cat} {x y : Obj} (h : y ⟶ x)
    (ρ : ∀ v, x ⟶ M.obj (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interp (fun v => h ≫ ρ v) t = h ≫ M.interp ρ t := by
  induction t with
  | var v => rfl
  | app B args ih =>
      simp only [interp_app]
      rw [show (fun i => M.interp (fun v => h ≫ ρ v) (args i)) =
            (fun i => h ≫ M.interp ρ (args i)) from funext ih,
        ← (M.P B).comp_lift, Category.assoc]

/-- The semantic substitution lemma: the first factorization of **Lemma 3.18**
([forsman2026syntactic]). -/
lemma interp_subst {V : Type uᵥ} {W : Type u𝓌} {vty : V → Sg.Cat} {wty : W → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (wty v)) (sub : ∀ v : V, Trm Sg.toFunSig wty (vty v))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interp ρ (t.subst sub) = M.interp (fun v => M.interp ρ (sub v)) t := by
  induction t with
  | var v => rfl
  | app B args ih =>
      change M.interp ρ (Trm.app B fun i => (args i).subst sub) = _
      simp only [interp_app]
      rw [show (fun i => M.interp ρ ((args i).subst sub)) =
            (fun i => M.interp (fun v => M.interp ρ (sub v)) (args i)) from funext ih]

/-- The image under a functor symbol `B` of a family of 2-cells between its arguments. -/
def appCell (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) :
    ((M.P B).lift g ≫ M.fn B) ⟶ ((M.P B).lift g' ≫ M.fn B) :=
  ((M.P B).lift₂ (fun i => eqToHom ((M.P B).lift_π g i) ≫ γ i ≫
    eqToHom ((M.P B).lift_π g' i).symm)) ▷ M.fn B

/-- `appCell B` respects pointwise equal families of 2-cells. -/
lemma appCell_congr (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    {γ δ : ∀ i, g i ⟶ g' i} (h : ∀ i, γ i = δ i) : M.appCell B γ = M.appCell B δ := by
  have : γ = δ := funext h
  rw [this]

/-- `appCell B` sends a family of identity 2-cells to the identity. -/
@[simp] lemma appCell_id (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    M.appCell B (fun i => 𝟙 (g i)) = 𝟙 _ := by
  rw [appCell, show (fun i => eqToHom ((M.P B).lift_π g i) ≫ 𝟙 (g i) ≫
      eqToHom ((M.P B).lift_π g i).symm) = (fun i => 𝟙 ((M.P B).lift g ≫ (M.P B).π i)) from
    funext (fun i => by simp), (M.P B).lift₂_id]
  simp

/-- `appCell B` sends a family of `eqToHom`s to an `eqToHom`. -/
@[simp] lemma appCell_eqToHom (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (h : ∀ i, g i = g' i) :
    M.appCell B (fun i => eqToHom (h i)) = eqToHom (by rw [funext h]) := by
  have hgg : g = g' := funext h
  subst hgg
  simp

/-- `appCell B` preserves vertical composition of families of 2-cells. -/
lemma appCell_comp (B : Sg.Fun) {x : Obj} {g g' g'' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (γ : ∀ i, g i ⟶ g' i) (δ : ∀ i, g' i ⟶ g'' i) :
    M.appCell B γ ≫ M.appCell B δ = M.appCell B (fun i => γ i ≫ δ i) := by
  rw [appCell, appCell, appCell, ← Bicategory.comp_whiskerRight, (M.P B).lift₂_comp]
  congr 1
  refine (M.P B).cell_ext (fun i => ?_)
  rw [(M.P B).lift₂_π, (M.P B).lift₂_π]
  simp

/-- The image under `B` of a family of 2-cells obtained by whiskering a single 2-cell. -/
lemma appCell_whiskerRight (B : Sg.Fun) {y x : Obj} {k k' : y ⟶ x} (Λ : k ⟶ k')
    (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    M.appCell B (fun i => Λ ▷ g i)
      = eqToHom (by rw [(M.P B).comp_lift]) ≫ ((Λ ▷ (M.P B).lift g) ▷ M.fn B) ≫
        eqToHom (by rw [(M.P B).comp_lift]) := by
  have h1 : ∀ i, (Λ ▷ (M.P B).lift g) ▷ (M.P B).π i
      = eqToHom (by rw [Category.assoc, (M.P B).lift_π]) ≫ (Λ ▷ g i) ≫
        eqToHom (by rw [Category.assoc, (M.P B).lift_π]) := by
    intro i
    have e1 := Bicategory.Strict.whiskerRight_comp Λ ((M.P B).lift g) ((M.P B).π i)
    rw [Bicategory.whiskerRight_congr Λ ((M.P B).lift_π g i).symm] at e1
    simpa using eqToHom_conj e1.symm
  have h2 : (M.P B).lift₂ (fun i =>
        eqToHom ((M.P B).lift_π (fun i => k ≫ g i) i) ≫ (Λ ▷ g i) ≫
          eqToHom ((M.P B).lift_π (fun i => k' ≫ g i) i).symm)
      = eqToHom (by rw [(M.P B).comp_lift]) ≫ (Λ ▷ (M.P B).lift g) ≫
        eqToHom (by rw [(M.P B).comp_lift]) := by
    refine (M.P B).cell_ext (fun i => ?_)
    rw [(M.P B).lift₂_π]
    simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
    rw [h1 i]
    simp
  rw [appCell, h2]
  simp

/-- The image under `B` of a family of invertible 2-cells is invertible. -/
instance appCell_isIso (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (γ : ∀ i, g i ⟶ g' i) [∀ i, IsIso (γ i)] : IsIso (M.appCell B γ) := by
  refine ⟨M.appCell B (fun i => inv (γ i)), ?_, ?_⟩
  · rw [M.appCell_comp, M.appCell_congr B (fun i => IsIso.hom_inv_id (γ i)), M.appCell_id]
  · rw [M.appCell_comp, M.appCell_congr B (fun i => IsIso.inv_hom_id (γ i)), M.appCell_id]

/-- Whiskering the image of a family of 2-cells by a 1-cell. -/
lemma whiskerLeft_appCell {y : Obj} (B : Sg.Fun) {x : Obj}
    {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) (h : y ⟶ x) :
    h ◁ (M.appCell B γ) =
      eqToHom (by rw [← Category.assoc, (M.P B).comp_lift]) ≫
        M.appCell B (fun i => h ◁ γ i) ≫ eqToHom (by rw [← Category.assoc, (M.P B).comp_lift]) := by
  have key := Bicategory.Strict.whisker_assoc h ((M.P B).lift₂ (fun i =>
      eqToHom ((M.P B).lift_π g i) ≫ γ i ≫ eqToHom ((M.P B).lift_π g' i).symm)) (M.fn B)
  rw [appCell, key, (M.P B).whiskerLeft_lift₂]
  have : ((M.P B).lift₂ fun i => eqToHom (Category.assoc h ((M.P B).lift g) ((M.P B).π i)) ≫
      (h ◁ (eqToHom ((M.P B).lift_π g i) ≫ γ i ≫ eqToHom ((M.P B).lift_π g' i).symm)) ≫
      eqToHom (Category.assoc h ((M.P B).lift g') ((M.P B).π i)).symm) =
      eqToHom (by rw [(M.P B).comp_lift]) ≫ ((M.P B).lift₂ (fun i =>
        eqToHom ((M.P B).lift_π (fun i => h ≫ g i) i) ≫ (h ◁ γ i) ≫
        eqToHom ((M.P B).lift_π (fun i => h ≫ g' i) i).symm)) ≫
      eqToHom (by rw [(M.P B).comp_lift]) := by
    refine (M.P B).cell_ext (fun i => ?_)
    rw [(M.P B).lift₂_π]
    simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
      (M.P B).lift₂_π]
    simp
  rw [this, appCell]
  simp

/-- Any environment factors through the corresponding product. -/
lemma interp_lift {V : Type uᵥ} {vty : V → Sg.Cat} (P : Product (fun v => M.obj (vty v)))
    {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interp ρ t = P.lift ρ ≫ M.interp P.π t := by
  rw [← M.interp_comp]
  exact M.interp_congr (fun v => (P.lift_π ρ v).symm) t

/-- The interpretation of a term is functorial in the environment: this is the 2-cell
`M_x̄(t)(γ₁, …, γₙ)` of the paper. -/
def interpCell {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)}
    (γ : ∀ v, ρ v ⟶ ρ' v) : ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c),
      M.interp ρ t ⟶ M.interp ρ' t
  | _, .var v => γ v
  | _, .app B args =>
      ((M.P B).lift₂ (fun i =>
        eqToHom ((M.P B).lift_π (fun i => M.interp ρ (args i)) i) ≫ interpCell γ (args i) ≫
          eqToHom ((M.P B).lift_π (fun i => M.interp ρ' (args i)) i).symm)) ▷ M.fn B

/-- On a variable `v`, `interpCell γ` is the 2-cell `γ v`. -/
@[simp] lemma interpCell_var {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (γ : ∀ v, ρ v ⟶ ρ' v) (v : V) :
    M.interpCell γ (Trm.var v) = γ v := by simp [PreModel.interpCell]

/-- On `B(args)`, `interpCell γ` is the `lift₂` of the 2-cells `M.interpCell γ (args i)`
(up to `eqToHom`), whiskered by `M.fn B`. -/
lemma interpCell_app {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (γ : ∀ v, ρ v ⟶ ρ' v) (B : Sg.Fun)
    (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    M.interpCell γ (Trm.app B args) =
      ((M.P B).lift₂ (fun i =>
        eqToHom ((M.P B).lift_π (fun i => M.interp ρ (args i)) i) ≫ M.interpCell γ (args i) ≫
          eqToHom ((M.P B).lift_π (fun i => M.interp ρ' (args i)) i).symm)) ▷ M.fn B := by
  simp [PreModel.interpCell]

/-- `M(B(args))(γ)` is `appCell B` of the 2-cells `M(args i)(γ)`. -/
lemma interpCell_app_appCell {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (γ : ∀ v, ρ v ⟶ ρ' v) (B : Sg.Fun)
    (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    M.interpCell γ (Trm.app B args) = M.appCell B (fun i => M.interpCell γ (args i)) := rfl

/-- `interpCell` sends the family of identity 2-cells to the identity on `M.interp ρ t`. -/
@[simp] lemma interpCell_id {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interpCell (fun v => 𝟙 (ρ v)) t = 𝟙 (M.interp ρ t) := by
  induction t with
  | var v => simp
  | app B args ih =>
      rw [M.interpCell_app]
      have h : (M.P B).lift₂ (fun i =>
          eqToHom ((M.P B).lift_π (fun i => M.interp ρ (args i)) i) ≫
            M.interpCell (fun v => 𝟙 (ρ v)) (args i) ≫
            eqToHom ((M.P B).lift_π (fun i => M.interp ρ (args i)) i).symm) = 𝟙 _ := by
        refine (M.P B).cell_ext (fun i => ?_)
        rw [(M.P B).lift₂_π]
        simp [ih i]
      rw [h]
      simp

/-- `interpCell` respects pointwise equal families of 2-cells. -/
lemma interpCell_congr {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} {γ δ : ∀ v, ρ v ⟶ ρ' v} (h : ∀ v, γ v = δ v)
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) : M.interpCell γ t = M.interpCell δ t := by
  rw [funext h]

/-- `interpCell` sends a family of `eqToHom`s to an `eqToHom`. -/
@[simp] lemma interpCell_eqToHom {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (e : ∀ v, ρ v = ρ' v) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    M.interpCell (fun v => eqToHom (e v)) t = eqToHom (by rw [funext e]) := by
  have hρ : ρ = ρ' := funext e
  subst hρ
  simp

/-- `interpCell` preserves vertical composition: `M(t)(γ) ≫ M(t)(δ) = M(t)(γ ≫ δ)`. -/
lemma interpCell_comp {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    {ρ ρ' ρ'' : ∀ v, x ⟶ M.obj (vty v)} (γ : ∀ v, ρ v ⟶ ρ' v) (δ : ∀ v, ρ' v ⟶ ρ'' v)
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    M.interpCell γ t ≫ M.interpCell δ t = M.interpCell (fun v => γ v ≫ δ v) t := by
  induction t with
  | var v => simp
  | app B args ih =>
      simp only [interpCell_app_appCell, M.appCell_comp]
      exact M.appCell_congr B (fun i => ih i)

/-- The 2-cell `M_x̄(t)(γ)` is the whiskering of the 2-cell induced on the context product. -/
lemma interpCell_whisker {V : Type uᵥ} {vty : V → Sg.Cat} (P : Product (fun v => M.obj (vty v)))
    {x : Obj} {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (γ : ∀ v, ρ v ⟶ ρ' v) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    M.interpCell γ t = eqToHom (M.interp_lift P ρ t) ≫
      ((P.lift₂ (fun v => eqToHom (P.lift_π ρ v) ≫ γ v ≫ eqToHom (P.lift_π ρ' v).symm)) ▷
        M.interp P.π t) ≫ eqToHom (M.interp_lift P ρ' t).symm := by
  induction t with
  | var v => simp [P.lift₂_π]
  | app B args ih =>
      rw [M.interpCell_app_appCell, M.appCell_congr B ih, ← M.appCell_comp, ← M.appCell_comp,
        M.appCell_whiskerRight B _ (fun i => M.interp P.π (args i))]
      simp only [interp_app, Bicategory.Strict.whiskerRight_comp]
      simp

end PreModel

/-- A Σ-model in a 2-category with chosen finite products (**Definition 3.8**,
[forsman2026syntactic]; the paper works in a PIE-complete 2-category, but a model only uses the
finite products of its arities and contexts). The 2-cell interpreting a transformation symbol is
taken at the generic environment, i.e. at the projections of the product `M_x̄` over the context
`x̄` of the symbol. -/
structure Model (Sg : TwoSig) (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    [HasChosenFinProducts.{u, v, w} Obj] extends PreModel Sg Obj where
  /-- The 2-cell interpreting a transformation symbol. -/
  tr : ∀ a : Sg.Tr,
    toPreModel.interp (toPreModel.Pctx a).π (Sg.trsrc a) ⟶
      toPreModel.interp (toPreModel.Pctx a).π (Sg.trtgt a)

namespace Model

variable {Sg : TwoSig} (M : Model Sg Obj)

/-- The lift of an environment into the context product is compatible with the
interpretation. -/
lemma interp_lift_ctx (a : Sg.Tr) {x : Obj} (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i))
    {c : Sg.Cat} (t : Trm Sg.toFunSig (Sg.trt a) c) :
    M.interp ρ t = (M.Pctx a).lift ρ ≫ M.interp (M.Pctx a).π t :=
  M.toPreModel.interp_lift (M.Pctx a) ρ t

/-- The 2-cell interpreting a transformation symbol, at an arbitrary environment. -/
def trAt (a : Sg.Tr) {x : Obj} (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) :
    M.interp ρ (Sg.trsrc a) ⟶ M.interp ρ (Sg.trtgt a) :=
  eqToHom (M.interp_lift_ctx a ρ (Sg.trsrc a)) ≫ ((M.Pctx a).lift ρ ◁ M.tr a) ≫
    eqToHom (M.interp_lift_ctx a ρ (Sg.trtgt a)).symm

/-- Transporting `trAt` along an equality of environments. -/
lemma trAt_congr (a : Sg.Tr) {x : Obj} {ρ ρ' : ∀ i, x ⟶ M.obj (Sg.trt a i)}
    (e : ∀ i, ρ i = ρ' i) :
    M.trAt a ρ' = eqToHom (by rw [funext e]) ≫ M.trAt a ρ ≫ eqToHom (by rw [funext e]) := by
  have hρ : ρ = ρ' := funext e
  subst hρ
  simp

/-- `trAt` is compatible with precomposition of the environment. -/
lemma trAt_precomp (a : Sg.Tr) {x y : Obj} (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) (h : y ⟶ x) :
    h ◁ M.trAt a ρ = eqToHom (by rw [← M.toPreModel.interp_comp]) ≫
      M.trAt a (fun i => h ≫ ρ i) ≫ eqToHom (by rw [← M.toPreModel.interp_comp]) := by
  rw [trAt, trAt]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
  rw [Bicategory.Strict.comp_whiskerLeft' h ((M.Pctx a).lift ρ) (M.tr a),
    Bicategory.whiskerLeft_congr ((M.Pctx a).comp_lift h ρ).symm (M.tr a)]
  simp

/-- Naturality of the interpretation of a transformation symbol in the environment. -/
lemma trAt_nat (a : Sg.Tr) {x : Obj} {ρ ρ' : ∀ i, x ⟶ M.obj (Sg.trt a i)}
    (γ : ∀ i, ρ i ⟶ ρ' i) :
    M.interpCell γ (Sg.trsrc a) ≫ M.trAt a ρ' = M.trAt a ρ ≫ M.interpCell γ (Sg.trtgt a) := by
  have ex := Eq.symm <| Bicategory.whisker_exchange ((M.Pctx a).lift₂ (fun i =>
    eqToHom ((M.Pctx a).lift_π ρ i) ≫ γ i ≫ eqToHom ((M.Pctx a).lift_π ρ' i).symm)) (M.tr a)
  rw [M.toPreModel.interpCell_whisker (M.Pctx a) γ (Sg.trsrc a),
    M.toPreModel.interpCell_whisker (M.Pctx a) γ (Sg.trtgt a), trAt, trAt]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% ex]

end Model

end UlmerBialgebras
