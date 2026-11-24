module

public import UlmerBialgebras.Paper.Sec3DefsTwoFun
public import UlmerBialgebras.Basic.ConjEq

/-!
# Natural transformations between strict 2-functors as morphisms of models

Helper lemmas for Example 3.12 (`UlmerBialgebras/Proofs/Sec3/Sec3Ex.lean`): the
transformation-symbol laws
`LaxData.TrLaw` / `OplaxData.TrLaw`, computations in the model `M_F` of a strict 2-functor, and the
naturality 2-cells `natOf L f`. The calculus of `ConjEq` is in `UlmerBialgebras/Basic/ConjEq.lean`.

## Main results

* `UlmerBialgebras.Paper.TwoFun.laxEquiv`, `UlmerBialgebras.Paper.TwoFun.oplaxEquiv` (Example 3.12):
  lax (oplax) transformations `F ⇒ G` are equivalent to lax (oplax) morphisms `M_F → M_G`, and
  `laxModifEquiv`, `oplaxModifEquiv` do the same for modifications and 2-cells.
* `UlmerBialgebras.Paper.TwoFun.laxIsPseudo_iff`, `laxIsStrict_iff`: a lax transformation is pseudo
  iff its lax morphism is strong, and strict iff its structure 2-cells are identities (`eqToHom`s).

The oplax morphisms are in `UlmerBialgebras/Proofs/Sec3/TwoFunctorOplaxModel.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.9 and
  3.12
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras

open CategoryTheory
open scoped CategoryTheory.Bicategory

section Laws
variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

/-- At the generic environment, `trAt` is the interpreting 2-cell itself. -/
lemma Model.trAt_π (M : Model Sg Obj) (a : Sg.Tr) : M.trAt a (M.Pctx a).π = M.tr a := by
  have hl : (M.Pctx a).lift (M.Pctx a).π = 𝟙 _ := by
    simpa using (M.Pctx a).lift_uniq (𝟙 _)
  rw [Model.trAt, Bicategory.whiskerLeft_congr' hl, Bicategory.Strict.id_whiskerLeft]
  simp

/-- Extensionality for lax morphisms of models: equal 1-cells and heterogeneously equal structure
2-cells. -/
lemma LaxMor.ext' {M N : Model Sg Obj} {L L' : LaxMor M N} (hc : L.cell = L'.cell)
    (hs : ∀ B, HEq (L.str B) (L'.str B)) : L = L' := by
  obtain ⟨⟨c, s⟩, t⟩ := L
  obtain ⟨⟨c', s'⟩, t'⟩ := L'
  dsimp only at hc hs
  subst hc
  have : s = s' := funext fun B => eq_of_heq (hs B)
  subst this
  rfl

/-- Extensionality for oplax morphisms of models: equal 1-cells and heterogeneously equal structure
2-cells. -/
lemma OplaxMor.ext' {M N : Model Sg Obj} {L L' : OplaxMor M N} (hc : L.cell = L'.cell)
    (hs : ∀ B, HEq (L.str B) (L'.str B)) : L = L' := by
  obtain ⟨⟨c, s⟩, t⟩ := L
  obtain ⟨⟨c', s'⟩, t'⟩ := L'
  dsimp only at hc hs
  subst hc
  have : s = s' := funext fun B => eq_of_heq (hs B)
  subst this
  rfl

namespace LaxData

variable {M N : Model Sg Obj}

/-- The compatibility of lax data with a transformation symbol, at an environment `ρ`. -/
def TrLaw (L : LaxData M.toPreModel N.toPreModel) (a : Sg.Tr) {x : Obj}
    (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) : Prop :=
  N.trAt a (fun i => ρ i ≫ L.cell (Sg.trt a i)) ≫ L.eta ρ (Sg.trtgt a)
    = L.eta ρ (Sg.trsrc a) ≫ (M.trAt a ρ ▷ L.cell (Sg.trty a))

/-- The transformation-symbol law of lax data transports along pointwise equal environments. -/
lemma TrLaw.congr {L : LaxData M.toPreModel N.toPreModel} {a : Sg.Tr} {x : Obj}
    {ρ ρ' : ∀ i, x ⟶ M.obj (Sg.trt a i)} (e : ∀ i, ρ i = ρ' i) (H : L.TrLaw a ρ) :
    L.TrLaw a ρ' := by
  have : ρ = ρ' := funext e
  subst this; exact H

/-- The transformation-symbol law is stable under precomposition of the environment. -/
lemma TrLaw.precomp {L : LaxData M.toPreModel N.toPreModel} {a : Sg.Tr} {x y : Obj}
    {ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)} (H : L.TrLaw a ρ) (h : y ⟶ x) :
    L.TrLaw a (fun i => h ≫ ρ i) := by
  have e1 := N.trAt_precomp a (fun i => ρ i ≫ L.cell (Sg.trt a i)) h
  rw [N.trAt_congr a (ρ := fun i => (h ≫ ρ i) ≫ L.cell (Sg.trt a i))
    (fun i => Category.assoc _ _ _)] at e1
  have e2 := fun {c : Sg.Cat} (t : Trm Sg.toFunSig (Sg.trt a) c) =>
    eqToHom_conj (L.eta_precomp ρ h t).symm
  have e3 := M.trAt_precomp a ρ h
  unfold TrLaw at H ⊢
  have key := congr(h ◁ $H)
  simp only [Bicategory.whiskerLeft_comp] at key
  rw [e1, e2, e2, Bicategory.Strict.whisker_assoc, e3] at key
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
    eqToHom_trans,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  simp only [← Category.assoc] at key
  rw [cancel_mono] at key
  exact key

/-- `tr_compat` of a lax morphism is the transformation-symbol law at the generic
environment. -/
lemma tr_compat_iff (L : LaxData M.toPreModel N.toPreModel) (a : Sg.Tr) :
    L.TrLaw a (M.Pctx a).π ↔
      (N.trAt a (fun i => (M.Pctx a).π i ≫ L.cell (Sg.trt a i))) ≫
          L.eta (M.Pctx a).π (Sg.trtgt a)
        = L.eta (M.Pctx a).π (Sg.trsrc a) ≫ (M.tr a ▷ L.cell (Sg.trty a)) := by
  unfold TrLaw
  rw [Model.trAt_π]

/-- A lax morphism of models satisfies the transformation-symbol law at the generic environment. -/
lemma _root_.UlmerBialgebras.LaxMor.trLaw {M N : Model Sg Obj} (F : LaxMor M N) (a : Sg.Tr) :
    F.toLaxData.TrLaw a (M.Pctx a).π :=
  (tr_compat_iff F.toLaxData a).mpr (F.tr_compat a)

end LaxData

namespace OplaxData

variable {M N : Model Sg Obj}

/-- The compatibility of oplax data with a transformation symbol, at an environment `ρ`. -/
def TrLaw (L : OplaxData M.toPreModel N.toPreModel) (a : Sg.Tr) {x : Obj}
    (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) : Prop :=
  (M.trAt a ρ ▷ L.cell (Sg.trty a)) ≫ L.eta ρ (Sg.trtgt a)
    = L.eta ρ (Sg.trsrc a) ≫ N.trAt a (fun i => ρ i ≫ L.cell (Sg.trt a i))

/-- The transformation-symbol law of oplax data transports along pointwise equal environments. -/
lemma TrLaw.congr {L : OplaxData M.toPreModel N.toPreModel} {a : Sg.Tr} {x : Obj}
    {ρ ρ' : ∀ i, x ⟶ M.obj (Sg.trt a i)} (e : ∀ i, ρ i = ρ' i) (H : L.TrLaw a ρ) :
    L.TrLaw a ρ' := by
  have : ρ = ρ' := funext e
  subst this; exact H

/-- The transformation-symbol law is stable under precomposition of the environment. -/
lemma TrLaw.precomp {L : OplaxData M.toPreModel N.toPreModel} {a : Sg.Tr} {x y : Obj}
    {ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)} (H : L.TrLaw a ρ) (h : y ⟶ x) :
    L.TrLaw a (fun i => h ≫ ρ i) := by
  have e1 := N.trAt_precomp a (fun i => ρ i ≫ L.cell (Sg.trt a i)) h
  rw [N.trAt_congr a (ρ := fun i => (h ≫ ρ i) ≫ L.cell (Sg.trt a i))
    (fun i => Category.assoc _ _ _)] at e1
  have e2 := fun {c : Sg.Cat} (t : Trm Sg.toFunSig (Sg.trt a) c) =>
    eqToHom_conj (L.eta_precomp ρ h t).symm
  have e3 := M.trAt_precomp a ρ h
  unfold TrLaw at H ⊢
  have key := congr(h ◁ $H)
  simp only [Bicategory.whiskerLeft_comp] at key
  rw [e1, e2, e2, Bicategory.Strict.whisker_assoc, e3] at key
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
    eqToHom_trans,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [cancel_epi] at key
  simp only [← Category.assoc] at key
  rw [cancel_mono] at key
  exact key

/-- `tr_compat` of an oplax morphism is the transformation-symbol law at the generic
environment. -/
lemma tr_compat_iff (L : OplaxData M.toPreModel N.toPreModel) (a : Sg.Tr) :
    L.TrLaw a (M.Pctx a).π ↔
      (M.tr a ▷ L.cell (Sg.trty a)) ≫ L.eta (M.Pctx a).π (Sg.trtgt a)
        = L.eta (M.Pctx a).π (Sg.trsrc a) ≫
          (N.trAt a (fun i => (M.Pctx a).π i ≫ L.cell (Sg.trt a i))) := by
  unfold TrLaw
  rw [Model.trAt_π]

/-- An oplax morphism of models satisfies the transformation-symbol law at the generic environment.
-/
lemma _root_.UlmerBialgebras.OplaxMor.trLaw {M N : Model Sg Obj} (F : OplaxMor M N) (a : Sg.Tr) :
    F.toOplaxData.TrLaw a (M.Pctx a).π :=
  (tr_compat_iff F.toOplaxData a).mpr (F.tr_compat a)

end OplaxData

end Laws

namespace Paper.TwoFun

open CategoryTheory

variable {A : Type ua} [Bicategory.{wa, va} A] [Bicategory.Strict A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K]

/-! ### Computations in the model `M_F` -/

namespace StrictTwoFunctor

variable (F : StrictTwoFunctor K A)

/-- In the model `M_F`, the function symbol of `f : a ⟶ b` is the unary projection followed by
`F f`. -/
lemma model_fn {a b : A} (f : a ⟶ b) :
    F.model.fn ⟨a, b, f⟩ = (F.model.P ⟨a, b, f⟩).π 0 ≫ F.map f := rfl

/-- In the model `M_F` of a strict 2-functor, the term `f(t)` is interpreted as `M_F(t) ≫ F f`. -/
lemma interp_app1 {V : Type} {vty : V → A} {x : K} (ρ : ∀ v, x ⟶ F.model.obj (vty v))
    {a b : A} (f : a ⟶ b) (t : Trm (funSigOf A) vty a) :
    F.model.interp ρ (app1 A f t) = F.model.interp ρ t ≫ F.map f := by
  rw [app1, PreModel.interp_app, model_fn, ← Category.assoc, Product.lift_π]

/-- The identity environment of the context of a transformation symbol. -/
def idEnv (τ : SigTr A) :
    ∀ i : Fin ((sigOf A).trn τ), F.obj τ.src ⟶ F.model.obj ((sigOf A).trt τ i) :=
  fun _ => 𝟙 (F.obj τ.src)

/-- In `M_F`, the 2-cell `appCell` of the function symbol `f` applied to `γ` is `ConjEq` to
`γ 0 ▷ F f`. -/
lemma appCell_eq {x : K} {a b : A} (f : a ⟶ b) {g g' : ∀ _ : Fin 1, x ⟶ F.obj a}
    (γ : ∀ i, g i ⟶ g' i) : ConjEq (F.model.appCell ⟨a, b, f⟩ γ) (γ 0 ▷ F.map f) := by
  refine (ConjEq.whiskerRight_comp₁ _ _ _).trans (ConjEq.whiskerRight ?_ (F.map f))
  rw [Product.lift₂_π]
  exact ConjEq.conj _ _ _

/-- In `M_F`, the transformation symbol of a 2-cell `η : f ⟶ g` at an environment `ρ` with `ρ 0 = k`
is `ConjEq` to `k ◁ F η`. -/
lemma trAt_cell {x : K} {a b : A} {f g : a ⟶ b} (η : f ⟶ g)
    (ρ : ∀ i, x ⟶ F.model.obj ((sigOf A).trt (SigTr.cell η) i)) (k : x ⟶ F.obj a)
    (hk : ρ 0 = k) : ConjEq (F.model.trAt (SigTr.cell η) ρ) (k ◁ F.map₂ η) := by
  subst hk
  have hr : F.model.tr (SigTr.cell η) =
      (F.model.P ⟨a, b, f⟩).lift (fun _ => (F.model.Pctx (SigTr.cell η)).π 0) ◁
        ((F.model.P ⟨a, b, f⟩).π 0 ◁ F.map₂ η) := rfl
  have hk : ((F.model.Pctx (SigTr.cell η)).lift ρ ≫
      (F.model.P ⟨a, b, f⟩).lift (fun _ => (F.model.Pctx (SigTr.cell η)).π 0)) ≫
        (F.model.P ⟨a, b, f⟩).π 0 = ρ 0 := by
    rw [Category.assoc, Product.lift_π, Product.lift_π]
  unfold Model.trAt
  rw [hr]
  exact (ConjEq.conj _ _ _).trans
    ((ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans
      ((ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans (ConjEq.whiskerLeft_congr' hk _)))

/-- In `M_F`, the transformation symbol of a composite `f ≫ g` (comparing `g(f(x))` and
`(f ≫ g)(x)`) is an `eqToHom` at every environment (`F` is strict). -/
lemma trAt_comp {x : K} {a b c : A} (f : a ⟶ b) (g : b ⟶ c)
    (ρ : ∀ i, x ⟶ F.model.obj ((sigOf A).trt (SigTr.comp f g) i)) :
    ∃ h, F.model.trAt (SigTr.comp f g) ρ = eqToHom h := by
  unfold Model.trAt
  dsimp only [StrictTwoFunctor.model, StrictTwoFunctor.trCell]
  rw [Bicategory.whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans]
  exact ⟨_, rfl⟩

/-- In `M_F`, the transformation symbol of an identity `𝟙 a` (comparing `x` and `id(x)`) is an
`eqToHom` at every environment (`F` is strict). -/
lemma trAt_unit {x : K} (a : A)
    (ρ : ∀ i, x ⟶ F.model.obj ((sigOf A).trt (SigTr.unit a) i)) :
    ∃ h, F.model.trAt (SigTr.unit a) ρ = eqToHom h := by
  unfold Model.trAt
  dsimp only [StrictTwoFunctor.model, StrictTwoFunctor.trCell]
  rw [Bicategory.whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans]
  exact ⟨_, rfl⟩

/-- For components `app c : H c ⟶ H' c`, the induced 2-cell on the unary product, whiskered by
`M_G(f)`, is `ConjEq` to `π₀ ◁ (app a ▷ G f)`. -/
lemma prodApp_whisker (G : StrictTwoFunctor K A)
    {Hc H'c : ∀ c : A, F.model.obj c ⟶ G.model.obj c} (app : ∀ c, Hc c ⟶ H'c c)
    {a b : A} (f : a ⟶ b) :
    ConjEq (prodApp (M := F.model.toPreModel) (N := G.model.toPreModel) app ⟨a, b, f⟩ ▷
        G.model.fn ⟨a, b, f⟩)
      ((F.model.P ⟨a, b, f⟩).π 0 ◁ (app a ▷ G.map f)) := by
  refine (ConjEq.whiskerRight_comp₁ _ _ _).trans
    ((ConjEq.whiskerRight ?_ (G.map f)).trans (ConjEq.whiskerLeft_whiskerRight _ _ _).symm)
  rw [prodApp_π]
  exact ConjEq.conj _ _ _

/-- In `M_F`, `M_F(f) ◁ β` is `ConjEq` to `π₀ ◁ (F f ◁ β)`. -/
lemma fn_whiskerLeft {a b : A} (f : a ⟶ b) {y : K} {u u' : F.obj b ⟶ y} (β : u ⟶ u') :
    ConjEq (F.model.fn ⟨a, b, f⟩ ◁ β) ((F.model.P ⟨a, b, f⟩).π 0 ◁ (F.map f ◁ β)) :=
  ConjEq.whiskerLeft_comp₁ _ _ _

end StrictTwoFunctor

open StrictTwoFunctor

variable (F G : StrictTwoFunctor K A)

/-- A section of the projection out of a unary product. -/
lemma lift_id_π {a b : A} (f : a ⟶ b) :
    (F.model.P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ≫ (F.model.P ⟨a, b, f⟩).π 0 =
      𝟙 (F.obj a) :=
  Product.lift_π _ _ 0

/-! ### Lax morphisms `M_F → M_G` -/

section Lax

/-- The naturality 2-cell of lax data `L : M_F → M_G` at a 1-cell `f`, read off at the
identity environment. -/
def natOf (L : LaxData F.model.toPreModel G.model.toPreModel) {a b : A} (f : a ⟶ b) :
    L.cell a ≫ G.map f ⟶ F.map f ≫ L.cell b :=
  eqToHom (by
      rw [model_fn, ← Category.assoc, Product.lift_π, Category.id_comp]) ≫
    L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) ≫
    eqToHom (by
      rw [model_fn, ← Category.assoc, Product.lift_π, Category.id_comp])

/-- `natOf F G L f` is `ConjEq` to the structure 2-cell `L.str f` whiskered by the section
`lift (id)` of the unary product. -/
lemma natOf_conj (L : LaxData F.model.toPreModel G.model.toPreModel) {a b : A} (f : a ⟶ b) :
    ConjEq (natOf F G L f)
      ((F.model.P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ◁ L.str ⟨a, b, f⟩) :=
  (ConjEq.conj _ _ (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)))).trans (ConjEq.conj _ _ _)

/-- The structure 2-cell of lax data `L` at the symbol `f` and an environment `g` with `g 0 = k` is
`ConjEq` to `k ◁ natOf F G L f`. -/
lemma strAt_eq (L : LaxData F.model.toPreModel G.model.toPreModel) {x : K} {a b : A}
    (f : a ⟶ b) (g : ∀ _ : Fin 1, x ⟶ F.obj a) (k : x ⟶ F.obj a) (hk : g 0 = k) :
    ConjEq (L.strAt ⟨a, b, f⟩ g) (k ◁ natOf F G L f) := by
  subst hk
  have pre := L.strAt_precomp ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) (g 0)
  have cg := L.strAt_congr ⟨a, b, f⟩ (g := fun _ => g 0 ≫ 𝟙 (F.obj a)) (g' := g)
    (fun i => by simp only [Category.comp_id]; exact congr(g $((Fin.fin_one_eq_zero i).symm)))
  have hn : ConjEq (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a))) (natOf F G L f) :=
    (ConjEq.conj _ _ _).symm
  exact (ConjEq.intro cg).trans ((ConjEq.intro pre).symm.trans (ConjEq.whiskerLeft (g 0) hn))

/-- The comparison 2-cell `eta` of lax data `L` on the unary term `f(x)` at the identity environment
is `ConjEq` to `natOf F G L f`. -/
lemma laxEta_app1 (L : LaxData F.model.toPreModel G.model.toPreModel) {a b : A}
    (f : a ⟶ b) :
    ConjEq (L.eta (fun _ : Fin 1 => 𝟙 (F.obj a))
        (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => a) (0 : Fin 1))))
      (natOf F G L f) := by
  rw [LaxData.eta_app]
  simp only [LaxData.eta_var, PreModel.appCell_id, Category.id_comp, PreModel.interp_var]
  exact (strAt_eq F G L f (fun _ => 𝟙 (F.obj a)) (𝟙 _) rfl).trans
    (ConjEq.id_whiskerLeft _)

/-- The comparison 2-cell `eta` of lax data `L` on the term `g(f(x))` at the identity environment is
`ConjEq` to the pasting `(natOf f ▷ G g) ≫ (F f ◁ natOf g)`. -/
lemma laxEta_app1_app1 (L : LaxData F.model.toPreModel G.model.toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    ConjEq (L.eta (fun _ : Fin 1 => 𝟙 (F.obj a))
        (app1 A g (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => a) (0 : Fin 1)))))
      ((natOf F G L f ▷ G.map g) ≫ eqToHom (Category.assoc _ _ _) ≫ (F.map f ◁ natOf F G L g)) := by
  rw [LaxData.eta_app]
  refine ConjEq.comp ((G.appCell_eq g _).trans ((laxEta_app1 F G L f).whiskerRight (G.map g))) ?_
  exact (strAt_eq F G L g _ (F.map f) (by rw [F.interp_app1]; simp)).trans
    (ConjEq.eqToHom_comp (ConjEq.of_eq rfl) _).symm

/-- The transformation-symbol law of lax data `L` for a 2-cell `η : f ⟶ g` (at the identity
environment) is the naturality of `natOf` in `η`, the 2-cell axiom of a lax transformation. -/
lemma laxTrLaw_cell_iff (L : LaxData F.model.toPreModel G.model.toPreModel) {a b : A}
    {f g : a ⟶ b} (η : f ⟶ g) :
    L.TrLaw (SigTr.cell η) (F.idEnv (SigTr.cell η)) ↔
      (L.cell a ◁ G.map₂ η) ≫ natOf F G L g = natOf F G L f ≫ (F.map₂ η ▷ L.cell b) :=
  ConjEq.eq_iff
    ((G.trAt_cell η
      (fun i => F.idEnv (SigTr.cell η) i ≫ L.cell ((sigOf A).trt (SigTr.cell η) i))
      (L.cell a) (Category.id_comp _)).comp (laxEta_app1 F G L g))
    ((laxEta_app1 F G L f).comp
      (((F.trAt_cell η (F.idEnv (SigTr.cell η)) (𝟙 (F.obj a)) rfl).trans
        (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell b)))

/-- The transformation-symbol law of lax data `L` for a composite `f ≫ g` (at the identity
environment) is the composition axiom of a lax transformation for `natOf`. -/
lemma laxTrLaw_comp_iff (L : LaxData F.model.toPreModel G.model.toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    L.TrLaw (SigTr.comp f g) (F.idEnv (SigTr.comp f g)) ↔
      natOf F G L (f ≫ g) = eqToHom (by rw [G.map_comp, Category.assoc]) ≫
        (natOf F G L f ▷ G.map g) ≫ eqToHom (Category.assoc _ _ _) ≫ (F.map f ◁ natOf F G L g) ≫
        eqToHom (by rw [F.map_comp, Category.assoc]) := by
  obtain ⟨r₁, hr₁⟩ := G.trAt_comp f g
    (fun i => F.idEnv (SigTr.comp f g) i ≫ L.cell ((sigOf A).trt (SigTr.comp f g) i))
  obtain ⟨r₂, hr₂⟩ := F.trAt_comp f g (F.idEnv (SigTr.comp f g))
  unfold LaxData.TrLaw
  rw [hr₁, hr₂]
  simp only [Bicategory.eqToHom_whiskerRight]
  refine (ConjEq.eq_iff_conj ((laxEta_app1_app1 F G L f g).eqToHom_comp _)
    ((laxEta_app1 F G L (f ≫ g)).comp_eqToHom _) (by rw [G.map_comp, Category.assoc])
    (by rw [F.map_comp, Category.assoc])).trans ?_
  simp only [Category.assoc, iff_self]

/-- The transformation-symbol law of lax data `L` for an identity `𝟙 a` (at the identity
environment) is the unit axiom of a lax transformation: `natOf (𝟙 a)` is an `eqToHom`. -/
lemma laxTrLaw_unit_iff (L : LaxData F.model.toPreModel G.model.toPreModel) (a : A) :
    L.TrLaw (SigTr.unit a) (F.idEnv (SigTr.unit a)) ↔
      natOf F G L (𝟙 a) = eqToHom (by simp only [G.map_id, F.map_id, Category.comp_id,
        Category.id_comp]) := by
  have h₁ : L.eta (F.idEnv (SigTr.unit a)) ((sigOf A).trtgt (SigTr.unit a)) = 𝟙 _ :=
    L.eta_var _ 0
  obtain ⟨r₁, hr₁⟩ := G.trAt_unit a
    (fun i => F.idEnv (SigTr.unit a) i ≫ L.cell ((sigOf A).trt (SigTr.unit a) i))
  obtain ⟨r₂, hr₂⟩ := F.trAt_unit a (F.idEnv (SigTr.unit a))
  unfold LaxData.TrLaw
  rw [h₁, hr₁, hr₂]
  simp only [Bicategory.eqToHom_whiskerRight]
  refine (iff_of_eq congr($(Category.comp_id _) = _)).trans ?_
  exact ConjEq.eqToHom_eq_iff ((laxEta_app1 F G L (𝟙 a)).comp_eqToHom _) _ _

/-- For lax data, the transformation-symbol law at the identity environment implies it at the
generic environment. -/
lemma laxTrLaw_generic_of_id (L : LaxData F.model.toPreModel G.model.toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ (F.idEnv τ)) : L.TrLaw τ (F.model.Pctx τ).π :=
  (H.precomp ((F.model.Pctx τ).π 0)).congr
    (fun i => by rw [Fin.fin_one_eq_zero i]; exact Category.comp_id _)

/-- For lax data, the transformation-symbol law at the generic environment implies it at the
identity environment. -/
lemma laxTrLaw_id_of_generic (L : LaxData F.model.toPreModel G.model.toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ (F.model.Pctx τ).π) : L.TrLaw τ (F.idEnv τ) :=
  (H.precomp ((F.model.Pctx τ).lift (F.idEnv τ))).congr (fun i => Product.lift_π _ _ i)

variable {F G}

/-- The lax data of a lax natural transformation. -/
abbrev LaxNat.toLaxData (σ : LaxNat F G) : LaxData F.model.toPreModel G.model.toPreModel where
  cell := σ.app
  str B := eqToHom (by
      change (G.model.P B).lift _ ≫ ((G.model.P B).π 0 ≫ G.map B.2.2) = _
      rw [← Category.assoc ((G.model.P B).lift _)]
      rw [Product.lift_π]
      exact Category.assoc _ _ _) ≫
    ((F.model.P B).π 0 ◁ σ.nat B.2.2) ≫ eqToHom (Category.assoc _ _ _).symm

/-- The structure 2-cell of `σ.toLaxData` at `f` is `ConjEq` to `π₀ ◁ σ.nat f`. -/
lemma LaxNat.toLaxData_str (σ : LaxNat F G) {a b : A} (f : a ⟶ b) :
    ConjEq (σ.toLaxData.str ⟨a, b, f⟩) ((F.model.P ⟨a, b, f⟩).π 0 ◁ σ.nat f) :=
  ConjEq.conj _ _ _

variable (F G)

/-- The naturality 2-cells read off from `σ.toLaxData` are those of the lax transformation `σ`. -/
lemma natOf_toLaxData (σ : LaxNat F G) {a b : A} (f : a ⟶ b) :
    natOf F G σ.toLaxData f = σ.nat f :=
  ((natOf_conj F G σ.toLaxData f).trans
    (((ConjEq.whiskerLeft _ (σ.toLaxData_str f)).trans (ConjEq.whiskerLeft_comp₁ _ _ _).symm).trans
      ((ConjEq.whiskerLeft_congr' (lift_id_π F f) _).trans (ConjEq.id_whiskerLeft _)))).eq

/-- The structure 2-cell of lax data `L` at the symbol `f` is `ConjEq` to `π₀ ◁ natOf F G L f`. -/
lemma laxStr_eq (L : LaxData F.model.toPreModel G.model.toPreModel) {a b : A} (f : a ⟶ b) :
    ConjEq (L.str ⟨a, b, f⟩) ((F.model.P ⟨a, b, f⟩).π 0 ◁ natOf F G L f) := by
  have hl : (F.model.P ⟨a, b, f⟩).lift (F.model.P ⟨a, b, f⟩).π = 𝟙 _ := by
    simpa using (F.model.P ⟨a, b, f⟩).lift_uniq (𝟙 _)
  have h1 : ConjEq (L.strAt ⟨a, b, f⟩ (F.model.P ⟨a, b, f⟩).π) (L.str ⟨a, b, f⟩) :=
    (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft_congr' hl _).trans (ConjEq.id_whiskerLeft _))
  exact h1.symm.trans (strAt_eq F G L f (F.model.P ⟨a, b, f⟩).π ((F.model.P ⟨a, b, f⟩).π 0) rfl)

variable {F G}

/-- The lax morphism `M_F → M_G` of a lax natural transformation. -/
def LaxNat.toLaxMor (σ : LaxNat F G) : LaxMor F.model G.model where
  toLaxData := σ.toLaxData
  tr_compat τ := (LaxData.tr_compat_iff _ τ).mp (laxTrLaw_generic_of_id F G _ τ (by
    cases τ with
    | cell η =>
      refine (laxTrLaw_cell_iff F G _ η).mpr ?_
      simp only [natOf_toLaxData]
      exact σ.nat_cell η
    | comp f g =>
      refine (laxTrLaw_comp_iff F G _ f g).mpr ?_
      simp only [natOf_toLaxData]
      exact σ.nat_comp f g
    | unit a =>
      refine (laxTrLaw_unit_iff F G _ a).mpr ?_
      simp only [natOf_toLaxData]
      exact σ.nat_id a))

/-- The lax natural transformation of a lax morphism `M_F → M_G`. -/
def LaxNat.ofLaxMor (L : LaxMor F.model G.model) : LaxNat F G where
  app := L.cell
  nat f := natOf F G L.toLaxData f
  nat_cell η := (laxTrLaw_cell_iff F G _ η).mp
    (laxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  nat_comp f g := (laxTrLaw_comp_iff F G _ f g).mp
    (laxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  nat_id a := (laxTrLaw_unit_iff F G _ a).mp
    (laxTrLaw_id_of_generic F G _ _ (L.trLaw _))

omit [HasChosenFinProducts.{u, v, w} K] in
/-- Extensionality for lax natural transformations: equal components and heterogeneously equal
naturality 2-cells. -/
lemma LaxNat.ext' {σ τ : LaxNat F G} (ha : σ.app = τ.app)
    (hn : ∀ (a b : A) (f : a ⟶ b), HEq (σ.nat f) (τ.nat f)) : σ = τ := by
  obtain ⟨app, nat, _, _, _⟩ := σ
  obtain ⟨app', nat', _, _, _⟩ := τ
  dsimp only at ha hn
  subst ha
  have : @nat = @nat' := by
    funext a b f
    exact eq_of_heq (hn a b f)
  subst this
  rfl

variable (F G)

/-- **Example 3.12** ([forsman2026syntactic]): lax natural transformations are lax morphisms of
models. -/
def laxEquiv : LaxNat F G ≃ LaxMor F.model G.model where
  toFun σ := σ.toLaxMor
  invFun L := LaxNat.ofLaxMor L
  left_inv σ := LaxNat.ext' rfl (fun _ _ f => heq_of_eq (natOf_toLaxData F G σ f))
  right_inv L := LaxMor.ext' rfl (by
    rintro ⟨a, b, f⟩
    refine ConjEq.heq ?_
    exact (ConjEq.conj _ _ _).trans (laxStr_eq F G L.toLaxData f).symm)

/-- For lax transformations `σ, τ` and components `app`, the 2-cell compatibility of `app` as a
2-cell of lax morphisms at `f` is the modification axiom
`(app a ▷ G f) ≫ τ.nat f = σ.nat f ≫ (F f ◁ app b)` (Example 3.12). -/
lemma laxStrCompat_iff (σ τ : LaxNat F G) (app : ∀ c, σ.app c ⟶ τ.app c) {a b : A}
    (f : a ⟶ b) :
    ((prodApp (M := F.model.toPreModel) (N := G.model.toPreModel) (Hc := σ.toLaxData.cell)
        (H'c := τ.toLaxData.cell) app ⟨a, b, f⟩ ▷ G.model.fn ⟨a, b, f⟩) ≫
        τ.toLaxData.str ⟨a, b, f⟩ =
      σ.toLaxData.str ⟨a, b, f⟩ ≫ (F.model.fn ⟨a, b, f⟩ ◁ app b)) ↔
    ((app a ▷ G.map f) ≫ τ.nat f = σ.nat f ≫ (F.map f ◁ app b)) := by
  refine (ConjEq.eq_iff
    ((F.prodApp_whisker G (Hc := σ.toLaxData.cell) (H'c := τ.toLaxData.cell) app f).comp
      (τ.toLaxData_str f))
    ((σ.toLaxData_str f).comp (F.fn_whiskerLeft f (app b)))).trans ?_
  rw [← Bicategory.whiskerLeft_comp ((F.model.P ⟨a, b, f⟩).π 0),
    ← Bicategory.whiskerLeft_comp ((F.model.P ⟨a, b, f⟩).π 0)]
  exact ⟨fun h => whiskerLeft_cancel_of_section _ _ (lift_id_π F f) h, fun h => by rw [h]⟩

/-- Modifications are 2-cells of lax morphisms. -/
def laxModifEquiv (σ τ : LaxNat F G) :
    LaxModif σ τ ≃ LaxTwoCell σ.toLaxData τ.toLaxData where
  toFun Γ := ⟨Γ.app, fun B => (laxStrCompat_iff F G σ τ Γ.app B.2.2).mpr (Γ.naturality B.2.2)⟩
  invFun α := ⟨α.app, fun f => (laxStrCompat_iff F G σ τ α.app f).mp (α.str_compat ⟨_, _, f⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A lax transformation `σ` is pseudo iff its lax morphism of models `laxEquiv F G σ` is strong
(Example 3.12 of [forsman2026syntactic]). -/
lemma laxIsPseudo_iff (σ : LaxNat F G) :
    σ.IsPseudo ↔ ∀ B, IsIso ((laxEquiv F G σ).str B) := by
  constructor
  · rintro h ⟨a, b, f⟩
    have := h f
    exact (σ.toLaxData_str f).isIso_iff.mpr inferInstance
  · intro h a b f
    rw [← natOf_toLaxData F G σ f]
    have : IsIso (σ.toLaxData.str ⟨a, b, f⟩) := h ⟨a, b, f⟩
    exact (natOf_conj F G σ.toLaxData f).isIso_iff.mpr inferInstance

/-- A lax transformation `σ` is strict iff the structure 2-cells of its lax morphism of models
`laxEquiv F G σ` are identities (`eqToHom`s) (Example 3.12 of [forsman2026syntactic]). -/
lemma laxIsStrict_iff (σ : LaxNat F G) :
    σ.IsStrict ↔ ∀ B, ∃ h, (laxEquiv F G σ).str B = eqToHom h := by
  constructor
  · rintro hs ⟨a, b, f⟩
    obtain ⟨h, hh⟩ := hs f
    exact (σ.toLaxData_str f).exists_eqToHom_iff.mpr
      ⟨congr((F.model.P ⟨a, b, f⟩).π 0 ≫ $h),
        by rw [hh, Bicategory.whiskerLeft_eqToHom]⟩
  · intro H a b f
    obtain ⟨h, hh⟩ := H ⟨a, b, f⟩
    rw [← natOf_toLaxData F G σ f]
    exact (natOf_conj F G (laxEquiv F G σ).toLaxData f).exists_eqToHom_iff.mpr
      ⟨congr((F.model.P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ≫ $h),
        by rw [hh, Bicategory.whiskerLeft_eqToHom]⟩

end Lax

end Paper.TwoFun

end UlmerBialgebras
