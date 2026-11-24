module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import UlmerBialgebras.Models.Semantics

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Lax morphisms of Σ-models

Definition 3.10 of *A Syntactic Approach to Ulmer's Bialgebras*, together with the
comparison 2-cells `η_{t}` and the substitution Lemma 3.18.

## Main results

* `UlmerBialgebras.LaxData`, `UlmerBialgebras.LaxMor`: lax morphisms of Σ-models (Definition 3.10).
* `UlmerBialgebras.LaxData.eta`: the comparison 2-cell `η_t` at an environment (Definition 3.10
  (2)).
* `UlmerBialgebras.LaxData.eta_subst`: the factorization (3.3) of `η` along a substitution
  (Lemma 3.18).
* `UlmerBialgebras.LaxData.eta_isIso_of_strong`: for a strong morphism every `η_t` is invertible.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Lemma 3.18
-/

universe u v w uᵥ u𝓌

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

/-- The data of a lax morphism: a 1-cell for each category symbol and a structure 2-cell
for each functor symbol. -/
structure LaxData (M N : PreModel Sg Obj) where
  /-- The 1-cell attached to a category symbol. -/
  cell : ∀ c : Sg.Cat, M.obj c ⟶ N.obj c
  /-- The structure 2-cell `η^B : N(B) ∘ F_c̄ ⇒ F_d ∘ M(B)` attached to a functor symbol. -/
  str : ∀ B : Sg.Fun,
    ((N.P B).lift (fun i => (M.P B).π i ≫ cell (Sg.art B i)) ≫ N.fn B) ⟶
      (M.fn B ≫ cell (Sg.fcod B))

namespace LaxData

variable {M N : PreModel Sg Obj} (F : LaxData M N)

/-- The 1-cell `F_c̄ : M_c̄ → N_c̄` on the product of an arity. -/
abbrev prodCell (B : Sg.Fun) : (M.P B).pt ⟶ (N.P B).pt :=
  (N.P B).lift (fun i => (M.P B).π i ≫ F.cell (Sg.art B i))

/-- Composing a lift into the product `M(c̄)` with `F_{c̄}` is the lift of the composites
`g i ≫ F_{c_i}`. -/
lemma lift_comp_prodCell (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (M.P B).lift g ≫ F.prodCell B = (N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) := by
  rw [(N.P B).comp_lift]
  congr 1
  funext i
  rw [← Category.assoc, (M.P B).lift_π]

/-- The source of `LaxData.strAt`: `⟨g_i ≫ F_{c_i}⟩ ≫ N(B)` is `⟨g⟩ ≫ F_{c̄} ≫ N(B)`. -/
lemma strAt_src_eq (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) ≫ N.fn B =
      (M.P B).lift g ≫ F.prodCell B ≫ N.fn B := by
  rw [← Category.assoc, F.lift_comp_prodCell]

/-- The structure 2-cell of a lax morphism, at an arbitrary family of arguments. -/
def strAt (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    ((N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) ≫ N.fn B) ⟶
      (((M.P B).lift g ≫ M.fn B) ≫ F.cell (Sg.fcod B)) :=
  eqToHom (strAt_src_eq F B g) ≫ ((M.P B).lift g ◁ F.str B) ≫
    eqToHom (Category.assoc ((M.P B).lift g) (M.fn B) (F.cell (Sg.fcod B))).symm

/-- The comparison 2-cell `η_{t}` of Definition 3.10 (2), at an arbitrary environment. -/
def eta {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v)) :
    ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c),
      N.interp (fun v => ρ v ≫ F.cell (vty v)) t ⟶ M.interp ρ t ≫ F.cell c
  | _, .var _ => 𝟙 _
  | _, .app B args =>
      N.appCell B (fun i => eta ρ (args i)) ≫ F.strAt B (fun i => M.interp ρ (args i))

/-- The comparison 2-cell `η_v` of a lax morphism at a variable is the identity. -/
@[simp] lemma eta_var {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (v : V) : F.eta ρ (Trm.var v) = 𝟙 _ := by simp [eta]

/-- The comparison 2-cell of a lax morphism at `B(args)` is `N(B)` applied to the comparison
2-cells at the arguments, followed by the structure 2-cell `η^B`. -/
@[simp] lemma eta_app {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (B : Sg.Fun) (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    F.eta ρ (Trm.app B args) =
      N.appCell B (fun i => F.eta ρ (args i)) ≫ F.strAt B (fun i => M.interp ρ (args i)) := by
  simp [eta]

/-- Transporting `eta` along an equality of environments. -/
lemma eta_congr {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)}
    (e : ∀ v, ρ v = ρ' v) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    F.eta ρ' t = eqToHom (by rw [funext e]) ≫ F.eta ρ t ≫ eqToHom (by rw [funext e]) := by
  have hρ : ρ = ρ' := funext e
  subst hρ
  simp

/-- Transporting `strAt` along an equality of the family of arguments. -/
lemma strAt_congr (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (e : ∀ i, g i = g' i) :
    F.strAt B g' = eqToHom (by rw [funext e]) ≫ F.strAt B g ≫ eqToHom (by rw [funext e]) := by
  have hgg : g = g' := funext e
  subst hgg
  simp

/-- `strAt` is compatible with precomposition. -/
lemma strAt_precomp (B : Sg.Fun) {x y : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) (h : y ⟶ x) :
    h ◁ (F.strAt B g) = eqToHom (by
        rw [show (fun i => (h ≫ g i) ≫ F.cell (Sg.art B i)) =
              (fun i => h ≫ (g i ≫ F.cell (Sg.art B i))) from funext fun i => Category.assoc _ _ _,
          ← (N.P B).comp_lift, ← Category.assoc]) ≫
      F.strAt B (fun i => h ≫ g i) ≫
      eqToHom (by rw [← Category.assoc, ← Category.assoc, (M.P B).comp_lift]) := by
  rw [strAt, strAt]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
  rw [Bicategory.Strict.comp_whiskerLeft' h ((M.P B).lift g) (F.str B),
    Bicategory.whiskerLeft_congr ((M.P B).comp_lift h g).symm (F.str B)]
  simp

/-- The naturality of the structure 2-cell in the arguments: the "interchange" step. -/
lemma strAt_nat (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (γ : ∀ i, g i ⟶ g' i) :
    N.appCell B (fun i => γ i ▷ F.cell (Sg.art B i)) ≫ F.strAt B g'
      = F.strAt B g ≫ (M.appCell B γ ▷ F.cell (Sg.fcod B)) := by
  -- Both `appCell`s are whiskerings of the one 2-cell `A` between the lifts (`hMapp`, `hNapp`);
  -- the square is then the interchange law for `A` and `F.str B`.
  set A : (M.P B).lift g ⟶ (M.P B).lift g' :=
    (M.P B).lift₂ (fun i => eqToHom ((M.P B).lift_π g i) ≫ γ i ≫
      eqToHom ((M.P B).lift_π g' i).symm) with hA
  have hMapp : M.appCell B γ = A ▷ M.fn B := rfl
  have hNapp : N.appCell B (fun i => γ i ▷ F.cell (Sg.art B i))
      = eqToHom (by rw [F.lift_comp_prodCell B g]) ≫ ((A ▷ F.prodCell B) ▷ N.fn B) ≫
        eqToHom (by rw [F.lift_comp_prodCell B g']) := by
    have h1 : ∀ i, (A ▷ F.prodCell B) ▷ (N.P B).π i
        = eqToHom (by rw [Category.assoc, (N.P B).lift_π, ← Category.assoc, (M.P B).lift_π]) ≫
          (γ i ▷ F.cell (Sg.art B i)) ≫
          eqToHom (by rw [Category.assoc, (N.P B).lift_π, ← Category.assoc, (M.P B).lift_π]) := by
      intro i
      have e1 := Bicategory.Strict.whiskerRight_comp A (F.prodCell B) ((N.P B).π i)
      rw [Bicategory.whiskerRight_congr A
          (((N.P B).lift_π (fun j => (M.P B).π j ≫ F.cell (Sg.art B j)) i).symm),
        Bicategory.Strict.whiskerRight_comp A ((M.P B).π i) (F.cell (Sg.art B i)), hA,
        (M.P B).lift₂_π] at e1
      rw [← hA] at e1
      simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
        eqToHom_trans] at e1
      simpa using eqToHom_conj e1.symm
    have h2 : (N.P B).lift₂ (fun i =>
          eqToHom ((N.P B).lift_π (fun i => g i ≫ F.cell (Sg.art B i)) i) ≫
            (γ i ▷ F.cell (Sg.art B i)) ≫
            eqToHom ((N.P B).lift_π (fun i => g' i ≫ F.cell (Sg.art B i)) i).symm)
        = eqToHom (F.lift_comp_prodCell B g).symm ≫ (A ▷ F.prodCell B) ≫
          eqToHom (F.lift_comp_prodCell B g') := by
      refine (N.P B).cell_ext (fun i => ?_)
      rw [(N.P B).lift₂_π]
      simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
      rw [h1 i]
      simp
    rw [PreModel.appCell, h2]
    simp
  rw [hNapp, hMapp, strAt, strAt]
  have ex := Eq.symm <| Bicategory.whisker_exchange A (F.str B)
  rw [Bicategory.Strict.whiskerRight_comp A (F.prodCell B) (N.fn B),
    Bicategory.Strict.whiskerRight_comp A (M.fn B) (F.cell (Sg.fcod B))] at ex
  simp only [Category.assoc, eqToHom_trans_assoc] at ex ⊢
  rw [reassoc_of% ((eqToHom_comp_iff _ _ _).1 ex)]
  simp

/-- Equation (3.3) of Lemma 3.18 (auxiliary form): compatibility of `η` with precomposition. -/
lemma eta_precomp {V : Type uᵥ} {vty : V → Sg.Cat} {x y : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (h : y ⟶ x) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    F.eta (fun v => h ≫ ρ v) t =
      eqToHom (by
        rw [show (fun v => (h ≫ ρ v) ≫ F.cell (vty v)) =
          (fun v => h ≫ (ρ v ≫ F.cell (vty v))) from funext fun v => Category.assoc _ _ _,
          N.interp_comp]) ≫
      (h ◁ F.eta ρ t) ≫
      eqToHom (by rw [← Category.assoc, ← M.interp_comp]) := by
  induction t with
  | var v => simp
  | app B args ih =>
      rw [eta_app, eta_app, N.appCell_congr B ih,
        F.strAt_congr B (g := fun i => h ≫ M.interp ρ (args i))
          (fun i => (M.interp_comp h ρ (args i)).symm),
        ← N.appCell_comp, ← N.appCell_comp, Bicategory.whiskerLeft_comp,
        N.whiskerLeft_appCell B (fun i => F.eta ρ (args i)) h,
        F.strAt_precomp B (fun i => M.interp ρ (args i)) h]
      simp

/-- Equation (3.3) of Lemma 3.18: the factorisation of `η` along a substitution. -/
lemma eta_subst {V : Type uᵥ} {W : Type u𝓌} {vty : V → Sg.Cat} {wty : W → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (wty v)) (sub : ∀ v : V, Trm Sg.toFunSig wty (vty v))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    F.eta ρ (t.subst sub) =
      eqToHom (by rw [N.interp_subst]) ≫
        N.interpCell (fun v => F.eta ρ (sub v)) t ≫
        F.eta (fun v => M.interp ρ (sub v)) t ≫
        eqToHom (by rw [← M.interp_subst]) := by
  induction t with
  | var v =>
      have hN (p : N.interp (fun v => ρ v ≫ F.cell (wty v)) ((Trm.var v).subst sub) =
          N.interp (fun v => N.interp (fun v => ρ v ≫ F.cell (wty v)) (sub v)) (Trm.var v)) :
          eqToHom p = (𝟙 _ : N.interp (fun v => ρ v ≫ F.cell (wty v)) (sub v) ⟶ _) := rfl
      have h1 := hN (by rw [N.interp_subst])
      rw [h1]
      simp [Trm.subst]
  | app B args ih =>
      change F.eta ρ (Trm.app B fun i => (args i).subst sub) = _
      rw [eta_app, N.appCell_congr B ih,
        F.strAt_congr B (g := fun i => M.interp (fun v => M.interp ρ (sub v)) (args i))
          (fun i => (M.interp_subst ρ sub (args i)).symm),
        ← N.appCell_comp, ← N.appCell_comp, ← N.appCell_comp,
        N.interpCell_app_appCell, eta_app]
      simp
      rfl

/-- The structure 2-cell at arbitrary arguments is invertible when `str B` is. -/
instance strAt_isIso (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i))
    [IsIso (F.str B)] : IsIso (F.strAt B g) := by
  rw [strAt]; infer_instance

/-- If `t` is a sort (a variable), the comparison 2-cell `η_t` is the identity. -/
lemma eta_isVar {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    {c : Sg.Cat} {t : Trm Sg.toFunSig vty c} (h : t.IsVar) : IsIso (F.eta ρ t) := by
  cases t with
  | var v => rw [eta_var]; infer_instance
  | app B args => exact h.elim

/-- For a *strong* morphism every comparison 2-cell `η_t` is invertible. -/
lemma eta_isIso_of_strong (hstr : ∀ B : Sg.Fun, IsIso (F.str B)) {V : Type uᵥ} {vty : V → Sg.Cat}
    {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    IsIso (F.eta ρ t) := by
  induction t with
  | var v => rw [eta_var]; infer_instance
  | app B args ih =>
      have : ∀ i, IsIso (F.eta ρ (args i)) := ih
      have := hstr B
      rw [eta_app]
      infer_instance

end LaxData

/-- A lax morphism of Σ-models (Definition 3.10). -/
structure LaxMor (M N : Model Sg Obj) extends LaxData M.toPreModel N.toPreModel where
  /-- Compatibility with the transformation symbols, Definition 3.10 (3). -/
  tr_compat : ∀ a : Sg.Tr,
    (N.trAt a (fun i => (M.Pctx a).π i ≫ toLaxData.cell (Sg.trt a i))) ≫
        toLaxData.eta (M.Pctx a).π (Sg.trtgt a)
      = toLaxData.eta (M.Pctx a).π (Sg.trsrc a) ≫ (M.tr a ▷ toLaxData.cell (Sg.trty a))

namespace LaxMor

variable {M N : Model Sg Obj} (F : LaxMor M N)

/-- Compatibility with the transformation symbols at an arbitrary environment. -/
lemma tr_compat_at (a : Sg.Tr) {x : Obj} (ρ : ∀ i, x ⟶ M.obj (Sg.trt a i)) :
    (N.trAt a (fun i => ρ i ≫ F.cell (Sg.trt a i))) ≫ F.toLaxData.eta ρ (Sg.trtgt a)
      = F.toLaxData.eta ρ (Sg.trsrc a) ≫ (M.trAt a ρ ▷ F.cell (Sg.trty a)) := by
  -- Whisker the compatibility `F.tr_compat a` (at the generic context) by the lift of `ρ`, and
  -- read each side at `ρ` (`e1`, `e2`, `e3`); the transports then cancel.
  have hρ : ∀ i, (M.Pctx a).lift ρ ≫ (M.Pctx a).π i = ρ i := fun i => (M.Pctx a).lift_π ρ i
  have e1 := N.trAt_precomp a (fun i => (M.Pctx a).π i ≫ F.cell (Sg.trt a i)) ((M.Pctx a).lift ρ)
  rw [N.trAt_congr a (ρ := fun i => ρ i ≫ F.cell (Sg.trt a i))
    (fun i => by rw [← Category.assoc, hρ])] at e1
  have e2 : ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig (Sg.trt a) c),
      (M.Pctx a).lift ρ ◁ F.toLaxData.eta (M.Pctx a).π t
        = eqToHom (by
            rw [← N.toPreModel.interp_comp]
            exact N.toPreModel.interp_congr (fun v => by rw [← Category.assoc, hρ]) t) ≫
          F.toLaxData.eta ρ t ≫
          eqToHom (by rw [← Category.assoc, ← M.interp_lift_ctx]) := by
    intro c t
    have p := F.toLaxData.eta_precomp (M.Pctx a).π ((M.Pctx a).lift ρ) t
    rw [F.toLaxData.eta_congr (fun i => (hρ i).symm) t] at p
    simpa using eqToHom_conj p.symm
  have e3 : (M.Pctx a).lift ρ ◁ (M.tr a ▷ F.cell (Sg.trty a))
      = eqToHom (by rw [← Category.assoc, ← M.interp_lift_ctx]) ≫
        (M.trAt a ρ ▷ F.cell (Sg.trty a)) ≫
        eqToHom (by rw [← Category.assoc, ← M.interp_lift_ctx]) := by
    have q : (M.Pctx a).lift ρ ◁ M.tr a
        = eqToHom (M.interp_lift_ctx a ρ (Sg.trsrc a)).symm ≫ M.trAt a ρ ≫
          eqToHom (M.interp_lift_ctx a ρ (Sg.trtgt a)) := by
      rw [Model.trAt]; simp
    rw [Bicategory.Strict.whisker_assoc, q]
    simp
  have key := congr((M.Pctx a).lift ρ ◁ $(F.tr_compat a))
  simp only [Bicategory.whiskerLeft_comp] at key
  rw [e1, e2, e2, e3] at key
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] at key
  rw [cancel_epi] at key
  simp only [← Category.assoc] at key
  rw [cancel_mono] at key
  exact key

end LaxMor

end UlmerBialgebras
