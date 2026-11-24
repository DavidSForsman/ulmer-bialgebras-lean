module

public import UlmerBialgebras.Proofs.Sec3.TwoFunctorModel

/-!
# Oplax morphisms between the models of strict 2-functors

The oplax morphisms `M_F → M_G` between the `Σ`-models of strict 2-functors `F, G : K → A`,
continuing `UlmerBialgebras/Proofs/Sec3/TwoFunctorModel.lean`, which treats the lax ones.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras

open CategoryTheory
open scoped CategoryTheory.Bicategory

namespace Paper.TwoFun

open CategoryTheory

variable {A : Type ua} [Bicategory.{wa, va} A] [Bicategory.Strict A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K]

open StrictTwoFunctor

variable (F G : StrictTwoFunctor K A)

/-! ### Oplax morphisms `M_F → M_G` -/

section Oplax

/-- The naturality 2-cell of oplax data `L : M_F → M_G` at a 1-cell `f`, read off at the
identity environment. -/
def opNatOf (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b : A} (f : a ⟶ b) :
    F.map f ≫ L.cell b ⟶ L.cell a ≫ G.map f :=
  eqToHom (by
      rw [model_fn, ← Category.assoc _ _ (F.map f), Product.lift_π, Category.id_comp]) ≫
    L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) ≫
    eqToHom (by
      rw [model_fn, ← Category.assoc, Product.lift_π, Category.id_comp])

/-- `opNatOf F G L f` is `ConjEq` to the structure 2-cell `L.str f` whiskered by the section
`lift (id)` of the unary product. -/
lemma opNatOf_conj (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b : A}
    (f : a ⟶ b) :
    ConjEq (opNatOf F G L f)
      ((F.model.P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ◁ L.str ⟨a, b, f⟩) :=
  (ConjEq.conj _ _ (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)))).trans (ConjEq.conj _ _ _)

/-- The structure 2-cell of oplax data `L` at the symbol `f` and an environment `g` with `g 0 = k`
is `ConjEq` to `k ◁ opNatOf F G L f`. -/
lemma opStrAt_eq (L : OplaxData F.model.toPreModel G.model.toPreModel) {x : K} {a b : A}
    (f : a ⟶ b) (g : ∀ _ : Fin 1, x ⟶ F.obj a) (k : x ⟶ F.obj a) (hk : g 0 = k) :
    ConjEq (L.strAt ⟨a, b, f⟩ g) (k ◁ opNatOf F G L f) := by
  subst hk
  have pre := L.strAt_precomp ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) (g 0)
  have cg := L.strAt_congr ⟨a, b, f⟩ (g := fun _ => g 0 ≫ 𝟙 (F.obj a)) (g' := g)
    (fun i => by simp only [Category.comp_id]; exact congr(g $((Fin.fin_one_eq_zero i).symm)))
  have hn : ConjEq (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a))) (opNatOf F G L f) :=
    (ConjEq.conj _ _ _).symm
  exact (ConjEq.intro cg).trans ((ConjEq.intro pre).symm.trans (ConjEq.whiskerLeft (g 0) hn))

/-- The comparison 2-cell `eta` of oplax data `L` on the unary term `f(x)` at the identity
environment is `ConjEq` to `opNatOf F G L f`. -/
lemma oplaxEta_app1 (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b : A}
    (f : a ⟶ b) :
    ConjEq (L.eta (fun _ : Fin 1 => 𝟙 (F.obj a))
        (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => a) (0 : Fin 1))))
      (opNatOf F G L f) := by
  rw [OplaxData.eta_app]
  simp only [OplaxData.eta_var, PreModel.appCell_id, Category.comp_id, PreModel.interp_var]
  exact (opStrAt_eq F G L f (fun _ => 𝟙 (F.obj a)) (𝟙 _) rfl).trans
    (ConjEq.id_whiskerLeft _)

/-- The comparison 2-cell `eta` of oplax data `L` on the term `g(f(x))` at the identity environment
is `ConjEq` to the pasting `(F f ◁ opNatOf g) ≫ (opNatOf f ▷ G g)`. -/
lemma oplaxEta_app1_app1 (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    ConjEq (L.eta (fun _ : Fin 1 => 𝟙 (F.obj a))
        (app1 A g (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => a) (0 : Fin 1)))))
      ((F.map f ◁ opNatOf F G L g) ≫ eqToHom (Category.assoc _ _ _).symm ≫
        (opNatOf F G L f ▷ G.map g)) := by
  rw [OplaxData.eta_app]
  refine ConjEq.comp (opStrAt_eq F G L g _ (F.map f) (by rw [F.interp_app1]; simp)) ?_
  exact ((G.appCell_eq g _).trans ((oplaxEta_app1 F G L f).whiskerRight (G.map g))).trans
    (ConjEq.eqToHom_comp (ConjEq.of_eq rfl) _).symm

/-- The transformation-symbol law of oplax data `L` for a 2-cell `η : f ⟶ g` (at the identity
environment) is the 2-cell axiom of an oplax transformation for `opNatOf`. -/
lemma oplaxTrLaw_cell_iff (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b : A}
    {f g : a ⟶ b} (η : f ⟶ g) :
    L.TrLaw (SigTr.cell η) (F.idEnv (SigTr.cell η)) ↔
      (F.map₂ η ▷ L.cell b) ≫ opNatOf F G L g = opNatOf F G L f ≫ (L.cell a ◁ G.map₂ η) :=
  ConjEq.eq_iff
    ((((F.trAt_cell η (F.idEnv (SigTr.cell η)) (𝟙 (F.obj a)) rfl).trans
        (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell b)).comp (oplaxEta_app1 F G L g))
    ((oplaxEta_app1 F G L f).comp
      (G.trAt_cell η
        (fun i => F.idEnv (SigTr.cell η) i ≫ L.cell ((sigOf A).trt (SigTr.cell η) i))
        (L.cell a) (Category.id_comp _)))

/-- The transformation-symbol law of oplax data `L` for a composite `f ≫ g` (at the identity
environment) is the composition axiom of an oplax transformation for `opNatOf`. -/
lemma oplaxTrLaw_comp_iff (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    L.TrLaw (SigTr.comp f g) (F.idEnv (SigTr.comp f g)) ↔
      opNatOf F G L (f ≫ g) = eqToHom (by rw [F.map_comp, Category.assoc]) ≫
        (F.map f ◁ opNatOf F G L g) ≫ eqToHom (Category.assoc _ _ _).symm ≫
        (opNatOf F G L f ▷ G.map g) ≫ eqToHom (by rw [G.map_comp, Category.assoc]) := by
  obtain ⟨r₁, hr₁⟩ := G.trAt_comp f g
    (fun i => F.idEnv (SigTr.comp f g) i ≫ L.cell ((sigOf A).trt (SigTr.comp f g) i))
  obtain ⟨r₂, hr₂⟩ := F.trAt_comp f g (F.idEnv (SigTr.comp f g))
  unfold OplaxData.TrLaw
  rw [hr₁, hr₂]
  simp only [Bicategory.eqToHom_whiskerRight]
  refine (ConjEq.eq_iff_conj ((oplaxEta_app1_app1 F G L f g).eqToHom_comp _)
    ((oplaxEta_app1 F G L (f ≫ g)).comp_eqToHom _) (by rw [F.map_comp, Category.assoc])
    (by rw [G.map_comp, Category.assoc])).trans ?_
  simp only [Category.assoc, iff_self]

/-- The transformation-symbol law of oplax data `L` for an identity `𝟙 a` (at the identity
environment) is the unit axiom of an oplax transformation: `opNatOf (𝟙 a)` is an `eqToHom`. -/
lemma oplaxTrLaw_unit_iff (L : OplaxData F.model.toPreModel G.model.toPreModel) (a : A) :
    L.TrLaw (SigTr.unit a) (F.idEnv (SigTr.unit a)) ↔
      opNatOf F G L (𝟙 a) = eqToHom (by simp only [G.map_id, F.map_id, Category.comp_id,
        Category.id_comp]) := by
  have h₁ : L.eta (F.idEnv (SigTr.unit a)) ((sigOf A).trtgt (SigTr.unit a)) = 𝟙 _ :=
    L.eta_var _ 0
  obtain ⟨r₁, hr₁⟩ := G.trAt_unit a
    (fun i => F.idEnv (SigTr.unit a) i ≫ L.cell ((sigOf A).trt (SigTr.unit a) i))
  obtain ⟨r₂, hr₂⟩ := F.trAt_unit a (F.idEnv (SigTr.unit a))
  unfold OplaxData.TrLaw
  rw [h₁, hr₁, hr₂]
  simp only [Bicategory.eqToHom_whiskerRight]
  refine (iff_of_eq congr($(Category.comp_id _) = _)).trans ?_
  exact ConjEq.eqToHom_eq_iff ((oplaxEta_app1 F G L (𝟙 a)).comp_eqToHom _) _ _

/-- For oplax data, the transformation-symbol law at the identity environment implies it at the
generic environment. -/
lemma oplaxTrLaw_generic_of_id (L : OplaxData F.model.toPreModel G.model.toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ (F.idEnv τ)) : L.TrLaw τ (F.model.Pctx τ).π :=
  (H.precomp ((F.model.Pctx τ).π 0)).congr
    (fun i => by rw [Fin.fin_one_eq_zero i]; exact Category.comp_id _)

/-- For oplax data, the transformation-symbol law at the generic environment implies it at the
identity environment. -/
lemma oplaxTrLaw_id_of_generic (L : OplaxData F.model.toPreModel G.model.toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ (F.model.Pctx τ).π) : L.TrLaw τ (F.idEnv τ) :=
  (H.precomp ((F.model.Pctx τ).lift (F.idEnv τ))).congr (fun i => Product.lift_π _ _ i)

variable {F G}

/-- The oplax data of an oplax natural transformation. -/
abbrev OplaxNat.toOplaxData (σ : OplaxNat F G) :
    OplaxData F.model.toPreModel G.model.toPreModel where
  cell := σ.app
  str B := eqToHom (Category.assoc _ _ _) ≫ ((F.model.P B).π 0 ◁ σ.nat B.2.2) ≫ eqToHom (by
      change _ = (G.model.P B).lift _ ≫ ((G.model.P B).π 0 ≫ G.map B.2.2)
      rw [← Category.assoc ((G.model.P B).lift _)]
      rw [Product.lift_π]
      exact (Category.assoc _ _ _).symm)

/-- The structure 2-cell of `σ.toOplaxData` at `f` is `ConjEq` to `π₀ ◁ σ.nat f`. -/
lemma OplaxNat.toOplaxData_str (σ : OplaxNat F G) {a b : A} (f : a ⟶ b) :
    ConjEq (σ.toOplaxData.str ⟨a, b, f⟩) ((F.model.P ⟨a, b, f⟩).π 0 ◁ σ.nat f) :=
  ConjEq.conj _ _ _

variable (F G)

/-- The naturality 2-cells read off from `σ.toOplaxData` are those of the oplax transformation `σ`.
-/
lemma opNatOf_toOplaxData (σ : OplaxNat F G) {a b : A} (f : a ⟶ b) :
    opNatOf F G σ.toOplaxData f = σ.nat f :=
  ((opNatOf_conj F G σ.toOplaxData f).trans
    (((ConjEq.whiskerLeft _ (σ.toOplaxData_str f)).trans
      (ConjEq.whiskerLeft_comp₁ _ _ _).symm).trans
      ((ConjEq.whiskerLeft_congr' (lift_id_π F f) _).trans (ConjEq.id_whiskerLeft _)))).eq

/-- The structure 2-cell of oplax data `L` at the symbol `f` is `ConjEq` to `π₀ ◁ opNatOf F G L f`.
-/
lemma oplaxStr_eq (L : OplaxData F.model.toPreModel G.model.toPreModel) {a b : A}
    (f : a ⟶ b) :
    ConjEq (L.str ⟨a, b, f⟩) ((F.model.P ⟨a, b, f⟩).π 0 ◁ opNatOf F G L f) := by
  have hl : (F.model.P ⟨a, b, f⟩).lift (F.model.P ⟨a, b, f⟩).π = 𝟙 _ := by
    simpa using (F.model.P ⟨a, b, f⟩).lift_uniq (𝟙 _)
  have h1 : ConjEq (L.strAt ⟨a, b, f⟩ (F.model.P ⟨a, b, f⟩).π) (L.str ⟨a, b, f⟩) :=
    (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft_congr' hl _).trans (ConjEq.id_whiskerLeft _))
  exact h1.symm.trans
    (opStrAt_eq F G L f (F.model.P ⟨a, b, f⟩).π ((F.model.P ⟨a, b, f⟩).π 0) rfl)

variable {F G}

/-- The oplax morphism `M_F → M_G` of an oplax natural transformation. -/
def OplaxNat.toOplaxMor (σ : OplaxNat F G) : OplaxMor F.model G.model where
  toOplaxData := σ.toOplaxData
  tr_compat τ := (OplaxData.tr_compat_iff _ τ).mp (oplaxTrLaw_generic_of_id F G _ τ (by
    cases τ with
    | cell η =>
      refine (oplaxTrLaw_cell_iff F G _ η).mpr ?_
      simp only [opNatOf_toOplaxData]
      exact σ.nat_cell η
    | comp f g =>
      refine (oplaxTrLaw_comp_iff F G _ f g).mpr ?_
      simp only [opNatOf_toOplaxData]
      exact σ.nat_comp f g
    | unit a =>
      refine (oplaxTrLaw_unit_iff F G _ a).mpr ?_
      simp only [opNatOf_toOplaxData]
      exact σ.nat_id a))

/-- The oplax natural transformation of an oplax morphism `M_F → M_G`. -/
def OplaxNat.ofOplaxMor (L : OplaxMor F.model G.model) : OplaxNat F G where
  app := L.cell
  nat f := opNatOf F G L.toOplaxData f
  nat_cell η := (oplaxTrLaw_cell_iff F G _ η).mp
    (oplaxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  nat_comp f g := (oplaxTrLaw_comp_iff F G _ f g).mp
    (oplaxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  nat_id a := (oplaxTrLaw_unit_iff F G _ a).mp
    (oplaxTrLaw_id_of_generic F G _ _ (L.trLaw _))

omit [HasChosenFinProducts.{u, v, w} K] in
/-- Extensionality for oplax natural transformations: equal components and heterogeneously equal
naturality 2-cells. -/
lemma OplaxNat.ext' {σ τ : OplaxNat F G} (ha : σ.app = τ.app)
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

/-- **Example 3.12** ([forsman2026syntactic]): oplax natural transformations are oplax morphisms of
models. -/
def oplaxEquiv : OplaxNat F G ≃ OplaxMor F.model G.model where
  toFun σ := σ.toOplaxMor
  invFun L := OplaxNat.ofOplaxMor L
  left_inv σ := OplaxNat.ext' rfl (fun _ _ f => heq_of_eq (opNatOf_toOplaxData F G σ f))
  right_inv L := OplaxMor.ext' rfl (by
    rintro ⟨a, b, f⟩
    refine ConjEq.heq ?_
    exact (ConjEq.conj _ _ _).trans (oplaxStr_eq F G L.toOplaxData f).symm)

/-- For oplax transformations `σ, τ` and components `app`, the 2-cell compatibility of `app` as a
2-cell of oplax morphisms at `f` is the modification axiom
`(F f ◁ app b) ≫ τ.nat f = σ.nat f ≫ (app a ▷ G f)` (Example 3.12). -/
lemma oplaxStrCompat_iff (σ τ : OplaxNat F G) (app : ∀ c, σ.app c ⟶ τ.app c) {a b : A}
    (f : a ⟶ b) :
    ((F.model.fn ⟨a, b, f⟩ ◁ app b) ≫ τ.toOplaxData.str ⟨a, b, f⟩ =
      σ.toOplaxData.str ⟨a, b, f⟩ ≫ (prodApp (M := F.model.toPreModel)
        (N := G.model.toPreModel) (Hc := σ.toOplaxData.cell) (H'c := τ.toOplaxData.cell) app
        ⟨a, b, f⟩ ▷ G.model.fn ⟨a, b, f⟩)) ↔
    ((F.map f ◁ app b) ≫ τ.nat f = σ.nat f ≫ (app a ▷ G.map f)) := by
  refine (ConjEq.eq_iff ((F.fn_whiskerLeft f (app b)).comp (τ.toOplaxData_str f))
    ((σ.toOplaxData_str f).comp
      (F.prodApp_whisker G (Hc := σ.toOplaxData.cell) (H'c := τ.toOplaxData.cell) app f))).trans ?_
  rw [← Bicategory.whiskerLeft_comp ((F.model.P ⟨a, b, f⟩).π 0),
    ← Bicategory.whiskerLeft_comp ((F.model.P ⟨a, b, f⟩).π 0)]
  exact ⟨fun h => whiskerLeft_cancel_of_section _ _ (lift_id_π F f) h, fun h => by rw [h]⟩

/-- Modifications are 2-cells of oplax morphisms. -/
def oplaxModifEquiv (σ τ : OplaxNat F G) :
    OplaxModif σ τ ≃ OplaxTwoCell σ.toOplaxData τ.toOplaxData where
  toFun Γ := ⟨Γ.app, fun B =>
    (oplaxStrCompat_iff F G σ τ Γ.app B.2.2).mpr (Γ.naturality B.2.2)⟩
  invFun α := ⟨α.app, fun f =>
    (oplaxStrCompat_iff F G σ τ α.app f).mp (α.str_compat ⟨_, _, f⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Oplax

end Paper.TwoFun

end UlmerBialgebras
