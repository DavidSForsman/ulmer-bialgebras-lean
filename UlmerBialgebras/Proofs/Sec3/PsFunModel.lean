module

public import UlmerBialgebras.Paper.Sec3DefsPsFun
public import UlmerBialgebras.Proofs.Sec3.TwoFunctorOplaxModel

/-!
# Transformations between pseudofunctors as morphisms of models

Helper results for Example 3.12 (`UlmerBialgebras/Proofs/Sec3/Sec3Ex.lean`) for a pseudofunctor `F :
A → K` out of a
bicategory: computations in the model `M_F` (`UlmerBialgebras/Paper/Sec3DefsPsFun.lean`), the
naturality 2-cells
`natOf L f` read off lax data `L : M_F → M_G`, and the correspondence of the transformation-symbol
laws of `L` with the axioms of Mathlib's lax and oplax transformations. The composition and unit
symbols are interpreted by the invertible structure 2-cells of `F` and `G`, so their laws are the
axioms `naturality_comp`, `naturality_id` after inverting these 2-cells.

## Main results

* `UlmerBialgebras.Paper.PsFun.laxEquiv`, `UlmerBialgebras.Paper.PsFun.oplaxEquiv`: lax (oplax)
  transformations `F.toLax ⟶ G.toLax` are equivalent to lax (oplax) morphisms `M_F → M_G`, and
  `laxModifEquiv`, `oplaxModifEquiv` do the same for modifications and 2-cells.
* `UlmerBialgebras.Paper.PsFun.laxIsIso_iff`, `laxIsStrict_iff` (and the oplax versions): a
  transformation has invertible (identity) naturality 2-cells iff its morphism of models is strong
  (strict).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples 3.9 and
  3.12
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras

open CategoryTheory
open scoped CategoryTheory.Bicategory

section Iso

variable {C : Type*} [Category C]

/-- A morphism `ConjEq` to the morphism of an isomorphism is the morphism of an isomorphism whose
inverse is `ConjEq` to the inverse. -/
lemma ConjEq.exists_iso {X Y X' Y' : C} {u : X ⟶ Y} {e : X' ≅ Y'} (h : ConjEq u e.hom) :
    ∃ e' : X ≅ Y, e'.hom = u ∧ ConjEq e'.inv e.inv := by
  obtain ⟨p, q, rfl⟩ := h
  subst p; subst q
  exact ⟨e, by simp, ConjEq.of_eq rfl⟩

/-- A morphism is `ConjEq` to its composite with an `eqToHom`. -/
lemma ConjEq.self_comp_eqToHom {X Y Y' : C} (u : X ⟶ Y) (r : Y = Y') :
    ConjEq u (u ≫ eqToHom r) :=
  (ConjEq.comp_eqToHom (ConjEq.of_eq rfl) r).symm

/-- A square with invertible horizontal sides commutes iff the square of the inverses does. -/
lemma iso_square_iff {X Y X' Y' : C} (i : X ≅ X') (j : Y ≅ Y') (a : X' ⟶ Y') (b : X ⟶ Y) :
    i.hom ≫ a = b ≫ j.hom ↔ i.inv ≫ b = a ≫ j.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact eq_comm

end Iso

namespace Paper.PsFun

variable {A : Type ua} [Bicategory.{wa, va} A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K]

/-! ### Computations in the model `M_F` -/

section Model

variable (F : Pseudofunctor A K)

/-- In the model `M_F` of a pseudofunctor, the term `f(t)` is interpreted as `M_F(t) ≫ F f`. -/
lemma interp_app1 {V : Type} {vty : V → A} {x : K} (ρ : ∀ v, x ⟶ (model F).obj (vty v))
    {a b : A} (f : a ⟶ b) (t : Trm (funSigOf A) vty a) :
    (model F).interp ρ (app1 A f t) = (model F).interp ρ t ≫ F.map f :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ F.map f) (Product.lift_π _ _ 0))

/-- The identity environment of the context of a transformation symbol. -/
def idEnv (τ : SigTr A) :
    ∀ i : Fin ((sigOf A).trn τ), F.obj τ.src ⟶ (model F).obj ((sigOf A).trt τ i) :=
  fun _ => 𝟙 (F.obj τ.src)

/-- In `M_F`, the 2-cell `appCell` of the function symbol `f` applied to `γ` is `ConjEq` to
`γ 0 ▷ F f`. -/
lemma appCell_eq {x : K} {a b : A} (f : a ⟶ b) {g g' : ∀ _ : Fin 1, x ⟶ F.obj a}
    (γ : ∀ i, g i ⟶ g' i) : ConjEq ((model F).appCell ⟨a, b, f⟩ γ) (γ 0 ▷ F.map f) := by
  refine (ConjEq.whiskerRight_comp₁ _ _ _).trans (ConjEq.whiskerRight ?_ (F.map f))
  rw [Product.lift₂_π]
  exact ConjEq.conj _ _ _

/-- Whiskering the interpretation of a transformation symbol, given as `p ◁ θ` up to `eqToHom`s
with `p` the projection, by the lift of an environment `ρ` with `ρ 0 = k` gives `k ◁ θ` up to
`eqToHom`s. -/
lemma trAt_of_tr (τ : SigTr A) {x : K} {u u' : F.obj τ.src ⟶ F.obj τ.tgt} (θ : u ⟶ u')
    (htr : ConjEq ((model F).tr τ) (((model F).Pctx τ).π 0 ◁ θ))
    (ρ : ∀ i, x ⟶ (model F).obj ((sigOf A).trt τ i)) (k : x ⟶ F.obj τ.src) (hk : ρ 0 = k) :
    ConjEq ((model F).trAt τ ρ) (k ◁ θ) := by
  subst hk
  have hk : ((model F).Pctx τ).lift ρ ≫ ((model F).Pctx τ).π 0 = ρ 0 := Product.lift_π _ _ 0
  unfold Model.trAt
  exact (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft _ htr).trans
    ((ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans (ConjEq.whiskerLeft_congr' hk _)))

/-- In `M_F`, the transformation symbol of a 2-cell `η : f ⟶ g` at an environment `ρ` with
`ρ 0 = k` is `ConjEq` to `k ◁ F η`. -/
lemma trAt_cell {x : K} {a b : A} {f g : a ⟶ b} (η : f ⟶ g)
    (ρ : ∀ i, x ⟶ (model F).obj ((sigOf A).trt (SigTr.cell η) i)) (k : x ⟶ F.obj a)
    (hk : ρ 0 = k) : ConjEq ((model F).trAt (SigTr.cell η) ρ) (k ◁ F.map₂ η) := by
  refine trAt_of_tr F (SigTr.cell η) (F.map₂ η) ?_ ρ k hk
  have hl : ((model F).P ⟨a, b, f⟩).lift (fun _ => ((model F).Pctx (SigTr.cell η)).π 0) ≫
      ((model F).P ⟨a, b, f⟩).π 0 = ((model F).Pctx (SigTr.cell η)).π 0 := Product.lift_π _ _ 0
  exact (ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans (ConjEq.whiskerLeft_congr' hl _)

/-- In `M_F`, the transformation symbol of a composite `f ≫ g` (comparing `(f ≫ g)(x)` and
`g(f(x))`) at an environment `ρ` with `ρ 0 = k` is `ConjEq` to `k ◁ (F.mapComp f g).hom`. -/
lemma trAt_comp {x : K} {a b c : A} (f : a ⟶ b) (g : b ⟶ c)
    (ρ : ∀ i, x ⟶ (model F).obj ((sigOf A).trt (SigTr.comp f g) i)) (k : x ⟶ F.obj a)
    (hk : ρ 0 = k) : ConjEq ((model F).trAt (SigTr.comp f g) ρ) (k ◁ (F.mapComp f g).hom) :=
  trAt_of_tr F (SigTr.comp f g) _ (ConjEq.conj _ _ _) ρ k hk

/-- In `M_F`, the transformation symbol of an identity `𝟙 a` (comparing `id(x)` and `x`) at an
environment `ρ` with `ρ 0 = k` is `ConjEq` to `k ◁ (F.mapId a).hom`. -/
lemma trAt_unit {x : K} (a : A)
    (ρ : ∀ i, x ⟶ (model F).obj ((sigOf A).trt (SigTr.unit a) i)) (k : x ⟶ F.obj a)
    (hk : ρ 0 = k) : ConjEq ((model F).trAt (SigTr.unit a) ρ) (k ◁ (F.mapId a).hom) :=
  trAt_of_tr F (SigTr.unit a) _ (ConjEq.conj _ _ _) ρ k hk

/-- For components `app c : H c ⟶ H' c`, the induced 2-cell on the unary product, whiskered by
`M_G(f)`, is `ConjEq` to `π₀ ◁ (app a ▷ G f)`. -/
lemma prodApp_whisker (G : Pseudofunctor A K)
    {Hc H'c : ∀ c : A, (model F).obj c ⟶ (model G).obj c} (app : ∀ c, Hc c ⟶ H'c c)
    {a b : A} (f : a ⟶ b) :
    ConjEq (prodApp (M := (model F).toPreModel) (N := (model G).toPreModel) app ⟨a, b, f⟩ ▷
        (model G).fn ⟨a, b, f⟩)
      (((model F).P ⟨a, b, f⟩).π 0 ◁ (app a ▷ G.map f)) := by
  refine (ConjEq.whiskerRight_comp₁ _ _ _).trans
    ((ConjEq.whiskerRight ?_ (G.map f)).trans (ConjEq.whiskerLeft_whiskerRight _ _ _).symm)
  rw [prodApp_π]
  exact ConjEq.conj _ _ _

/-- In `M_F`, `M_F(f) ◁ β` is `ConjEq` to `π₀ ◁ (F f ◁ β)`. -/
lemma fn_whiskerLeft {a b : A} (f : a ⟶ b) {y : K} {u u' : F.obj b ⟶ y} (β : u ⟶ u') :
    ConjEq ((model F).fn ⟨a, b, f⟩ ◁ β) (((model F).P ⟨a, b, f⟩).π 0 ◁ (F.map f ◁ β)) :=
  ConjEq.whiskerLeft_comp₁ _ _ _

/-- A section of the projection out of a unary product. -/
lemma lift_id_π {a b : A} (f : a ⟶ b) :
    ((model F).P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ≫ ((model F).P ⟨a, b, f⟩).π 0 =
      𝟙 (F.obj a) :=
  Product.lift_π _ _ 0

end Model

variable (F G : Pseudofunctor A K)

/-! ### Lax morphisms `M_F → M_G` -/

section Lax

/-- The naturality 2-cell of lax data `L : M_F → M_G` at a 1-cell `f`, read off at the
identity environment. -/
def natOf (L : LaxData (model F).toPreModel (model G).toPreModel) {a b : A} (f : a ⟶ b) :
    L.cell a ≫ G.map f ⟶ F.map f ≫ L.cell b :=
  eqToHom ((congrArg (· ≫ G.map f) (Category.id_comp (L.cell a)).symm).trans
      ((congrArg (· ≫ G.map f) (Product.lift_π _ _ 0)).symm.trans (Category.assoc _ _ _))) ≫
    L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) ≫
    eqToHom ((congrArg (· ≫ L.cell b) (Category.assoc _ _ _).symm).trans
      (congrArg (· ≫ L.cell b) ((congrArg (· ≫ F.map f) (lift_id_π F f)).trans
        (Category.id_comp _))))

/-- `natOf F G L f` is `ConjEq` to the structure 2-cell `L.str f` whiskered by the section
`lift (id)` of the unary product. -/
lemma natOf_conj (L : LaxData (model F).toPreModel (model G).toPreModel) {a b : A} (f : a ⟶ b) :
    ConjEq (natOf F G L f)
      (((model F).P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ◁ L.str ⟨a, b, f⟩) :=
  (ConjEq.conj _ _ (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)))).trans (ConjEq.conj _ _ _)

/-- The structure 2-cell of lax data `L` at the symbol `f` and an environment `g` with `g 0 = k` is
`ConjEq` to `k ◁ natOf F G L f`. -/
lemma strAt_eq (L : LaxData (model F).toPreModel (model G).toPreModel) {x : K} {a b : A}
    (f : a ⟶ b) (g : ∀ _ : Fin 1, x ⟶ F.obj a) (k : x ⟶ F.obj a) (hk : g 0 = k) :
    ConjEq (L.strAt ⟨a, b, f⟩ g) (k ◁ natOf F G L f) := by
  subst hk
  have pre := L.strAt_precomp ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) (g 0)
  have cg := L.strAt_congr ⟨a, b, f⟩ (g := fun _ => g 0 ≫ 𝟙 (F.obj a)) (g' := g)
    (fun i => by simp only [Category.comp_id]; exact congrArg g (Fin.fin_one_eq_zero i).symm)
  have hn : ConjEq (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a))) (natOf F G L f) :=
    (ConjEq.conj _ _ _).symm
  exact (ConjEq.intro cg).trans ((ConjEq.intro pre).symm.trans (ConjEq.whiskerLeft (g 0) hn))

/-- The comparison 2-cell `eta` of lax data `L` on the unary term `f(x)` at the identity environment
is `ConjEq` to `natOf F G L f`. -/
lemma laxEta_app1 (L : LaxData (model F).toPreModel (model G).toPreModel) {a b : A}
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
lemma laxEta_app1_app1 (L : LaxData (model F).toPreModel (model G).toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    ConjEq (L.eta (fun _ : Fin 1 => 𝟙 (F.obj a))
        (app1 A g (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => a) (0 : Fin 1)))))
      ((natOf F G L f ▷ G.map g) ≫ eqToHom (Category.assoc _ _ _) ≫ (F.map f ◁ natOf F G L g)) := by
  rw [LaxData.eta_app]
  refine ConjEq.comp ((appCell_eq G g _).trans ((laxEta_app1 F G L f).whiskerRight (G.map g))) ?_
  exact (strAt_eq F G L g _ (F.map f) (by rw [interp_app1]; simp)).trans
    (ConjEq.eqToHom_comp (ConjEq.of_eq rfl) _).symm

/-- The transformation-symbol law of lax data `L` for a 2-cell `η : f ⟶ g` (at the identity
environment) is the naturality of `natOf` in `η`, the 2-cell axiom of a lax transformation. -/
lemma laxTrLaw_cell_iff (L : LaxData (model F).toPreModel (model G).toPreModel) {a b : A}
    {f g : a ⟶ b} (η : f ⟶ g) :
    L.TrLaw (SigTr.cell η) (idEnv F (SigTr.cell η)) ↔
      natOf F G L f ≫ (F.map₂ η ▷ L.cell b) = (L.cell a ◁ G.map₂ η) ≫ natOf F G L g :=
  (ConjEq.eq_iff
    ((trAt_cell G η
      (fun i => idEnv F (SigTr.cell η) i ≫ L.cell ((sigOf A).trt (SigTr.cell η) i))
      (L.cell a) (Category.id_comp _)).comp (laxEta_app1 F G L g))
    ((laxEta_app1 F G L f).comp
      (((trAt_cell F η (idEnv F (SigTr.cell η)) (𝟙 (F.obj a)) rfl).trans
        (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell b)))).trans eq_comm

/-- The transformation-symbol law of lax data `L` for a composite `f ≫ g` (at the identity
environment) is the composition axiom `naturality_comp` of a lax transformation for `natOf`. -/
lemma laxTrLaw_comp_iff (L : LaxData (model F).toPreModel (model G).toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    L.TrLaw (SigTr.comp f g) (idEnv F (SigTr.comp f g)) ↔
      L.cell a ◁ G.toLax.mapComp f g ≫ natOf F G L (f ≫ g) =
        (α_ _ _ _).inv ≫ natOf F G L f ▷ G.map g ≫ (α_ _ _ _).hom ≫
          F.map f ◁ natOf F G L g ≫ (α_ _ _ _).inv ≫ F.toLax.mapComp f g ▷ L.cell c := by
  obtain ⟨i, hi, hi'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerLeftIso (L.cell a)
    (G.mapComp f g)) (trAt_comp G f g
      (fun i => idEnv F (SigTr.comp f g) i ≫ L.cell ((sigOf A).trt (SigTr.comp f g) i))
      (L.cell a) (Category.id_comp _))
  obtain ⟨j, hj, hj'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerRightIso (F.mapComp f g)
    (L.cell c)) (((trAt_comp F f g (idEnv F (SigTr.comp f g)) (𝟙 _) rfl).trans
      (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell c))
  unfold LaxData.TrLaw
  rw [← hi, ← hj, iso_square_iff]
  refine ConjEq.eq_iff (hi'.comp (laxEta_app1 F G L (f ≫ g)))
    ((((laxEta_app1_app1 F G L f g).trans
      (ConjEq.self_comp_eqToHom _ (Category.assoc _ _ _).symm)).comp hj').trans ?_)
  refine ⟨Category.assoc _ _ _, rfl, ?_⟩
  simp [Bicategory.Strict.associator_eqToIso]

/-- The transformation-symbol law of lax data `L` for an identity `𝟙 a` (at the identity
environment) is the unit axiom `naturality_id` of a lax transformation for `natOf`. -/
lemma laxTrLaw_unit_iff (L : LaxData (model F).toPreModel (model G).toPreModel) (a : A) :
    L.TrLaw (SigTr.unit a) (idEnv F (SigTr.unit a)) ↔
      L.cell a ◁ G.toLax.mapId a ≫ natOf F G L (𝟙 a) =
        (ρ_ (L.cell a)).hom ≫ (λ_ (L.cell a)).inv ≫ F.toLax.mapId a ▷ L.cell a := by
  have h₁ : L.eta (idEnv F (SigTr.unit a)) ((sigOf A).trtgt (SigTr.unit a)) = 𝟙 _ :=
    L.eta_var _ 0
  obtain ⟨i, hi, hi'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerLeftIso (L.cell a)
    (G.mapId a)) (trAt_unit G a
      (fun i => idEnv F (SigTr.unit a) i ≫ L.cell ((sigOf A).trt (SigTr.unit a) i))
      (L.cell a) (Category.id_comp _))
  obtain ⟨j, hj, hj'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerRightIso (F.mapId a)
    (L.cell a)) (((trAt_unit F a (idEnv F (SigTr.unit a)) (𝟙 _) rfl).trans
      (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell a))
  unfold LaxData.TrLaw
  rw [← hi, ← hj, iso_square_iff]
  refine ConjEq.eq_iff (hi'.comp (laxEta_app1 F G L (𝟙 a))) ?_
  simp only [Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv]
  refine ((ConjEq.of_eq (congrArg (· ≫ j.inv) h₁)).trans (ConjEq.of_eq (Category.id_comp _))).trans
    (hj'.trans (ConjEq.eqToHom_comp (ConjEq.eqToHom_comp (ConjEq.of_eq rfl) _) _).symm)

/-- For lax data, the transformation-symbol law at the identity environment implies it at the
generic environment. -/
lemma laxTrLaw_generic_of_id (L : LaxData (model F).toPreModel (model G).toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ (idEnv F τ)) : L.TrLaw τ ((model F).Pctx τ).π :=
  (H.precomp (((model F).Pctx τ).π 0)).congr
    (fun i => by rw [Fin.fin_one_eq_zero i]; exact Category.comp_id _)

/-- For lax data, the transformation-symbol law at the generic environment implies it at the
identity environment. -/
lemma laxTrLaw_id_of_generic (L : LaxData (model F).toPreModel (model G).toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ ((model F).Pctx τ).π) : L.TrLaw τ (idEnv F τ) :=
  (H.precomp (((model F).Pctx τ).lift (idEnv F τ))).congr (fun i => Product.lift_π _ _ i)

variable {F G}

/-- The lax data of a lax transformation. -/
abbrev toLaxData (σ : Lax.LaxTrans F.toLax G.toLax) :
    LaxData (model F).toPreModel (model G).toPreModel where
  cell := σ.app
  str B := eqToHom ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.map B.2.2) (Product.lift_π _ _ 0)).trans (Category.assoc _ _ _))) ≫
    (((model F).P B).π 0 ◁ σ.naturality B.2.2) ≫ eqToHom (Category.assoc _ _ _).symm

/-- The structure 2-cell of `toLaxData σ` at `f` is `ConjEq` to `π₀ ◁ σ.naturality f`. -/
lemma toLaxData_str (σ : Lax.LaxTrans F.toLax G.toLax) {a b : A} (f : a ⟶ b) :
    ConjEq ((toLaxData σ).str ⟨a, b, f⟩) (((model F).P ⟨a, b, f⟩).π 0 ◁ σ.naturality f) :=
  ConjEq.conj _ _ _

variable (F G)

/-- The naturality 2-cells read off from `toLaxData σ` are those of the lax transformation `σ`. -/
lemma natOf_toLaxData (σ : Lax.LaxTrans F.toLax G.toLax) {a b : A} (f : a ⟶ b) :
    natOf F G (toLaxData σ) f = σ.naturality f :=
  ((natOf_conj F G (toLaxData σ) f).trans
    (((ConjEq.whiskerLeft _ (toLaxData_str σ f)).trans (ConjEq.whiskerLeft_comp₁ _ _ _).symm).trans
      ((ConjEq.whiskerLeft_congr' (lift_id_π F f) _).trans (ConjEq.id_whiskerLeft _)))).eq

/-- The structure 2-cell of lax data `L` at the symbol `f` is `ConjEq` to `π₀ ◁ natOf F G L f`. -/
lemma laxStr_eq (L : LaxData (model F).toPreModel (model G).toPreModel) {a b : A} (f : a ⟶ b) :
    ConjEq (L.str ⟨a, b, f⟩) (((model F).P ⟨a, b, f⟩).π 0 ◁ natOf F G L f) := by
  have hl : ((model F).P ⟨a, b, f⟩).lift ((model F).P ⟨a, b, f⟩).π = 𝟙 _ := by
    simpa using ((model F).P ⟨a, b, f⟩).lift_uniq (𝟙 _)
  have h1 : ConjEq (L.strAt ⟨a, b, f⟩ ((model F).P ⟨a, b, f⟩).π) (L.str ⟨a, b, f⟩) :=
    (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft_congr' hl _).trans (ConjEq.id_whiskerLeft _))
  exact h1.symm.trans
    (strAt_eq F G L f ((model F).P ⟨a, b, f⟩).π (((model F).P ⟨a, b, f⟩).π 0) rfl)

variable {F G}

/-- The lax morphism `M_F → M_G` of a lax transformation. -/
def toLaxMor (σ : Lax.LaxTrans F.toLax G.toLax) : LaxMor (model F) (model G) where
  toLaxData := toLaxData σ
  tr_compat τ := (LaxData.tr_compat_iff _ τ).mp (laxTrLaw_generic_of_id F G _ τ (by
    cases τ with
    | cell η =>
      refine (laxTrLaw_cell_iff F G _ η).mpr ?_
      simp only [natOf_toLaxData]
      exact σ.naturality_naturality η
    | comp f g =>
      refine (laxTrLaw_comp_iff F G _ f g).mpr ?_
      simp only [natOf_toLaxData]
      exact σ.naturality_comp f g
    | unit a =>
      refine (laxTrLaw_unit_iff F G _ a).mpr ?_
      simp only [natOf_toLaxData]
      exact σ.naturality_id a))

/-- The lax transformation of a lax morphism `M_F → M_G`. -/
def ofLaxMor (L : LaxMor (model F) (model G)) : Lax.LaxTrans F.toLax G.toLax where
  app := L.cell
  naturality f := natOf F G L.toLaxData f
  naturality_naturality η := (laxTrLaw_cell_iff F G _ η).mp
    (laxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  naturality_comp f g := (laxTrLaw_comp_iff F G _ f g).mp
    (laxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  naturality_id a := (laxTrLaw_unit_iff F G _ a).mp
    (laxTrLaw_id_of_generic F G _ _ (L.trLaw _))

omit [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K] in
/-- Extensionality for lax transformations: equal components and heterogeneously equal
naturality 2-cells. -/
lemma laxTrans_ext' {σ τ : Lax.LaxTrans F.toLax G.toLax} (ha : σ.app = τ.app)
    (hn : ∀ (a b : A) (f : a ⟶ b), HEq (σ.naturality f) (τ.naturality f)) : σ = τ := by
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

/-- **Example 3.12** ([forsman2026syntactic]): lax transformations are lax morphisms of models. -/
def laxEquiv : Lax.LaxTrans F.toLax G.toLax ≃ LaxMor (model F) (model G) where
  toFun σ := toLaxMor σ
  invFun L := ofLaxMor L
  left_inv σ := laxTrans_ext' rfl (fun _ _ f => heq_of_eq (natOf_toLaxData F G σ f))
  right_inv L := LaxMor.ext' rfl (by
    rintro ⟨a, b, f⟩
    refine ConjEq.heq ?_
    exact (ConjEq.conj _ _ _).trans (laxStr_eq F G L.toLaxData f).symm)

/-- For lax transformations `σ, τ` and components `app`, the 2-cell compatibility of `app` as a
2-cell of lax morphisms at `f` is the modification axiom
`(app a ▷ G f) ≫ τ.naturality f = σ.naturality f ≫ (F f ◁ app b)` (Example 3.12). -/
lemma laxStrCompat_iff (σ τ : Lax.LaxTrans F.toLax G.toLax) (app : ∀ c, σ.app c ⟶ τ.app c)
    {a b : A} (f : a ⟶ b) :
    ((prodApp (M := (model F).toPreModel) (N := (model G).toPreModel)
        (Hc := (toLaxData σ).cell) (H'c := (toLaxData τ).cell) app ⟨a, b, f⟩ ▷
          (model G).fn ⟨a, b, f⟩) ≫ (toLaxData τ).str ⟨a, b, f⟩ =
      (toLaxData σ).str ⟨a, b, f⟩ ≫ ((model F).fn ⟨a, b, f⟩ ◁ app b)) ↔
    ((app a ▷ G.map f) ≫ τ.naturality f = σ.naturality f ≫ (F.map f ◁ app b)) := by
  refine (ConjEq.eq_iff
    ((prodApp_whisker F G (Hc := (toLaxData σ).cell) (H'c := (toLaxData τ).cell) app f).comp
      (toLaxData_str τ f))
    ((toLaxData_str σ f).comp (fn_whiskerLeft F f (app b)))).trans ?_
  rw [← Bicategory.whiskerLeft_comp (((model F).P ⟨a, b, f⟩).π 0),
    ← Bicategory.whiskerLeft_comp (((model F).P ⟨a, b, f⟩).π 0)]
  exact ⟨fun h => whiskerLeft_cancel_of_section _ _ (lift_id_π F f) h, fun h => by rw [h]⟩

/-- Modifications are 2-cells of lax morphisms. -/
def laxModifEquiv (σ τ : Lax.LaxTrans F.toLax G.toLax) :
    Lax.LaxTrans.Modification σ τ ≃ LaxTwoCell (toLaxData σ) (toLaxData τ) where
  toFun Γ := ⟨Γ.app, fun B => (laxStrCompat_iff F G σ τ Γ.app B.2.2).mpr (Γ.naturality B.2.2)⟩
  invFun α := ⟨α.app, fun f => (laxStrCompat_iff F G σ τ α.app f).mp (α.str_compat ⟨_, _, f⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A lax transformation has invertible naturality 2-cells iff its lax morphism of models is
strong (Example 3.12 of [forsman2026syntactic]). -/
lemma laxIsIso_iff (σ : Lax.LaxTrans F.toLax G.toLax) :
    (∀ {a b : A} (f : a ⟶ b), IsIso (σ.naturality f)) ↔
      ∀ B, IsIso ((laxEquiv F G σ).str B) := by
  constructor
  · rintro h ⟨a, b, f⟩
    have := h f
    exact (toLaxData_str σ f).isIso_iff.mpr inferInstance
  · intro h a b f
    rw [← natOf_toLaxData F G σ f]
    have : IsIso ((toLaxData σ).str ⟨a, b, f⟩) := h ⟨a, b, f⟩
    exact (natOf_conj F G (toLaxData σ) f).isIso_iff.mpr inferInstance

/-- A lax transformation has identity naturality 2-cells (`eqToHom`s) iff the structure 2-cells of
its lax morphism of models are identities (Example 3.12 of [forsman2026syntactic]). -/
lemma laxIsStrict_iff (σ : Lax.LaxTrans F.toLax G.toLax) :
    (∀ {a b : A} (f : a ⟶ b), ∃ h, σ.naturality f = eqToHom h) ↔
      ∀ B, ∃ h, (laxEquiv F G σ).str B = eqToHom h := by
  constructor
  · rintro hs ⟨a, b, f⟩
    obtain ⟨h, hh⟩ := hs f
    exact (toLaxData_str σ f).exists_eqToHom_iff.mpr
      ⟨congrArg (fun z => ((model F).P ⟨a, b, f⟩).π 0 ≫ z) h,
        by rw [hh, Bicategory.whiskerLeft_eqToHom]⟩
  · intro H a b f
    obtain ⟨h, hh⟩ := H ⟨a, b, f⟩
    rw [← natOf_toLaxData F G σ f]
    exact (natOf_conj F G (laxEquiv F G σ).toLaxData f).exists_eqToHom_iff.mpr
      ⟨congrArg (fun z => ((model F).P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ≫ z) h,
        by rw [hh, Bicategory.whiskerLeft_eqToHom]⟩

end Lax

/-! ### Oplax morphisms `M_F → M_G` -/

section Oplax

/-- The naturality 2-cell of oplax data `L : M_F → M_G` at a 1-cell `f`, read off at the
identity environment. -/
def opNatOf (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b : A} (f : a ⟶ b) :
    F.map f ≫ L.cell b ⟶ L.cell a ≫ G.map f :=
  eqToHom ((congrArg (· ≫ L.cell b) ((congrArg (· ≫ F.map f) (lift_id_π F f)).trans
        (Category.id_comp _))).symm.trans
      (congrArg (· ≫ L.cell b) (Category.assoc _ _ _))) ≫
    L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) ≫
    eqToHom ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.map f) (Product.lift_π _ _ 0)).trans
        (congrArg (· ≫ G.map f) (Category.id_comp (L.cell a)))))

/-- `opNatOf F G L f` is `ConjEq` to the structure 2-cell `L.str f` whiskered by the section
`lift (id)` of the unary product. -/
lemma opNatOf_conj (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b : A}
    (f : a ⟶ b) :
    ConjEq (opNatOf F G L f)
      (((model F).P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ◁ L.str ⟨a, b, f⟩) :=
  (ConjEq.conj _ _ (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)))).trans (ConjEq.conj _ _ _)

/-- The structure 2-cell of oplax data `L` at the symbol `f` and an environment `g` with `g 0 = k`
is `ConjEq` to `k ◁ opNatOf F G L f`. -/
lemma opStrAt_eq (L : OplaxData (model F).toPreModel (model G).toPreModel) {x : K} {a b : A}
    (f : a ⟶ b) (g : ∀ _ : Fin 1, x ⟶ F.obj a) (k : x ⟶ F.obj a) (hk : g 0 = k) :
    ConjEq (L.strAt ⟨a, b, f⟩ g) (k ◁ opNatOf F G L f) := by
  subst hk
  have pre := L.strAt_precomp ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a)) (g 0)
  have cg := L.strAt_congr ⟨a, b, f⟩ (g := fun _ => g 0 ≫ 𝟙 (F.obj a)) (g' := g)
    (fun i => by simp only [Category.comp_id]; exact congrArg g (Fin.fin_one_eq_zero i).symm)
  have hn : ConjEq (L.strAt ⟨a, b, f⟩ (fun _ => 𝟙 (F.obj a))) (opNatOf F G L f) :=
    (ConjEq.conj _ _ _).symm
  exact (ConjEq.intro cg).trans ((ConjEq.intro pre).symm.trans (ConjEq.whiskerLeft (g 0) hn))

/-- The comparison 2-cell `eta` of oplax data `L` on the unary term `f(x)` at the identity
environment is `ConjEq` to `opNatOf F G L f`. -/
lemma oplaxEta_app1 (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b : A}
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
lemma oplaxEta_app1_app1 (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    ConjEq (L.eta (fun _ : Fin 1 => 𝟙 (F.obj a))
        (app1 A g (app1 A f (Trm.var (S := funSigOf A) (vty := fun _ : Fin 1 => a) (0 : Fin 1)))))
      ((F.map f ◁ opNatOf F G L g) ≫ eqToHom (Category.assoc _ _ _).symm ≫
        (opNatOf F G L f ▷ G.map g)) := by
  rw [OplaxData.eta_app]
  refine ConjEq.comp (opStrAt_eq F G L g _ (F.map f) (by rw [interp_app1]; simp)) ?_
  exact ((appCell_eq G g _).trans ((oplaxEta_app1 F G L f).whiskerRight (G.map g))).trans
    (ConjEq.eqToHom_comp (ConjEq.of_eq rfl) _).symm

/-- The transformation-symbol law of oplax data `L` for a 2-cell `η : f ⟶ g` (at the identity
environment) is the 2-cell axiom of an oplax transformation for `opNatOf`. -/
lemma oplaxTrLaw_cell_iff (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b : A}
    {f g : a ⟶ b} (η : f ⟶ g) :
    L.TrLaw (SigTr.cell η) (idEnv F (SigTr.cell η)) ↔
      (F.map₂ η ▷ L.cell b) ≫ opNatOf F G L g = opNatOf F G L f ≫ (L.cell a ◁ G.map₂ η) :=
  ConjEq.eq_iff
    ((((trAt_cell F η (idEnv F (SigTr.cell η)) (𝟙 (F.obj a)) rfl).trans
        (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell b)).comp (oplaxEta_app1 F G L g))
    ((oplaxEta_app1 F G L f).comp
      (trAt_cell G η
        (fun i => idEnv F (SigTr.cell η) i ≫ L.cell ((sigOf A).trt (SigTr.cell η) i))
        (L.cell a) (Category.id_comp _)))

/-- The transformation-symbol law of oplax data `L` for a composite `f ≫ g` (at the identity
environment) is the composition axiom `naturality_comp` of an oplax transformation for
`opNatOf`. -/
lemma oplaxTrLaw_comp_iff (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b c : A}
    (f : a ⟶ b) (g : b ⟶ c) :
    L.TrLaw (SigTr.comp f g) (idEnv F (SigTr.comp f g)) ↔
      F.toLax.mapComp f g ▷ L.cell c ≫ opNatOf F G L (f ≫ g) =
        (α_ _ _ _).hom ≫ F.map f ◁ opNatOf F G L g ≫ (α_ _ _ _).inv ≫
          opNatOf F G L f ▷ G.map g ≫ (α_ _ _ _).hom ≫ L.cell a ◁ G.toLax.mapComp f g := by
  obtain ⟨i, hi, hi'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerRightIso (F.mapComp f g)
    (L.cell c)) (((trAt_comp F f g (idEnv F (SigTr.comp f g)) (𝟙 _) rfl).trans
      (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell c))
  obtain ⟨j, hj, hj'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerLeftIso (L.cell a)
    (G.mapComp f g)) (trAt_comp G f g
      (fun i => idEnv F (SigTr.comp f g) i ≫ L.cell ((sigOf A).trt (SigTr.comp f g) i))
      (L.cell a) (Category.id_comp _))
  unfold OplaxData.TrLaw
  rw [← hi, ← hj, iso_square_iff]
  refine ConjEq.eq_iff (hi'.comp (oplaxEta_app1 F G L (f ≫ g)))
    ((((oplaxEta_app1_app1 F G L f g).trans
      (ConjEq.self_comp_eqToHom _ (Category.assoc _ _ _))).comp hj').trans ?_)
  refine ⟨(Category.assoc _ _ _).symm, rfl, ?_⟩
  simp [Bicategory.Strict.associator_eqToIso]

/-- The transformation-symbol law of oplax data `L` for an identity `𝟙 a` (at the identity
environment) is the unit axiom `naturality_id` of an oplax transformation for `opNatOf`. -/
lemma oplaxTrLaw_unit_iff (L : OplaxData (model F).toPreModel (model G).toPreModel) (a : A) :
    L.TrLaw (SigTr.unit a) (idEnv F (SigTr.unit a)) ↔
      F.toLax.mapId a ▷ L.cell a ≫ opNatOf F G L (𝟙 a) =
        (λ_ (L.cell a)).hom ≫ (ρ_ (L.cell a)).inv ≫ L.cell a ◁ G.toLax.mapId a := by
  have h₁ : L.eta (idEnv F (SigTr.unit a)) ((sigOf A).trtgt (SigTr.unit a)) = 𝟙 _ :=
    L.eta_var _ 0
  obtain ⟨i, hi, hi'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerRightIso (F.mapId a)
    (L.cell a)) (((trAt_unit F a (idEnv F (SigTr.unit a)) (𝟙 _) rfl).trans
      (ConjEq.id_whiskerLeft _)).whiskerRight (L.cell a))
  obtain ⟨j, hj, hj'⟩ := ConjEq.exists_iso (e := Bicategory.whiskerLeftIso (L.cell a)
    (G.mapId a)) (trAt_unit G a
      (fun i => idEnv F (SigTr.unit a) i ≫ L.cell ((sigOf A).trt (SigTr.unit a) i))
      (L.cell a) (Category.id_comp _))
  unfold OplaxData.TrLaw
  rw [← hi, ← hj, iso_square_iff]
  refine ConjEq.eq_iff (hi'.comp (oplaxEta_app1 F G L (𝟙 a))) ?_
  simp only [Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso,
    eqToIso.hom, eqToIso.inv]
  refine ((ConjEq.of_eq (congrArg (· ≫ j.inv) h₁)).trans (ConjEq.of_eq (Category.id_comp _))).trans
    (hj'.trans (ConjEq.eqToHom_comp (ConjEq.eqToHom_comp (ConjEq.of_eq rfl) _) _).symm)

/-- For oplax data, the transformation-symbol law at the identity environment implies it at the
generic environment. -/
lemma oplaxTrLaw_generic_of_id (L : OplaxData (model F).toPreModel (model G).toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ (idEnv F τ)) : L.TrLaw τ ((model F).Pctx τ).π :=
  (H.precomp (((model F).Pctx τ).π 0)).congr
    (fun i => by rw [Fin.fin_one_eq_zero i]; exact Category.comp_id _)

/-- For oplax data, the transformation-symbol law at the generic environment implies it at the
identity environment. -/
lemma oplaxTrLaw_id_of_generic (L : OplaxData (model F).toPreModel (model G).toPreModel)
    (τ : SigTr A) (H : L.TrLaw τ ((model F).Pctx τ).π) : L.TrLaw τ (idEnv F τ) :=
  (H.precomp (((model F).Pctx τ).lift (idEnv F τ))).congr (fun i => Product.lift_π _ _ i)

variable {F G}

/-- The oplax data of an oplax transformation. -/
abbrev toOplaxData (σ : Lax.OplaxTrans F.toLax G.toLax) :
    OplaxData (model F).toPreModel (model G).toPreModel where
  cell := σ.app
  str B := eqToHom (Category.assoc _ _ _) ≫ (((model F).P B).π 0 ◁ σ.naturality B.2.2) ≫
    eqToHom ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.map B.2.2) (Product.lift_π _ _ 0)).symm.trans (Category.assoc _ _ _)))

/-- The structure 2-cell of `toOplaxData σ` at `f` is `ConjEq` to `π₀ ◁ σ.naturality f`. -/
lemma toOplaxData_str (σ : Lax.OplaxTrans F.toLax G.toLax) {a b : A} (f : a ⟶ b) :
    ConjEq ((toOplaxData σ).str ⟨a, b, f⟩) (((model F).P ⟨a, b, f⟩).π 0 ◁ σ.naturality f) :=
  ConjEq.conj _ _ _

variable (F G)

/-- The naturality 2-cells read off from `toOplaxData σ` are those of the oplax transformation
`σ`. -/
lemma opNatOf_toOplaxData (σ : Lax.OplaxTrans F.toLax G.toLax) {a b : A} (f : a ⟶ b) :
    opNatOf F G (toOplaxData σ) f = σ.naturality f :=
  ((opNatOf_conj F G (toOplaxData σ) f).trans
    (((ConjEq.whiskerLeft _ (toOplaxData_str σ f)).trans
      (ConjEq.whiskerLeft_comp₁ _ _ _).symm).trans
      ((ConjEq.whiskerLeft_congr' (lift_id_π F f) _).trans (ConjEq.id_whiskerLeft _)))).eq

/-- The structure 2-cell of oplax data `L` at the symbol `f` is `ConjEq` to
`π₀ ◁ opNatOf F G L f`. -/
lemma oplaxStr_eq (L : OplaxData (model F).toPreModel (model G).toPreModel) {a b : A}
    (f : a ⟶ b) :
    ConjEq (L.str ⟨a, b, f⟩) (((model F).P ⟨a, b, f⟩).π 0 ◁ opNatOf F G L f) := by
  have hl : ((model F).P ⟨a, b, f⟩).lift ((model F).P ⟨a, b, f⟩).π = 𝟙 _ := by
    simpa using ((model F).P ⟨a, b, f⟩).lift_uniq (𝟙 _)
  have h1 : ConjEq (L.strAt ⟨a, b, f⟩ ((model F).P ⟨a, b, f⟩).π) (L.str ⟨a, b, f⟩) :=
    (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft_congr' hl _).trans (ConjEq.id_whiskerLeft _))
  exact h1.symm.trans
    (opStrAt_eq F G L f ((model F).P ⟨a, b, f⟩).π (((model F).P ⟨a, b, f⟩).π 0) rfl)

variable {F G}

/-- The oplax morphism `M_F → M_G` of an oplax transformation. -/
def toOplaxMor (σ : Lax.OplaxTrans F.toLax G.toLax) : OplaxMor (model F) (model G) where
  toOplaxData := toOplaxData σ
  tr_compat τ := (OplaxData.tr_compat_iff _ τ).mp (oplaxTrLaw_generic_of_id F G _ τ (by
    cases τ with
    | cell η =>
      refine (oplaxTrLaw_cell_iff F G _ η).mpr ?_
      simp only [opNatOf_toOplaxData]
      exact σ.naturality_naturality η
    | comp f g =>
      refine (oplaxTrLaw_comp_iff F G _ f g).mpr ?_
      simp only [opNatOf_toOplaxData]
      exact σ.naturality_comp f g
    | unit a =>
      refine (oplaxTrLaw_unit_iff F G _ a).mpr ?_
      simp only [opNatOf_toOplaxData]
      exact σ.naturality_id a))

/-- The oplax transformation of an oplax morphism `M_F → M_G`. -/
def ofOplaxMor (L : OplaxMor (model F) (model G)) : Lax.OplaxTrans F.toLax G.toLax where
  app := L.cell
  naturality f := opNatOf F G L.toOplaxData f
  naturality_naturality η := (oplaxTrLaw_cell_iff F G _ η).mp
    (oplaxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  naturality_comp f g := (oplaxTrLaw_comp_iff F G _ f g).mp
    (oplaxTrLaw_id_of_generic F G _ _ (L.trLaw _))
  naturality_id a := (oplaxTrLaw_unit_iff F G _ a).mp
    (oplaxTrLaw_id_of_generic F G _ _ (L.trLaw _))

omit [Bicategory.Strict K] [HasChosenFinProducts.{u, v, w} K] in
/-- Extensionality for oplax transformations: equal components and heterogeneously equal
naturality 2-cells. -/
lemma oplaxTrans_ext' {σ τ : Lax.OplaxTrans F.toLax G.toLax} (ha : σ.app = τ.app)
    (hn : ∀ (a b : A) (f : a ⟶ b), HEq (σ.naturality f) (τ.naturality f)) : σ = τ := by
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

/-- **Example 3.12** ([forsman2026syntactic]): oplax transformations are oplax morphisms of
models. -/
def oplaxEquiv : Lax.OplaxTrans F.toLax G.toLax ≃ OplaxMor (model F) (model G) where
  toFun σ := toOplaxMor σ
  invFun L := ofOplaxMor L
  left_inv σ := oplaxTrans_ext' rfl (fun _ _ f => heq_of_eq (opNatOf_toOplaxData F G σ f))
  right_inv L := OplaxMor.ext' rfl (by
    rintro ⟨a, b, f⟩
    refine ConjEq.heq ?_
    exact (ConjEq.conj _ _ _).trans (oplaxStr_eq F G L.toOplaxData f).symm)

/-- For oplax transformations `σ, τ` and components `app`, the 2-cell compatibility of `app` as a
2-cell of oplax morphisms at `f` is the modification axiom
`(F f ◁ app b) ≫ τ.naturality f = σ.naturality f ≫ (app a ▷ G f)` (Example 3.12). -/
lemma oplaxStrCompat_iff (σ τ : Lax.OplaxTrans F.toLax G.toLax) (app : ∀ c, σ.app c ⟶ τ.app c)
    {a b : A} (f : a ⟶ b) :
    (((model F).fn ⟨a, b, f⟩ ◁ app b) ≫ (toOplaxData τ).str ⟨a, b, f⟩ =
      (toOplaxData σ).str ⟨a, b, f⟩ ≫ (prodApp (M := (model F).toPreModel)
        (N := (model G).toPreModel) (Hc := (toOplaxData σ).cell) (H'c := (toOplaxData τ).cell)
        app ⟨a, b, f⟩ ▷ (model G).fn ⟨a, b, f⟩)) ↔
    ((F.map f ◁ app b) ≫ τ.naturality f = σ.naturality f ≫ (app a ▷ G.map f)) := by
  refine (ConjEq.eq_iff ((fn_whiskerLeft F f (app b)).comp (toOplaxData_str τ f))
    ((toOplaxData_str σ f).comp
      (prodApp_whisker F G (Hc := (toOplaxData σ).cell) (H'c := (toOplaxData τ).cell) app
        f))).trans ?_
  rw [← Bicategory.whiskerLeft_comp (((model F).P ⟨a, b, f⟩).π 0),
    ← Bicategory.whiskerLeft_comp (((model F).P ⟨a, b, f⟩).π 0)]
  exact ⟨fun h => whiskerLeft_cancel_of_section _ _ (lift_id_π F f) h, fun h => by rw [h]⟩

/-- Modifications are 2-cells of oplax morphisms. -/
def oplaxModifEquiv (σ τ : Lax.OplaxTrans F.toLax G.toLax) :
    Lax.OplaxTrans.Modification σ τ ≃ OplaxTwoCell (toOplaxData σ) (toOplaxData τ) where
  toFun Γ := ⟨Γ.app, fun B =>
    (oplaxStrCompat_iff F G σ τ Γ.app B.2.2).mpr (Γ.naturality B.2.2)⟩
  invFun α := ⟨α.app, fun f =>
    (oplaxStrCompat_iff F G σ τ α.app f).mp (α.str_compat ⟨_, _, f⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An oplax transformation has invertible naturality 2-cells iff its oplax morphism of models is
strong (Example 3.12 of [forsman2026syntactic]). -/
lemma oplaxIsIso_iff (σ : Lax.OplaxTrans F.toLax G.toLax) :
    (∀ {a b : A} (f : a ⟶ b), IsIso (σ.naturality f)) ↔
      ∀ B, IsIso ((oplaxEquiv F G σ).str B) := by
  constructor
  · rintro h ⟨a, b, f⟩
    have := h f
    exact (toOplaxData_str σ f).isIso_iff.mpr inferInstance
  · intro h a b f
    rw [← opNatOf_toOplaxData F G σ f]
    have : IsIso ((toOplaxData σ).str ⟨a, b, f⟩) := h ⟨a, b, f⟩
    exact (opNatOf_conj F G (toOplaxData σ) f).isIso_iff.mpr inferInstance

/-- An oplax transformation has identity naturality 2-cells (`eqToHom`s) iff the structure 2-cells
of its oplax morphism of models are identities (Example 3.12 of [forsman2026syntactic]). -/
lemma oplaxIsStrict_iff (σ : Lax.OplaxTrans F.toLax G.toLax) :
    (∀ {a b : A} (f : a ⟶ b), ∃ h, σ.naturality f = eqToHom h) ↔
      ∀ B, ∃ h, (oplaxEquiv F G σ).str B = eqToHom h := by
  constructor
  · rintro hs ⟨a, b, f⟩
    obtain ⟨h, hh⟩ := hs f
    exact (toOplaxData_str σ f).exists_eqToHom_iff.mpr
      ⟨congrArg (fun z => ((model F).P ⟨a, b, f⟩).π 0 ≫ z) h,
        by rw [hh, Bicategory.whiskerLeft_eqToHom]⟩
  · intro H a b f
    obtain ⟨h, hh⟩ := H ⟨a, b, f⟩
    rw [← opNatOf_toOplaxData F G σ f]
    exact (opNatOf_conj F G (oplaxEquiv F G σ).toOplaxData f).exists_eqToHom_iff.mpr
      ⟨congrArg (fun z => ((model F).P ⟨a, b, f⟩).lift (fun _ => 𝟙 (F.obj a)) ≫ z) h,
        by rw [hh, Bicategory.whiskerLeft_eqToHom]⟩

end Oplax

end Paper.PsFun

end UlmerBialgebras
