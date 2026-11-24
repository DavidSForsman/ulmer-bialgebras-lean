module

public import UlmerBialgebras.Paper.Sec5DefsDoctrinal
public import UlmerBialgebras.Proofs.Sec5.MateNat

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Doctrinal adjunction for Σ-models (proofs)

Helpers for `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean`.

* `idData_eta`, `idData_tr_compat`: the comparison 2-cells of the identity data are `eqToHom`s,
  so the identity data is a lax morphism.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Proposition 3.11
-/

universe u v w z

namespace UlmerBialgebras.Paper.Doctrinal

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj]
variable {Sg : TwoSig}

/-! ## Heterogeneous equality of 2-cells -/

section HEqTools

variable {a b c : Obj}

/-- Right whiskering preserves heterogeneous equality of 2-cells whose sources and targets are
equal. -/
lemma heq_whiskerRight {f g f' g' : a ⟶ b} (hf : f = f') (hg : g = g') {α : f ⟶ g}
    {α' : f' ⟶ g'} (h : HEq α α') (k : b ⟶ c) : HEq (α ▷ k) (α' ▷ k) := by
  subst hf hg; cases h; rfl

/-- Left whiskering preserves heterogeneous equality of 2-cells whose sources and targets are equal.
-/
lemma heq_whiskerLeft (k : c ⟶ a) {f g f' g' : a ⟶ b} (hf : f = f') (hg : g = g')
    {α : f ⟶ g} {α' : f' ⟶ g'} (h : HEq α α') : HEq (k ◁ α) (k ◁ α') := by
  subst hf hg; cases h; rfl

/-- Right whiskering a 2-cell by equal 1-cells gives heterogeneously equal 2-cells. -/
lemma heq_whiskerRight_obj {f g : a ⟶ b} (α : f ⟶ g) {k k' : b ⟶ c} (e : k = k') :
    HEq (α ▷ k) (α ▷ k') := by
  subst e; rfl

/-- Left whiskering a 2-cell by equal 1-cells gives heterogeneously equal 2-cells. -/
lemma heq_whiskerLeft_obj {k k' : c ⟶ a} (e : k = k') {f g : a ⟶ b} (α : f ⟶ g) :
    HEq (k ◁ α) (k' ◁ α) := by
  subst e; rfl

/-- Two `eqToHom` morphisms with equal sources are heterogeneously equal. -/
lemma heq_eqToHom_eqToHom {C : Type*} [Category C] {X Y X' Y' : C} (p : X = Y) (q : X' = Y')
    (h : X = X') : HEq (eqToHom p) (eqToHom q) := by
  subst h p; subst q; rfl

/-- Pre- and postcomposing a morphism with `eqToHom`s gives a morphism heterogeneously equal to it.
-/
lemma eqToHom_comp_comp_eqToHom_heq {C : Type*} [Category C] {X Y X' Y' : C} (p : X = X')
    (q : Y' = Y) (x : X' ⟶ Y') : HEq (eqToHom p ≫ x ≫ eqToHom q) x := by
  subst p q; simp

variable {d : Obj}

/-- In a strict bicategory, whiskering by a composite `h ≫ k` is heterogeneously equal to whiskering
by `h` and then by `k`. -/
lemma whiskerR_comp₁ [Bicategory.Strict Obj] {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) (k : c ⟶ d) :
    HEq (η ▷ (h ≫ k)) ((η ▷ h) ▷ k) := by
  rw [Bicategory.Strict.whiskerRight_comp]; exact eqToHom_comp_comp_eqToHom_heq _ _ _

/-- In a strict bicategory, left whiskering by a composite `f ≫ g` is heterogeneously equal to left
whiskering by `g` and then by `f`. -/
lemma whiskerL_comp₁ [Bicategory.Strict Obj] (f : a ⟶ b) (g : b ⟶ c) {h k : c ⟶ d} (η : h ⟶ k) :
    HEq ((f ≫ g) ◁ η) (f ◁ g ◁ η) := by
  rw [Bicategory.Strict.comp_whiskerLeft]; exact eqToHom_comp_comp_eqToHom_heq _ _ _

/-- In a strict bicategory, `f ◁ (η ▷ k)` is heterogeneously equal to `(f ◁ η) ▷ k`. -/
lemma whisker_mid [Bicategory.Strict Obj] (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) (k : c ⟶ d) :
    HEq (f ◁ (η ▷ k)) ((f ◁ η) ▷ k) := by
  rw [Bicategory.Strict.whisker_assoc]; exact eqToHom_comp_comp_eqToHom_heq _ _ _

/-- Heterogeneously equal morphisms `x` and `y` with the same source satisfy `x = y ≫ eqToHom h`. -/
lemma eq_comp_eqToHom_of_heq {C : Type*} [Category C] {X Y Y' : C} (x : X ⟶ Y) (y : X ⟶ Y')
    (h : Y' = Y) (hxy : HEq x y) : x = y ≫ eqToHom h := by
  subst h; simpa using eq_of_heq hxy

/-- Two mutually inverse `eqToHom`s in the middle of a composite cancel:
`(m ≫ eqToHom p) ≫ (eqToHom q ≫ k) = m ≫ k`. -/
lemma comp_eqToHom_eqToHom_comp {C : Type*} [Category C] {W X Y Z : C} (m : W ⟶ X) (p : X = Y)
    (q : Y = X) (k : X ⟶ Z) : (m ≫ eqToHom p) ≫ (eqToHom q ≫ k) = m ≫ k := by
  subst p; simp

/-- Postcomposition with an `eqToHom` is cancellable. -/
lemma comp_eqToHom_cancel {C : Type*} [Category C] {X Y Z : C} (p : Y = Z) {u v : X ⟶ Y}
    (h : u ≫ eqToHom p = v ≫ eqToHom p) : u = v := by
  subst p; simpa using h

/-- An `eqToHom` is heterogeneously equal to the identity on its source. -/
lemma eqToHom_heq_id {C : Type*} [Category C] {X Y : C} (p : X = Y) : HEq (eqToHom p) (𝟙 X) := by
  subst p; rfl

/-- The lift into a product followed by the `i`-th projection and a 1-cell `h` is the `i`-th
component followed by `h`. -/
lemma lift_π_assoc [Bicategory.Strict Obj] {ι : Type*} {cs : ι → Obj}
    (P : Product cs) {x : Obj} (g : ∀ i, x ⟶ cs i)
    (i : ι) (h : cs i ⟶ c) : P.lift g ≫ (P.π i ≫ h) = g i ≫ h := by
  rw [← Category.assoc, P.lift_π]

/-- 2-cells into a product with heterogeneously equal components are heterogeneously equal. -/
lemma heq_of_proj {ι : Type*} {cs : ι → Obj} (P : Product cs) {X : Obj} {x x' y y' : X ⟶ P.pt}
    (ex : x = x') (ey : y = y') (α : x ⟶ y) (β : x' ⟶ y')
    (h : ∀ i, HEq (α ▷ P.π i) (β ▷ P.π i)) : HEq α β := by
  subst ex ey
  exact heq_of_eq (P.cell_ext fun i => eq_of_heq (h i))

end HEqTools

variable [Bicategory.Strict Obj] [HasChosenFinProducts.{u, v, w} Obj]

/-! ## The identity lax morphism -/

/-- The comparison 2-cells of the identity data are `eqToHom`s. -/
lemma idData_eta (M : PreModel Sg Obj) {V : Type} {vty : V → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (vty v)) :
    ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c), ∃ h, (LaxData.idData M).eta ρ t = eqToHom h := by
  intro c t
  induction t with
  | var v => exact ⟨rfl, by simp⟩
  | app B args ih =>
    choose hs ehs using ih
    refine ⟨?_, ?_⟩
    · simp only [LaxData.idData, Category.comp_id]
    · rw [LaxData.eta_app, M.appCell_congr B ehs, M.appCell_eqToHom, LaxData.strAt]
      simp only [LaxData.idData, Bicategory.whiskerLeft_eqToHom]
      exact (eqToHom_trans_assoc _ _ _).trans
        ((eqToHom_trans_assoc _ _ _).trans (eqToHom_trans _ _))

/-- The identity data satisfies the compatibility with the transformation symbols. -/
lemma idData_tr_compat (M : Model Sg Obj) (a : Sg.Tr) :
    (M.trAt a (fun i => (M.Pctx a).π i ≫ (LaxData.idData M.toPreModel).cell (Sg.trt a i))) ≫
        (LaxData.idData M.toPreModel).eta (M.Pctx a).π (Sg.trtgt a)
      = (LaxData.idData M.toPreModel).eta (M.Pctx a).π (Sg.trsrc a) ≫
        (M.tr a ▷ (LaxData.idData M.toPreModel).cell (Sg.trty a)) := by
  obtain ⟨h₁, e₁⟩ := idData_eta M.toPreModel (M.Pctx a).π (Sg.trtgt a)
  obtain ⟨h₂, e₂⟩ := idData_eta M.toPreModel (M.Pctx a).π (Sg.trsrc a)
  have hl : (M.Pctx a).lift (M.Pctx a).π = 𝟙 _ := by
    have := (M.Pctx a).lift_uniq (𝟙 _)
    simpa using this
  rw [e₁, e₂]
  change (M.trAt a (fun i => (M.Pctx a).π i ≫ 𝟙 _)) ≫ eqToHom h₁ =
    eqToHom h₂ ≫ (M.tr a ▷ 𝟙 _)
  rw [M.trAt_congr a (ρ := (M.Pctx a).π) (fun i => (Category.comp_id _).symm), Model.trAt,
    Bicategory.whiskerLeft_congr' hl, Bicategory.Strict.id_whiskerLeft,
    Bicategory.Strict.whiskerRight_id]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (_ ≫= M.tr a ≫= eqToHom_trans _ _).trans
    ((eqToHom_trans_assoc _ _ _).symm)

/-! ## The product adjunction -/

/-- Equalities of composites of 1-cells through product projections. -/
local macro "obj_eq" : tactic =>
  `(tactic| simp only [Category.id_comp, Category.comp_id, Category.assoc, lift_π_assoc,
    Product.lift_π])

section PiAdj

omit [HasChosenFinProducts Obj]

variable {ι : Type*} {a b : ι → Obj} (P : Product a) (Q : Product b) {f : ∀ i, b i ⟶ a i}
  {g : ∀ i, a i ⟶ b i} (A : ∀ i, TwoAdj (f i) (g i))

/-- The 1-cell `F : Q → P` between products induced by a family `f_i : b_i → a_i`. -/
abbrev piL (f : ∀ i, b i ⟶ a i) : Q.pt ⟶ P.pt := P.lift (fun i => Q.π i ≫ f i)

/-- The 1-cell `G : P → Q` between products induced by a family `g_i : a_i → b_i`. -/
abbrev piR (g : ∀ i, a i ⟶ b i) : P.pt ⟶ Q.pt := Q.lift (fun i => P.π i ≫ g i)

/-- The composite `piL ≫ piR` followed by the `i`-th projection of `Q` is the `i`-th projection
followed by `f i ≫ g i`. -/
lemma piL_piR_π (i : ι) : (piL P Q f ≫ piR P Q g) ≫ Q.π i = Q.π i ≫ (f i ≫ g i) := by
  rw [Category.assoc, Q.lift_π, ← Category.assoc, P.lift_π, Category.assoc]

/-- The unit of the product adjunction. -/
def piUnit : 𝟙 Q.pt ⟶ piL P Q f ≫ piR P Q g :=
  Q.lift₂ (fun i => eqToHom (Category.id_comp _) ≫ eqToHom (Category.comp_id _).symm ≫
    (Q.π i ◁ (A i).unit') ≫ eqToHom (piL_piR_π P Q i).symm)

/-- The composite `piR ≫ piL` followed by the `i`-th projection of `P` is the `i`-th projection
followed by `g i ≫ f i`. -/
lemma piR_piL_π (i : ι) :
    (piR P Q g ≫ piL P Q f) ≫ P.π i = P.π i ≫ (g i ≫ f i) := by
  rw [Category.assoc, P.lift_π, ← Category.assoc, Q.lift_π, Category.assoc]

/-- The counit `G_c̄ ∘ F_c̄ ⇒ 1` of the product adjunction. -/
def piCounit : piR P Q g ≫ piL P Q f ⟶ 𝟙 P.pt :=
  P.lift₂ (fun i => eqToHom (piR_piL_π P Q i) ≫
    (P.π i ◁ (A i).counit') ≫ eqToHom (Category.comp_id _) ≫
      eqToHom (Category.id_comp _).symm)

/-- The `i`-th component of the unit `piUnit` of the product adjunction is the unit of the `i`-th
adjunction, up to heterogeneous equality. -/
lemma piUnit_π (i : ι) :
    HEq (piUnit P Q A ▷ Q.π i) (Q.π i ◁ (A i).unit') := by
  rw [piUnit, Q.lift₂_π]
  simp

/-- The `i`-th component of the counit `piCounit` of the product adjunction is the counit of the
`i`-th adjunction, up to heterogeneous equality. -/
lemma piCounit_π (i : ι) :
    HEq (piCounit P Q A ▷ P.π i) (P.π i ◁ (A i).counit') := by
  rw [piCounit, P.lift₂_π]
  simp

/-- The left triangle identity for the unit `piUnit` and counit `piCounit` of the product
adjunction. -/
lemma pi_left_triangle :
    (piUnit P Q A ▷ piL P Q f) ≫ eqToHom (Category.assoc _ _ _) ≫ (piL P Q f ◁ piCounit P Q A) =
      eqToHom (Category.id_comp _) ≫ eqToHom (Category.comp_id _).symm := by
  -- Componentwise, the triangle is that of the `i`-th adjunction, up to `HEq` of whiskerings.
  refine P.cell_ext fun i => ?_
  have hz := (A i).left_triangle'
  have t₁ : HEq ((piUnit P Q A ▷ piL P Q f) ▷ P.π i)
      (Q.π i ◁ ((A i).unit' ▷ f i)) :=
    (whiskerR_comp₁ _ _ _).symm.trans <|
      (heq_whiskerRight_obj _ (P.lift_π _ i)).trans <|
      (whiskerR_comp₁ _ _ _).trans <|
      (heq_whiskerRight (by simp) (piL_piR_π P Q i) (piUnit_π P Q A i) (f i)).trans
      (whisker_mid _ _ _).symm
  have t₃ : HEq ((piL P Q f ◁ piCounit P Q A) ▷ P.π i)
      (Q.π i ◁ (f i ◁ (A i).counit')) :=
    (whisker_mid _ _ _).symm.trans <|
      (heq_whiskerLeft _ (piR_piL_π P Q i) (by simp) (piCounit_π P Q A i)).trans <|
      (whiskerL_comp₁ _ _ _).symm.trans <|
      (heq_whiskerLeft_obj (P.lift_π _ i) _).trans
      (whiskerL_comp₁ _ _ _)
  have hw : Q.π i ◁ (((A i).unit' ▷ f i) ≫ eqToHom (Category.assoc _ _ _) ≫
      (f i ◁ (A i).counit')) = eqToHom (by simp) := by
    rw [hz]; simp
  rw [Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    Bicategory.comp_whiskerRight,
    Bicategory.eqToHom_whiskerRight, Bicategory.eqToHom_whiskerRight, eqToHom_trans]
  -- Compare the whiskered composite with the `i`-th triangle.
  apply eq_of_heq
  refine HEq.trans (?_ : HEq _ (Q.π i ◁ (((A i).unit' ▷ f i) ≫ eqToHom (Category.assoc _ _ _) ≫
      (f i ◁ (A i).counit')))) ((heq_of_eq hw).trans (heq_eqToHom_eqToHom _ _
        (by obj_eq)))
  rw [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  exact heq_comp (by obj_eq)
    (by obj_eq)
    (by obj_eq) t₁
    (heq_comp (by obj_eq)
      (by obj_eq)
      (by obj_eq)
      (heq_eqToHom_eqToHom _ _
        (by obj_eq)) t₃)

/-- The right triangle identity for the unit `piUnit` and counit `piCounit` of the product
adjunction. -/
lemma pi_right_triangle :
    (piR P Q g ◁ piUnit P Q A) ≫ eqToHom (Category.assoc _ _ _).symm ≫
        (piCounit P Q A ▷ piR P Q g) =
      eqToHom (Category.comp_id _) ≫ eqToHom (Category.id_comp _).symm := by
  -- Componentwise, the triangle is that of the `i`-th adjunction, up to `HEq` of whiskerings.
  refine Q.cell_ext fun i => ?_
  have hz := (A i).right_triangle'
  have t₁ : HEq ((piR P Q g ◁ piUnit P Q A) ▷ Q.π i)
      (P.π i ◁ (g i ◁ (A i).unit')) :=
    (whisker_mid _ _ _).symm.trans <|
      (heq_whiskerLeft _ (by simp) (piL_piR_π P Q i) (piUnit_π P Q A i)).trans <|
      (whiskerL_comp₁ _ _ _).symm.trans <|
      (heq_whiskerLeft_obj (Q.lift_π _ i) _).trans
      (whiskerL_comp₁ _ _ _)
  have t₃ : HEq ((piCounit P Q A ▷ piR P Q g) ▷ Q.π i)
      (P.π i ◁ ((A i).counit' ▷ g i)) :=
    (whiskerR_comp₁ _ _ _).symm.trans <|
      (heq_whiskerRight_obj _ (Q.lift_π _ i)).trans <|
      (whiskerR_comp₁ _ _ _).trans <|
      (heq_whiskerRight (piR_piL_π P Q i) (by simp) (piCounit_π P Q A i)
        (g i)).trans
      (whisker_mid _ _ _).symm
  have hw : P.π i ◁ ((g i ◁ (A i).unit') ≫
      eqToHom (Category.assoc _ _ _).symm ≫ ((A i).counit' ▷ g i)) =
        eqToHom (by simp) := by
    rw [hz]; simp
  rw [Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    Bicategory.comp_whiskerRight,
    Bicategory.eqToHom_whiskerRight, Bicategory.eqToHom_whiskerRight, eqToHom_trans]
  -- Compare the whiskered composite with the `i`-th triangle.
  apply eq_of_heq
  refine HEq.trans (?_ : HEq _ (P.π i ◁ ((g i ◁ (A i).unit') ≫
      eqToHom (Category.assoc _ _ _).symm ≫ ((A i).counit' ▷ g i))))
    ((heq_of_eq hw).trans (heq_eqToHom_eqToHom _ _ (by obj_eq)))
  rw [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  exact heq_comp (by obj_eq) (by obj_eq) (by obj_eq) t₁
    (heq_comp (by obj_eq) (by obj_eq) (by obj_eq) (heq_eqToHom_eqToHom _ _ (by obj_eq)) t₃)

/-- **The product adjunction** `F_c̄ ⊣ G_c̄` of a family of adjunctions `F_c ⊣ G_c`, with the
units and counits of the factors. -/
def piAdj : TwoAdj (piL P Q f) (piR P Q g) :=
  TwoAdj.mk' (piUnit P Q A) (piCounit P Q A) (pi_left_triangle P Q A) (pi_right_triangle P Q A)

/-- **The mate of a projection square** `G ≫ π_v = π_v ≫ g_v` (an identity) is the identity
`π_v ≫ f_v = F ≫ π_v`. -/
lemma mate_proj (v : ι) :
    (Bicategory.mateEquiv (piAdj P Q A) (A v)).symm
        (eqToHom (Q.lift_π (fun i => P.π i ≫ g i) v)) =
      eqToHom (P.lift_π (fun i => Q.π i ≫ f i) v).symm := by
  rw [Bicategory.mateEquiv_symm_apply']
  simp only [bicategoricalComp, piAdj, TwoAdj.mk']
  conv_lhs => simp
  have t₁ : HEq (piUnit P Q A ▷ Q.π v ▷ f v) (Q.π v ◁ ((A v).unit' ▷ f v)) :=
    (heq_whiskerRight (by simp) (piL_piR_π P Q v) (piUnit_π P Q A v) (f v)).trans
      (whisker_mid _ _ _).symm
  have t₃ : HEq (piL P Q f ◁ P.π v ◁ (A v).counit') (Q.π v ◁ (f v ◁ (A v).counit')) :=
    (whiskerL_comp₁ _ _ _).symm.trans ((heq_whiskerLeft_obj (P.lift_π _ v) _).trans
      (whiskerL_comp₁ _ _ _))
  have hw : Q.π v ◁ (((A v).unit' ▷ f v) ≫ eqToHom (Category.assoc _ _ _) ≫ (f v ◁ (A v).counit')) =
      eqToHom (by simp) := by
    rw [(A v).left_triangle']; simp
  apply eq_of_heq
  refine HEq.trans (?_ : HEq _ (Q.π v ◁ (((A v).unit' ▷ f v) ≫ eqToHom (Category.assoc _ _ _) ≫
      (f v ◁ (A v).counit')))) ((heq_of_eq hw).trans (heq_eqToHom_eqToHom _ _ (by obj_eq)))
  rw [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  simp only [eqToHom_comp_heq_iff]
  exact heq_comp (by obj_eq) (by obj_eq) (by obj_eq) t₁
    (heq_comp (by obj_eq) (by obj_eq) (by obj_eq) (heq_eqToHom_eqToHom _ _ (by obj_eq))
      (by simpa only [comp_eqToHom_heq_iff] using t₃))

/-- **Mates of squares into a product**, componentwise: if the `i`-th component of a square
`S : r ≫ ⟨gs⟩ ⇒ ⟨hs⟩ ≫ G` is `Sᵢ`, then the `i`-th component of its mate is the mate of `Sᵢ`. -/
lemma mate_lift_π {Yn Ym : Obj} {l : Yn ⟶ Ym} {r : Ym ⟶ Yn} (adj : TwoAdj l r)
    {gs : ∀ i, Yn ⟶ b i} {hs : ∀ i, Ym ⟶ a i} (S : r ≫ Q.lift gs ⟶ P.lift hs ≫ piR P Q g)
    (i : ι) (Si : r ≫ gs i ⟶ hs i ≫ g i) (hS : HEq (S ▷ Q.π i) Si) :
    HEq ((Bicategory.mateEquiv adj (piAdj P Q A)).symm S ▷ P.π i)
      ((Bicategory.mateEquiv adj (A i)).symm Si) := by
  have hv : HEq (Bicategory.rightAdjointSquare.vcomp S
      (eqToHom (Q.lift_π (fun i => P.π i ≫ g i) i))) Si := by
    refine HEq.trans ?_ hS
    simp [Bicategory.rightAdjointSquare.vcomp]
  have hm := Bicategory.mateEquiv_symm_heq adj (A i) (Q.lift_π gs i) (P.lift_π hs i) hv
  rw [Bicategory.mateEquiv_symm_vcomp adj (piAdj P Q A) (A i), mate_proj] at hm
  refine HEq.trans ?_ hm
  simp [Bicategory.leftAdjointSquare.vcomp]

end PiAdj

section ProdAdj

variable {M N : PreModel Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c} {Gc : ∀ c, M.obj c ⟶ N.obj c}
  (A : ∀ c, TwoAdj (Fc c) (Gc c))

/-- The product adjunction `F_c̄ ⊣ G_c̄` on the arity of a functor symbol. -/
def prodAdj (B : Sg.Fun) : TwoAdj (prodL Fc B) (prodR Gc B) :=
  piAdj (M.P B) (N.P B) (fun i => A (Sg.art B i))

/-- The product adjunction on the arity of a functor symbol `B` unfolds to `piAdj` on the products
`M.P B` and `N.P B`. -/
lemma prodAdj_eq (B : Sg.Fun) :
    prodAdj A B = piAdj (M.P B) (N.P B) (fun i => A (Sg.art B i)) := rfl

/-- `mateStr` is Mathlib's mate along the product adjunction and `F_d ⊣ G_d`. -/
lemma mateStr_eq (B : Sg.Fun) (s : prodR Gc B ≫ N.fn B ⟶ M.fn B ≫ Gc (Sg.fcod B)) :
    mateStr A B s = (Bicategory.mateEquiv (prodAdj A B) (A (Sg.fcod B))).symm s := by
  rw [Bicategory.mateEquiv_symm_apply, Bicategory.Adjunction.homEquiv₂_symm_apply,
    Bicategory.Adjunction.homEquiv₁_symm_apply]
  simp [mateStr, prodAdj]
  rfl

end ProdAdj

/-! ## The comparison 2-cells of the mates -/

section TermMate

variable {M N : Model Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c}
  (G : LaxData M.toPreModel N.toPreModel) (A : ∀ c, TwoAdj (Fc c) (G.cell c))
  {V : Type} {vty : V → Sg.Cat} (Pm : Product (fun v => M.obj (vty v)))
  (Pn : Product (fun v => N.obj (vty v)))

/-- The lax `η_t` of `G` at `B args` (after an `eqToHom`) is the vertical composite of any square
`S` of the arguments, given by their `η`, with the structure 2-cell of `G` at `B`. -/
lemma eta_app_heq_vcomp (B : Sg.Fun) (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i))
    (S : piR Pm Pn (fun v => G.cell (vty v)) ≫ (N.P B).lift (fun i => N.interp Pn.π (args i)) ⟶
      (M.P B).lift (fun i => M.interp Pm.π (args i)) ≫ prodR G.cell B)
    (hS : ∀ i, HEq (S ▷ (N.P B).π i)
      (eqToHom (N.toPreModel.interp_lift Pn (fun v => Pm.π v ≫ G.cell (vty v))
        (args i)).symm ≫ G.eta Pm.π (args i))) :
    HEq (eqToHom (N.toPreModel.interp_lift Pn
        (fun v => Pm.π v ≫ G.cell (vty v)) (Trm.app B args)).symm ≫
        G.eta Pm.π (Trm.app B args))
      (Bicategory.rightAdjointSquare.vcomp S (G.str B)) := by
  rw [LaxData.eta_app, LaxData.strAt, PreModel.appCell]
  simp only [Bicategory.rightAdjointSquare.vcomp, Bicategory.Strict.associator_eqToIso,
    eqToIso.hom, eqToIso.inv, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
  have hx : (N.P B).lift (fun i => N.interp (fun v => Pm.π v ≫ G.cell (vty v)) (args i)) =
      piR Pm Pn (fun v => G.cell (vty v)) ≫
        (N.P B).lift (fun i => N.interp Pn.π (args i)) := by
    rw [(N.P B).comp_lift]
    exact congrArg _ (funext fun i => N.toPreModel.interp_lift Pn _ (args i))
  have hy : (N.P B).lift (fun i => M.interp Pm.π (args i) ≫ G.cell (Sg.art B i)) =
      (M.P B).lift (fun i => M.interp Pm.π (args i)) ≫ prodR G.cell B :=
    (G.lift_comp_prodCell B _).symm
  refine heq_comp (by rw [hx]) (by rw [hy]) rfl
    (heq_whiskerRight hx hy (heq_of_proj (N.P B) hx hy _ _ fun i => ?_) (N.fn B)) ?_
  · rw [(N.P B).lift₂_π]; simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact ((hS i).trans (eqToHom_comp_heq _ _)).symm
  · simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff]
    rfl

/-- **The comparison 2-cells of the mates are the mates of the comparison 2-cells**: for a
context with products `Pm`, `Pn`, the oplax `η_t` of `mateOplaxData G A` at the projections of
`Pn` is the mate, along the context adjunction and `F_c ⊣ G_c`, of the lax `η_t` of `G` at the
projections of `Pm`. -/
lemma eta_mate : ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c),
    HEq ((mateOplaxData G A).eta Pn.π t)
      ((Bicategory.mateEquiv (piAdj Pm Pn (fun v => A (vty v))) (A c)).symm
        (eqToHom (N.toPreModel.interp_lift Pn (fun v => Pm.π v ≫ G.cell (vty v)) t).symm ≫
          G.eta Pm.π t))
  | _, .var v => by
      rw [OplaxData.eta_var, LaxData.eta_var, Category.comp_id]
      exact (eqToHom_heq_id (Pm.lift_π (fun i => Pn.π i ≫ Fc (vty i)) v).symm).symm.trans
        (heq_of_eq (mate_proj Pm Pn (fun v => A (vty v)) v).symm)
  | _, .app B args => by
      have ih := fun i => eta_mate (args i)
      -- the square of the arguments, into the product of the arity of `B`
      let S : piR Pm Pn (fun v => G.cell (vty v)) ≫
          (N.P B).lift (fun i => N.interp Pn.π (args i)) ⟶
          (M.P B).lift (fun i => M.interp Pm.π (args i)) ≫ prodR G.cell B :=
        (N.P B).lift₂ (fun i => eqToHom (by obj_eq) ≫
          (eqToHom (N.toPreModel.interp_lift Pn (fun v => Pm.π v ≫ G.cell (vty v))
            (args i)).symm ≫ G.eta Pm.π (args i)) ≫ eqToHom (by obj_eq))
      have hS : ∀ i, HEq (S ▷ (N.P B).π i)
          (eqToHom (N.toPreModel.interp_lift Pn (fun v => Pm.π v ≫ G.cell (vty v))
            (args i)).symm ≫ G.eta Pm.π (args i)) := fun i => by
        simp only [S, (N.P B).lift₂_π, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
          heq_eqToHom_comp_iff]; rfl
      have C1 := eta_app_heq_vcomp G Pm Pn B args S hS
      have key := Bicategory.mateEquiv_symm_heq (piAdj Pm Pn (fun v => A (vty v)))
        (A (Sg.fcod B)) rfl rfl C1
      rw [Bicategory.mateEquiv_symm_vcomp (piAdj Pm Pn (fun v => A (vty v))) (prodAdj A B)
        (A (Sg.fcod B)), ← mateStr_eq, prodAdj_eq] at key
      refine HEq.trans ?_ key.symm
      have ex : (M.P B).lift (fun i => N.interp Pn.π (args i) ≫ Fc (Sg.art B i)) =
          (N.P B).lift (fun i => N.interp Pn.π (args i)) ≫ prodL Fc B :=
        ((mateOplaxData G A).lift_comp_prodCell B _).symm
      have ey : (M.P B).lift (fun i => M.interp (fun v => Pn.π v ≫ Fc (vty v)) (args i)) =
          piL Pm Pn (fun v => Fc (vty v)) ≫ (M.P B).lift (fun i => M.interp Pm.π (args i)) := by
        rw [(M.P B).comp_lift]
        exact congrArg _ (funext fun i => M.toPreModel.interp_lift Pm _ (args i))
      have C2 : HEq ((M.P B).lift₂ (fun i =>
            eqToHom ((M.P B).lift_π (fun i => N.interp Pn.π (args i) ≫ Fc (Sg.art B i)) i) ≫
              (mateOplaxData G A).eta Pn.π (args i) ≫
              eqToHom ((M.P B).lift_π (fun i =>
                M.interp (fun v => Pn.π v ≫ Fc (vty v)) (args i)) i).symm))
          ((Bicategory.mateEquiv (piAdj Pm Pn (fun v => A (vty v)))
            (piAdj (M.P B) (N.P B) (fun i => A (Sg.art B i)))).symm S) := by
        refine heq_of_proj (M.P B) ex ey _ _ fun i => ?_
        rw [(M.P B).lift₂_π]
        simp only [eqToHom_comp_heq_iff]
        have := (mate_lift_π (M.P B) (N.P B) (fun i => A (Sg.art B i))
          (piAdj Pm Pn (fun v => A (vty v))) S i _ (hS i)).symm
        exact (comp_eqToHom_heq _ _).trans ((ih i).trans this)
      rw [OplaxData.eta_app, OplaxData.strAt, PreModel.appCell]
      simp only [Bicategory.leftAdjointSquare.vcomp, Bicategory.Strict.associator_eqToIso,
        eqToIso.hom, eqToIso.inv, heq_eqToHom_comp_iff]
      refine heq_comp (Category.assoc _ _ _)
        ((ex =≫ M.fn B).trans (Category.assoc _ _ _))
        ((ey =≫ M.fn B).trans (Category.assoc _ _ _))
        ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _))
        ((heq_whiskerRight ex ey C2 (M.fn B)).trans
          ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

end TermMate

/-! ## The lax data with the inverse structure 2-cells -/

section InvData

variable {M N : PreModel Sg Obj} (F : OplaxData M N) [∀ B, IsIso (F.str B)]

/-- The structure 2-cell of `invLaxData F` at a family `g`, followed by that of `F`, is the
identity. -/
lemma invLaxData_strAt_hom (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (invLaxData F).strAt B g ≫ F.strAt B g = 𝟙 _ := by
  dsimp only [LaxData.strAt, OplaxData.strAt, invLaxData]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Bicategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id, Bicategory.whiskerLeft_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- The structure 2-cell of `F` at a family `g`, followed by that of `invLaxData F`, is the
identity. -/
lemma invLaxData_strAt_inv (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    F.strAt B g ≫ (invLaxData F).strAt B g = 𝟙 _ := by
  dsimp only [LaxData.strAt, OplaxData.strAt, invLaxData]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Bicategory.whiskerLeft_comp_assoc, IsIso.hom_inv_id, Bicategory.whiskerLeft_id,
    Category.id_comp, eqToHom_trans, eqToHom_refl]

variable {V : Type} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))

/-- For every term `t`, the comparison 2-cell `η_t` of `invLaxData F` followed by that of `F` is the
identity. -/
lemma invLaxData_eta_hom : ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c),
    (invLaxData F).eta ρ t ≫ F.eta ρ t = 𝟙 _
  | _, .var v => by
      rw [LaxData.eta_var, OplaxData.eta_var]; exact Category.id_comp _
  | _, .app B args => by
      rw [LaxData.eta_app, OplaxData.eta_app]
      have h1 := invLaxData_strAt_hom F B (fun i => M.interp ρ (args i))
      have h2 : N.appCell B (fun i => (invLaxData F).eta ρ (args i)) ≫
          N.appCell B (fun i => F.eta ρ (args i)) = 𝟙 _ :=
        (N.appCell_comp B _ _).trans
          ((N.appCell_congr B (fun i => invLaxData_eta_hom (args i))).trans (N.appCell_id B _))
      exact (Category.assoc _ _ _).trans ((_ ≫= (Category.assoc _ _ _).symm.trans
        ((h1 =≫ _).trans (Category.id_comp _))).trans h2)

/-- For every term `t`, the comparison 2-cell `η_t` of `F` followed by that of `invLaxData F` is the
identity. -/
lemma invLaxData_eta_inv : ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c),
    F.eta ρ t ≫ (invLaxData F).eta ρ t = 𝟙 _
  | _, .var v => by
      rw [LaxData.eta_var, OplaxData.eta_var]; exact Category.id_comp _
  | _, .app B args => by
      rw [LaxData.eta_app, OplaxData.eta_app]
      have h1 := invLaxData_strAt_inv F B (fun i => M.interp ρ (args i))
      have h2 : N.appCell B (fun i => F.eta ρ (args i)) ≫
          N.appCell B (fun i => (invLaxData F).eta ρ (args i)) = 𝟙 _ :=
        (N.appCell_comp B _ _).trans
          ((N.appCell_congr B (fun i => invLaxData_eta_inv (args i))).trans (N.appCell_id B _))
      exact (Category.assoc _ _ _).trans ((_ ≫= (Category.assoc _ _ _).symm.trans
        ((h2 =≫ _).trans (Category.id_comp _))).trans h1)

end InvData

section InvMor

variable {M N : Model Sg Obj} (F : OplaxMor M N) [∀ B, IsIso (F.str B)]

/-- The lax data with the inverse structure 2-cells of an oplax morphism is compatible with the
transformation symbols. -/
lemma invLaxData_tr_compat (a : Sg.Tr) :
    (N.trAt a (fun i => (M.Pctx a).π i ≫ (invLaxData F.toOplaxData).cell (Sg.trt a i))) ≫
        (invLaxData F.toOplaxData).eta (M.Pctx a).π (Sg.trtgt a)
      = (invLaxData F.toOplaxData).eta (M.Pctx a).π (Sg.trsrc a) ≫
        (M.tr a ▷ (invLaxData F.toOplaxData).cell (Sg.trty a)) := by
  have h := F.tr_compat a
  have hs := invLaxData_eta_hom F.toOplaxData (M.Pctx a).π (Sg.trsrc a)
  have ht := invLaxData_eta_inv F.toOplaxData (M.Pctx a).π (Sg.trtgt a)
  exact (Category.id_comp _).symm.trans <| (hs.symm =≫ _).trans <|
    (Category.assoc _ _ _).trans <| _ ≫= ((Category.assoc _ _ _).symm.trans <|
      (h.symm =≫ _).trans <| (Category.assoc _ _ _).trans <|
        (_ ≫= ht).trans (Category.comp_id _))

end InvMor

/-! ## The unit and the counit of the doctrinal adjunction -/

section UnitCounit

variable {M N : Model Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c}
  (G : LaxData M.toPreModel N.toPreModel) (A : ∀ c, TwoAdj (Fc c) (G.cell c))

/-- The 2-cell induced on the arity of `B` by the units of the adjunctions `F_c ⊣ G_c` is the unit
`prodUnit` of the product adjunction, up to heterogeneous equality. -/
lemma prodApp_unit_heq (B : Sg.Fun) :
    HEq (prodApp (M := N.toPreModel) (N := N.toPreModel) (Hc := fun c => 𝟙 (N.obj c))
      (H'c := fun c => Fc c ≫ G.cell c) (fun c => (A c).unit') B) (prodUnit A B) := by
  refine heq_of_proj (N.P B) ?_ ?_ _ _ (fun i => ?_)
  · exact (N.P B).hom_ext fun i => by simp [Product.lift_π]
  · exact (N.P B).hom_ext fun i => by
      simp only [Category.assoc, Product.lift_π, lift_π_assoc]
  · rw [prodApp_π, prodUnit, (N.P B).lift₂_π]
    simp


/-- The 2-cell induced on the arity of `B` by the counits of the adjunctions `F_c ⊣ G_c` is the
counit of the product adjunction `prodAdj A B`, up to heterogeneous equality. -/
lemma prodApp_counit_heq (B : Sg.Fun) :
    HEq (prodApp (M := M.toPreModel) (N := M.toPreModel) (Hc := fun c => G.cell c ≫ Fc c)
      (H'c := fun c => 𝟙 (M.obj c)) (fun c => (A c).counit') B) ((prodAdj A B).counit) := by
  refine heq_of_proj (M.P B) ?_ ?_ _ _ (fun i => ?_)
  · exact (M.P B).hom_ext fun i => by
      simp only [Category.assoc, Product.lift_π, lift_π_assoc]
  · exact (M.P B).hom_ext fun i => by simp [Product.lift_π]
  · rw [prodApp_π, prodAdj_eq]
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    exact (piCounit_π (M.P B) (N.P B) (fun i => A (Sg.art B i)) i).symm

variable [∀ B, IsIso ((mateOplaxData G A).str B)]

/-- The units of the adjunctions `F_c ⊣ G_c` are compatible with the structure 2-cells at a functor
symbol `B`, from the identity lax morphism of `N` to the inverse of the mate of `G` followed by
`G`. -/
lemma unit_str_compat (B : Sg.Fun) :
    (prodApp (M := N.toPreModel) (N := N.toPreModel) (Hc := fun c => 𝟙 (N.obj c))
      (H'c := fun c => Fc c ≫ G.cell c) (fun c => (A c).unit') B ▷ N.fn B) ≫
        ((invLaxData (mateOplaxData G A)).comp G).str B =
      (LaxData.idData N.toPreModel).str B ≫ (N.fn B ◁ (A (Sg.fcod B)).unit') := by
  have : IsIso (mateStr A B (G.str B)) :=
    inferInstanceAs (IsIso ((mateOplaxData G A).str B))
  have hu := Bicategory.unit_mateEquiv_symm (prodAdj A B) (A (Sg.fcod B)) (G.str B)
  rw [← mateStr_eq] at hu
  simp only [AsBicat.leftUnitor_inv, AsBicat.associator_hom, AsBicat.associator_inv,
    AsBicat.rightUnitor_inv] at hu
  have hu' := (eqToHom_comp_iff _ _ _).1 hu
  simp only [Category.assoc, eqToHom_trans_assoc] at hu'
  have hsrc : (N.P B).lift (fun i => (N.P B).π i ≫ 𝟙 (N.obj (Sg.art B i))) = 𝟙 _ :=
    (N.P B).hom_ext fun i => by simp [Product.lift_π]
  have htgt : (N.P B).lift (fun i => (N.P B).π i ≫ (Fc (Sg.art B i) ≫ G.cell (Sg.art B i))) =
      prodL Fc B ≫ prodR G.cell B :=
    (N.P B).hom_ext fun i => by simp only [Category.assoc, Product.lift_π, lift_π_assoc]
  have H1 := heq_whiskerRight hsrc htgt (prodApp_unit_heq G A B) (N.fn B)
  have hX : (prodUnit A B ▷ N.fn B) ≫
      eqToHom (Category.assoc (prodL Fc B) (prodR G.cell B) (N.fn B)) ≫
        (prodL Fc B ◁ G.str B) ≫
          eqToHom (Category.assoc (prodL Fc B) (M.fn B) (G.cell (Sg.fcod B))).symm ≫
            (inv (mateStr A B (G.str B)) ▷ G.cell (Sg.fcod B)) =
        eqToHom (by simp) ≫ (N.fn B ◁ (A (Sg.fcod B)).unit') ≫ eqToHom (by simp) := by
    have k : (prodUnit A B ▷ N.fn B) ≫
        eqToHom (Category.assoc (prodL Fc B) (prodR G.cell B) (N.fn B)) ≫
          (prodL Fc B ◁ G.str B) =
        eqToHom (by simp) ≫ (N.fn B ◁ (A (Sg.fcod B)).unit') ≫ eqToHom (by simp) ≫
          (mateStr A B (G.str B) ▷ G.cell (Sg.fcod B)) ≫
            eqToHom (Category.assoc (prodL Fc B) (M.fn B) (G.cell (Sg.fcod B))) := hu'
    rw [reassoc_of% k, eqToHom_trans_assoc, eqToHom_refl]
    simp only [Category.id_comp, ← Bicategory.comp_whiskerRight, IsIso.hom_inv_id,
      Bicategory.id_whiskerRight, Category.comp_id]
  rw [LaxData.comp_str, LaxData.strAt]
  dsimp only [invLaxData, mateOplaxData, LaxData.idData]
  apply eq_of_heq
  refine (heq_comp ?_ ?_ ?_ H1 ?_).trans ((heq_of_eq hX).trans ?_)
  · exact (hsrc =≫ N.fn B)
  · exact (htgt =≫ N.fn B)
  · exact (Category.assoc _ _ _).symm
  · simp only [← Category.assoc]
    refine (comp_eqToHom_heq _ _).trans (heq_comp ?_ rfl rfl ?_ HEq.rfl)
    · exact (htgt =≫ N.fn B)
    refine heq_comp ?_ rfl rfl ?_ (heq_eqToHom_eqToHom _ _ rfl)
    · exact (htgt =≫ N.fn B)
    refine heq_comp ?_ rfl rfl ?_ HEq.rfl
    · exact (htgt =≫ N.fn B)
    refine (eqToHom_comp_heq _ _).trans (heq_eqToHom_eqToHom _ _ ?_)
    have htgt' : (N.P B).lift (fun i => ((N.P B).π i ≫ Fc (Sg.art B i)) ≫ G.cell (Sg.art B i)) =
        prodL Fc B ≫ prodR G.cell B :=
      (N.P B).hom_ext fun i => by simp only [Category.assoc, Product.lift_π, lift_π_assoc]
    exact (htgt' =≫ N.fn B)
  · exact (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans
      (eqToHom_comp_heq _ _).symm)

/-- The counits of the adjunctions `F_c ⊣ G_c` are compatible with the structure 2-cells at a
functor symbol `B`, from `G` followed by the inverse of its mate to the identity lax morphism of
`M`. -/
lemma counit_str_compat (B : Sg.Fun) :
    (prodApp (M := M.toPreModel) (N := M.toPreModel) (Hc := fun c => G.cell c ≫ Fc c)
      (H'c := fun c => 𝟙 (M.obj c)) (fun c => (A c).counit') B ▷ M.fn B) ≫
        (LaxData.idData M.toPreModel).str B =
      (G.comp (invLaxData (mateOplaxData G A))).str B ≫ (M.fn B ◁ (A (Sg.fcod B)).counit') := by
  have : IsIso (mateStr A B (G.str B)) :=
    inferInstanceAs (IsIso ((mateOplaxData G A).str B))
  have hc := Bicategory.mateEquiv_symm_counit (prodAdj A B) (A (Sg.fcod B)) (G.str B)
  rw [← mateStr_eq] at hc
  simp only [AsBicat.leftUnitor_hom, AsBicat.associator_hom, AsBicat.associator_inv,
    AsBicat.rightUnitor_hom] at hc
  have k' : (G.str B ▷ Fc (Sg.fcod B)) ≫
      eqToHom (Category.assoc (M.fn B) (G.cell (Sg.fcod B)) (Fc (Sg.fcod B))) ≫
        (M.fn B ◁ (A (Sg.fcod B)).counit') ≫ eqToHom (Category.comp_id (M.fn B)) =
      eqToHom (Category.assoc (prodR G.cell B) (N.fn B) (Fc (Sg.fcod B))) ≫
        (prodR G.cell B ◁ mateStr A B (G.str B)) ≫
          eqToHom (Category.assoc (prodR G.cell B) (prodL Fc B) (M.fn B)).symm ≫
            ((prodAdj A B).counit' ▷ M.fn B) ≫ eqToHom (Category.id_comp (M.fn B)) := hc
  have k2 := k' =≫ eqToHom (Category.comp_id (M.fn B)).symm
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at k2
  have hY : ((prodR G.cell B ◁ inv (mateStr A B (G.str B))) ≫
      eqToHom (Category.assoc (prodR G.cell B) (N.fn B) (Fc (Sg.fcod B))).symm ≫
        (G.str B ▷ Fc (Sg.fcod B)) ≫
          eqToHom (Category.assoc (M.fn B) (G.cell (Sg.fcod B)) (Fc (Sg.fcod B)))) ≫
        (M.fn B ◁ (A (Sg.fcod B)).counit') =
      eqToHom (by simp) ≫ ((prodAdj A B).counit' ▷ M.fn B) ≫ eqToHom (by simp) := by
    simp only [Category.assoc]
    rw [k2, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Bicategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id, Bicategory.whiskerLeft_id,
      Category.id_comp]
  have hRL : (M.P B).lift (fun i => (M.P B).π i ≫ (G.cell (Sg.art B i) ≫ Fc (Sg.art B i))) =
      prodR G.cell B ≫ prodL Fc B :=
    (M.P B).hom_ext fun i => by simp only [Category.assoc, Product.lift_π, lift_π_assoc]
  rw [LaxData.comp_str, LaxData.strAt]
  dsimp only [invLaxData, mateOplaxData, LaxData.idData]
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans
    ((heq_whiskerRight ?_ ?_ (prodApp_counit_heq G A B) (M.fn B)).trans ?_)
  · exact (M.P B).hom_ext fun i => by
      simp only [Category.assoc, Product.lift_π, lift_π_assoc]
  · exact (M.P B).hom_ext fun i => by simp [Product.lift_π]
  · refine HEq.trans ?_ ((heq_of_eq hY).symm.trans ?_)
    · exact ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm
    · refine heq_comp ?_ rfl rfl ?_ HEq.rfl
      · exact (Category.assoc _ _ _).symm.trans (hRL.symm =≫ M.fn B)
      · refine HEq.trans ?_ (eqToHom_comp_heq _ _).symm
        refine (heq_of_eq (Category.assoc _ _ _).symm).trans (heq_comp ?_ rfl rfl ?_ HEq.rfl)
        · have hRL' : (M.P B).lift
                (fun i => ((M.P B).π i ≫ G.cell (Sg.art B i)) ≫ Fc (Sg.art B i)) =
              prodR G.cell B ≫ prodL Fc B :=
            (M.P B).hom_ext fun i => by simp only [Category.assoc, Product.lift_π, lift_π_assoc]
          exact (Category.assoc _ _ _).symm.trans (hRL'.symm =≫ M.fn B)
        · exact (comp_eqToHom_heq _ _).trans
            ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm

end UnitCounit

/-! ## Compatibility with the transformation symbols -/

section TrCompat

variable {M N : Model Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c}
  (G : LaxData M.toPreModel N.toPreModel) (A : ∀ c, TwoAdj (Fc c) (G.cell c))

/-- **Lax compatibility with a transformation symbol is oplax compatibility of the mates.** -/
lemma tr_compat_iff (a : Sg.Tr) :
    (N.trAt a (fun i => (M.Pctx a).π i ≫ G.cell (Sg.trt a i))) ≫ G.eta (M.Pctx a).π (Sg.trtgt a)
        = G.eta (M.Pctx a).π (Sg.trsrc a) ≫ (M.tr a ▷ G.cell (Sg.trty a)) ↔
      (N.tr a ▷ (mateOplaxData G A).cell (Sg.trty a)) ≫
          (mateOplaxData G A).eta (N.Pctx a).π (Sg.trtgt a)
        = (mateOplaxData G A).eta (N.Pctx a).π (Sg.trsrc a) ≫
          (M.trAt a (fun i => (N.Pctx a).π i ≫ (mateOplaxData G A).cell (Sg.trt a i))) := by
  set Pm := M.Pctx a
  set Pn := N.Pctx a
  -- The product adjunctions on the contexts, and the interpretations of both sides.
  let adj₁ := piAdj Pm Pn (fun v => A (Sg.trt a v))
  have p₁ := N.toPreModel.interp_lift Pn (fun v => Pm.π v ≫ G.cell (Sg.trt a v)) (Sg.trsrc a)
  have p₂ := N.toPreModel.interp_lift Pn (fun v => Pm.π v ≫ G.cell (Sg.trt a v)) (Sg.trtgt a)
  have f₁ := M.toPreModel.interp_lift Pm (fun v => Pn.π v ≫ Fc (Sg.trt a v)) (Sg.trsrc a)
  have f₂ := M.toPreModel.interp_lift Pm (fun v => Pn.π v ≫ Fc (Sg.trt a v)) (Sg.trtgt a)
  let βs := eqToHom p₁.symm ≫ G.eta Pm.π (Sg.trsrc a)
  let βt := eqToHom p₂.symm ≫ G.eta Pm.π (Sg.trtgt a)
  have hs : (mateOplaxData G A).eta Pn.π (Sg.trsrc a) =
      (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm βs ≫ eqToHom f₁.symm :=
    eq_comp_eqToHom_of_heq _ _ _ (eta_mate G A Pm Pn (Sg.trsrc a))
  have ht : (mateOplaxData G A).eta Pn.π (Sg.trtgt a) =
      (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm βt ≫ eqToHom f₂.symm :=
    eq_comp_eqToHom_of_heq _ _ _ (eta_mate G A Pm Pn (Sg.trtgt a))
  -- The compatibility square of `G` and that of its mate correspond under the mate bijection.
  have hl₁ : N.trAt a (fun i => Pm.π i ≫ G.cell (Sg.trt a i)) ≫ G.eta Pm.π (Sg.trtgt a) =
      eqToHom p₁ ≫ ((piR Pm Pn (fun v => G.cell (Sg.trt a v)) ◁ N.tr a) ≫ βt) := by
    simp only [Model.trAt, βt, Category.assoc]
    rfl
  have hl₂ : G.eta Pm.π (Sg.trsrc a) ≫ (M.tr a ▷ G.cell (Sg.trty a)) =
      eqToHom p₁ ≫ (βs ≫ (M.tr a ▷ G.cell (Sg.trty a))) := by
    simp only [βs, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have ho₁ : (N.tr a ▷ (mateOplaxData G A).cell (Sg.trty a)) ≫
      (mateOplaxData G A).eta Pn.π (Sg.trtgt a) =
        ((N.tr a ▷ Fc (Sg.trty a)) ≫ (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm βt) ≫
          eqToHom f₂.symm := by
    rw [ht, Category.assoc]; rfl
  have ho₂ : (mateOplaxData G A).eta Pn.π (Sg.trsrc a) ≫
      M.trAt a (fun i => Pn.π i ≫ (mateOplaxData G A).cell (Sg.trt a i)) =
        ((Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm βs ≫
          (piL Pm Pn (fun v => Fc (Sg.trt a v)) ◁ M.tr a)) ≫ eqToHom f₂.symm := by
    rw [hs, Model.trAt]
    exact (comp_eqToHom_eqToHom_comp _ _ _ _).trans (Category.assoc _ _ _).symm
  have e1 : (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm
      ((piR Pm Pn (fun v => G.cell (Sg.trt a v)) ◁ N.tr a) ≫ βt) =
        (N.tr a ▷ Fc (Sg.trty a)) ≫ (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm βt :=
    Bicategory.mateEquiv_symm_comp_left adj₁ (A (Sg.trty a)) (N.tr a) βt
  have e2 : (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm
      (βs ≫ (M.tr a ▷ G.cell (Sg.trty a))) =
        (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm βs ≫
          (piL Pm Pn (fun v => Fc (Sg.trt a v)) ◁ M.tr a) :=
    Bicategory.mateEquiv_symm_comp_right adj₁ (A (Sg.trty a)) βs (M.tr a)
  rw [hl₁, hl₂, ho₁, ho₂, cancel_epi]
  constructor
  · intro h
    exact (e1.symm.trans ((congrArg (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm h).trans
      e2)) =≫ eqToHom f₂.symm
  · intro h
    exact (Bicategory.mateEquiv adj₁ (A (Sg.trty a))).symm.injective
      (e1.trans ((comp_eqToHom_cancel _ h).trans e2.symm))

end TrCompat

end UlmerBialgebras.Paper.Doctrinal
