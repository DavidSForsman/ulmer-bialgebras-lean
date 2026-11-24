module

public import UlmerBialgebras.Basic.PIE

@[expose] public section

/-!
# The 2-category `K^co`

For a strict 2-category `K`, `K^co` has the same objects and 1-cells and the 2-cells reversed.
Every statement about `K` has a dual statement about `K^co`, and the paper's "dually" arguments
are instances of this: right Kan extensions in `K` are left Kan extensions in `K^co`, oplax
morphisms of models in `K` are lax morphisms in `K^co`, and so on.

This file sets up `K^co` and shows that PIE limits transfer:
* products and equifiers in `K^co` are those of `K`;
* the inserter of `(f, g)` in `K^co` is the inserter of `(g, f)` in `K`.

Hence `K^co` is PIE-complete when `K` is.

This dual keeps the 1-cells of `K` unchanged, and the paper library uses that by definition. For a
general bicategory use `Bicategory.Co` (the development repository's
`Foundations/CategoryTheory/Bicategory/Co.lean`), which
wraps the 1-cells in `ᵒᵖ`; the two are not identified here.

## Main definitions

* `UlmerBialgebras.Co Obj`: the objects of `K^co`, wrapping those of `K` (`UlmerBialgebras.Co.op`,
  `UlmerBialgebras.Co.unop`); `UlmerBialgebras.Co.hom`, `UlmerBialgebras.Co.cell` and
  `UlmerBialgebras.Co.uncell` translate 1-cells and 2-cells.
* `UlmerBialgebras.Co.product`, `UlmerBialgebras.Co.inserter`, `UlmerBialgebras.Co.equifier`: PIE
  limits in `K^co` from those of `K`; `UlmerBialgebras.Co.pieComplete`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2
* [G. J. Bird, G. M. Kelly, A. J. Power, R. H. Street,
  *Flexible limits for 2-categories*][birdFlexibleLimits2categories1989]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

universe u v w s

namespace UlmerBialgebras

open CategoryTheory Bicategory

/-- The objects of `K^co`, the 2-category `K` with its 2-cells reversed. As for Mathlib's
`Opposite`, this is a one-field structure rather than a type synonym, so that objects of `K^co`
are never silently identified with objects of `K`. -/
structure Co (Obj : Type u) : Type u where
  /-- An object of `K`, seen in `K^co`. -/
  op ::
  /-- An object of `K^co`, seen in `K`. -/
  unop : Obj

namespace Co

variable {Obj : Type u}

/-- Unwrapping an object of `K` seen in `K^co` gives it back. -/
@[simp] lemma unop_op (a : Obj) : unop (op a) = a := rfl

/-- Structure eta for `K^co`. -/
@[simp] lemma op_unop (a : Co Obj) : op (unop a) = a := rfl

variable [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- `K^co`: the same objects and 1-cells as `K`, with the 2-cells reversed. -/
abbrev twoCategoryData : TwoCategoryData.{u, v, w} (Co Obj) where
  Hom a b := a.unop ⟶ b.unop
  Cell f g := g ⟶ f
  id₁ a := 𝟙 a.unop
  comp₁ f g := f ≫ g
  id₁_comp₁ f := Bicategory.Strict.id_comp (B := Obj) f
  comp₁_id₁ f := Bicategory.Strict.comp_id (B := Obj) f
  assoc₁ f g h := Bicategory.Strict.assoc (B := Obj) f g h
  id₂ f := 𝟙 f
  vcomp α β := β ≫ α
  id₂_vcomp α := Category.comp_id α
  vcomp_id₂ α := Category.id_comp α
  vcomp_assoc α β γ := (Category.assoc γ β α).symm
  whiskerL f _ _ α := f ◁ α
  whiskerR α h := α ▷ h
  whiskerL_id₂ f g := Bicategory.whiskerLeft_id (B := Obj) f g
  whiskerR_id₂ f g := Bicategory.id_whiskerRight (B := Obj) f g
  whiskerL_vcomp f _ _ _ α β := Bicategory.whiskerLeft_comp (B := Obj) f β α
  whiskerR_vcomp α β k := Bicategory.comp_whiskerRight (B := Obj) β α k
  interchange α β := Bicategory.whisker_exchange (B := Obj) α β
  whiskerL_id₁ α := Bicategory.Strict.id_whiskerLeft_heq (B := Obj) α
  whiskerR_id₁ α := Bicategory.Strict.whiskerRight_id_heq (B := Obj) α
  whiskerL_comp₁ f g _ _ α := Bicategory.Strict.comp_whiskerLeft_heq (B := Obj) f g α
  whiskerR_comp₁ α h k := Bicategory.Strict.whiskerRight_comp_heq (B := Obj) α h k
  whisker_mid f _ _ α k := Bicategory.Strict.whisker_assoc_heq (B := Obj) f α k

instance bicategory : CategoryTheory.Bicategory.{w, v} (Co Obj) := twoCategoryData.toBicategory

instance strictBicategory : CategoryTheory.Bicategory.Strict (Co Obj) := twoCategoryData.strict

/-- A 1-cell of `K`, seen in `K^co`. -/
abbrev hom {a b : Obj} (f : a ⟶ b) : op a ⟶ op b := f

/-- A 2-cell `g ⟹ f` of `K` is a 2-cell `f ⟹ g` of `K^co`. -/
abbrev cell {a b : Obj} {f g : a ⟶ b} (α : g ⟶ f) : hom f ⟶ hom g := α

/-- A 2-cell `f ⟹ g` of `K^co` is a 2-cell `g ⟹ f` of `K`. -/
abbrev uncell {a b : Obj} {f g : a ⟶ b} (α : hom f ⟶ hom g) : g ⟶ f := α

/-- `uncell` is a left inverse of `cell`: `uncell (cell α) = α`. -/
lemma uncell_cell {a b : Obj} {f g : a ⟶ b} (α : g ⟶ f) : uncell (cell α) = α := rfl
/-- `cell` is a left inverse of `uncell`: `cell (uncell α) = α`. -/
lemma cell_uncell {a b : Obj} {f g : a ⟶ b} (α : hom f ⟶ hom g) : cell (uncell α) = α :=
  rfl

/-- `uncell` reverses vertical composition: `uncell (α ≫ β) = uncell β ≫ uncell α`. -/
@[simp] lemma uncell_comp {a b : Obj} {f g h : a ⟶ b} (α : hom f ⟶ hom g) (β : hom g ⟶ hom h) :
    uncell (α ≫ β) = uncell β ≫ uncell α := rfl

/-- `uncell` sends the identity 2-cell of `K^co` to the identity 2-cell of `K`. -/
@[simp] lemma uncell_id {a b : Obj} (f : a ⟶ b) : uncell (𝟙 (hom f)) = 𝟙 f := rfl


section Cells

variable {a b : Co Obj}

/-- Vertical composition in `K^co` is vertical composition in `K` in the opposite order. -/
lemma comp_eq {f g h : a ⟶ b} (α : f ⟶ g) (β : g ⟶ h) :
    α ≫ β = @CategoryStruct.comp (unop a ⟶ unop b) _ h g f β α :=
  rfl

/-- `eqToHom` in `K^co` is `eqToHom` of the inverse equality in `K`. -/
lemma eqToHom_eq {f g : a ⟶ b} (e : f = g) :
    eqToHom e = @eqToHom (unop a ⟶ unop b) _ g f e.symm := by
  cases e; rfl
/-- Whiskering in `K^co` is whiskering in `K`. -/
lemma whiskerLeft_eq {c : Co Obj} (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    f ◁ α = @Bicategory.whiskerLeft Obj _ (unop a) (unop b) (unop c) f h g α := rfl


/-- Right whiskering in `K^co` is right whiskering in `K`. -/
lemma whiskerRight_eq {c : Co Obj} {f g : a ⟶ b} (α : f ⟶ g) (h : b ⟶ c) :
    α ▷ h = @Bicategory.whiskerRight Obj _ (unop a) (unop b) (unop c) g f α h := rfl

end Cells

section PIE

/-- A product in `K` is a product in `K^co`. -/
@[implicit_reducible]
def product {ι : Type s} {c : ι → Obj} (P : Product c) :
    Product (Obj := Co Obj) (fun i => op (c i)) where
  pt := op P.pt
  π i := P.π i
  lift g := P.lift g
  lift_π g i := P.lift_π g i
  lift_uniq h := P.lift_uniq h
  lift₂ α := P.lift₂ α
  lift₂_π α i := P.lift₂_π α i
  lift₂_uniq β := P.lift₂_uniq β

/-- An equifier in `K` is an equifier in `K^co`. -/
def equifier {a b : Obj} {f g : a ⟶ b} {η θ : g ⟶ f} (E : Equifier η θ) :
    Equifier (Obj := Co Obj) (Co.cell η) (Co.cell θ) where
  pt := op E.pt
  e := E.e
  cond := E.cond
  lift h H := E.lift h H
  lift_e h H := E.lift_e h H
  lift_uniq k h H hk := E.lift_uniq k h H hk
  full β := E.full β
  faithful α β h := E.faithful α β h

/-- The inserter of `(g, f)` in `K` is the inserter of `(f, g)` in `K^co`. -/
@[implicit_reducible]
def inserter {a b : Obj} {f g : a ⟶ b} (I : Inserter g f) :
    Inserter (Obj := Co Obj) (hom f) (hom g) where
  pt := op I.pt
  u := I.u
  φ := I.φ
  lift h α := I.lift h α
  lift_u h α := I.lift_u h α
  lift_φ h α := by
    simp only [comp_eq, eqToHom_eq, whiskerLeft_eq]
    rw [I.lift_φ]
    with_unfolding_all simp
  lift_uniq k h α hu hφ := I.lift_uniq k h α hu (by
    simp only [comp_eq, eqToHom_eq, whiskerLeft_eq] at hφ
    rw [hφ]
    with_unfolding_all simp)
  lift₂ {_ k₁ k₂} α H := I.lift₂ (k₁ := k₂) (k₂ := k₁) α (by
    with_unfolding_all simp only [comp_eq, eqToHom_eq, whiskerLeft_eq, whiskerRight_eq] at H
    have H' := H.symm
    simp only [Category.assoc] at H'
    simp only [Category.assoc]
    exact H')
  lift₂_u α H := I.lift₂_u α _
  lift₂_uniq β γ h := I.lift₂_uniq β γ h

/-- `K^co` has chosen finite products when `K` has. -/
instance hasChosenFinProducts [P : HasChosenFinProducts.{u, v, w} Obj] :
    HasChosenFinProducts.{u, v, w} (Co Obj) where
  finProd c := @product Obj _ _ _ (fun i => unop (c i)) (P.finProd (fun i => unop (c i)))

/-- `K^co` has chosen inserters when `K` has: the inserter of `(f, g)` in `K^co` is that of
`(g, f)` in `K`. -/
instance hasChosenInserters [P : HasChosenInserters.{u, v, w} Obj] :
    HasChosenInserters.{u, v, w} (Co Obj) where
  ins f g := inserter (P.ins g f)

/-- `K^co` has chosen equifiers when `K` has. -/
instance hasChosenEquifiers [P : HasChosenEquifiers.{u, v, w} Obj] :
    HasChosenEquifiers.{u, v, w} (Co Obj) where
  equif η θ := equifier (P.equif η θ)

/-- `K^co` has products of size `s` when `K` has. -/
instance hasChosenProductsOfSize [P : HasChosenProductsOfSize.{s, u, v, w} Obj] :
    HasChosenProductsOfSize.{s, u, v, w} (Co Obj) where
  prod c := @product Obj _ _ _ (fun i => unop (c i)) (P.prod (fun i => unop (c i)))

/-- `K^co` is PIE-complete_s when `K` is. -/
instance pieComplete [PIEComplete.{s, u, v, w} Obj] : PIEComplete.{s, u, v, w} (Co Obj) where
  toHasChosenProductsOfSize := inferInstance
  toHasChosenFinProducts := inferInstance
  toHasChosenInserters := inferInstance
  toHasChosenEquifiers := inferInstance

/-- Transporting the chosen equifier object along endpoint equalities and heterogeneous equalities
of the parallel 2-cells. -/
lemma equif_pt_eq_of_heq [HasChosenEquifiers.{u, v, w} Obj]
    {a a' b : Obj} (ha : a = a') {f g : a ⟶ b} {f' g' : a' ⟶ b}
    (hf : HEq f f') (hg : HEq g g') {η θ : f ⟶ g} {η' θ' : f' ⟶ g'}
    (hη : HEq η η') (hθ : HEq θ θ') :
    (HasChosenEquifiers.equif (Obj := Obj) η θ).pt =
      (HasChosenEquifiers.equif (Obj := Obj) η' θ').pt := by
  subst ha; cases eq_of_heq hf; cases eq_of_heq hg
  cases eq_of_heq hη; cases eq_of_heq hθ
  rfl

/-- Transporting the chosen equifier 1-cell `e` along endpoint equalities and heterogeneous
equalities of the parallel 2-cells. -/
lemma equif_e_heq_of_heq [HasChosenEquifiers.{u, v, w} Obj]
    {a a' b : Obj} (ha : a = a') {f g : a ⟶ b} {f' g' : a' ⟶ b}
    (hf : HEq f f') (hg : HEq g g') {η θ : f ⟶ g} {η' θ' : f' ⟶ g'}
    (hη : HEq η η') (hθ : HEq θ θ') :
    HEq (HasChosenEquifiers.equif (Obj := Obj) η θ).e
      (HasChosenEquifiers.equif (Obj := Obj) η' θ').e := by
  subst ha; cases eq_of_heq hf; cases eq_of_heq hg
  cases eq_of_heq hη; cases eq_of_heq hθ
  rfl

/-- A 2-cell in `K` equal to an `eqToHom`-whiskered conjugation of `η'` is heterogeneously equal
to `η'`. -/
lemma cell_heq_of_eqToHom_whiskerLeft
    {a a' b : Obj} (hx : a = a') {f g : a ⟶ b} {f' g' : a' ⟶ b}
    (hf : f = eqToHom hx ≫ f') (hg : g = eqToHom hx ≫ g')
    {η : f ⟶ g} {η' : f' ⟶ g'}
    (hη : η = eqToHom hf ≫ (eqToHom hx ◁ η') ≫ eqToHom hg.symm) :
    HEq η η' := by
  subst hx
  generalize he : eqToHom (rfl : a = a) = id_a at hf hg hη
  rw [eqToHom_refl] at he; subst he
  simp only [Bicategory.Strict.id_comp] at hf hg
  subst hf hg
  have hη' : η = η' := by
    rw [hη, Bicategory.Strict.id_whiskerLeft]
    simp [eqToHom_trans]
  subst hη'
  rfl

/-- A 1-cell `f : a ⟶ b` equal to `eqToHom ha ≫ f'` is heterogeneously equal to `f'`. -/
lemma hom_heq_of_eqToHom_comp {a a' b : Obj} (ha : a = a') {f : a ⟶ b} {f' : a' ⟶ b}
    (hf : f = eqToHom ha ≫ f') : HEq f f' := by
  subst ha; simp only [eqToHom_refl, Bicategory.Strict.id_comp] at hf; subst hf
  rfl

end PIE

end Co

end UlmerBialgebras
