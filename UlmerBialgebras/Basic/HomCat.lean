module

public import UlmerBialgebras.Basic.PIE
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Hom-categories of a 2-category and the representable comparison equivalences

For Section 7 of *A Syntactic Approach to Ulmer's Bialgebras* we need the functors
between hom-categories of a strict 2-category induced by pre- and post-composition, and
the comparison between the hom-category of a PIE limit and the corresponding PIE limit of
hom-categories:

* `UlmerBialgebras.precomp f c : (y ⟶ c) ⥤ (x ⟶ c)` for `f : x ⟶ y` and
  `UlmerBialgebras.postcomp x u : (x ⟶ c) ⥤ (x ⟶ d)` for `u : c ⟶ d`;
* `UlmerBialgebras.Product.homEquiv P x : (x ⟶ P.pt) ≌ ∀ i, (x ⟶ c i)`;
* `UlmerBialgebras.Inserter.homEquiv I x : (x ⟶ I.pt) ≌ Ins (postcomp x f) (postcomp x g)`;
* `UlmerBialgebras.Equifier.homEquiv E x : (x ⟶ E.pt) ≌ Equif (postcompNat x η) (postcompNat x θ)`.

Each comparison is the functor given by composing with the canonical 1-cell out of the PIE
limit; the strict universal properties of `UlmerBialgebras.Product`, `UlmerBialgebras.Inserter` and
`UlmerBialgebras.Equifier` say precisely that these functors are full, faithful and (strictly)
essentially surjective.

This is the statement, made after Remark 2.2, that the representable 2-functors `K(x, -)`
preserve and jointly reflect PIE limits.

## Main results

* `UlmerBialgebras.precomp`, `UlmerBialgebras.postcomp`: the functors between hom-categories given
  by pre- and post-composition.
* `UlmerBialgebras.Product.homEquiv`: the equivalence `(x ⟶ P.pt) ≌ ∀ i, (x ⟶ c i)`.
* `UlmerBialgebras.Inserter.homEquiv`: the equivalence
  `(x ⟶ I.pt) ≌ Ins (postcomp x f) (postcomp x g)`.
* `UlmerBialgebras.Equifier.homEquiv`: the equivalence
  `(x ⟶ E.pt) ≌ Equif (postcompNat x η) (postcompNat x θ)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 2.1, Remark 2.2 and Section 7
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w s

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Pre- and post-composition functors -/

/-- Pre-composition with `f : x ⟶ y` as a functor `K(y, c) ⥤ K(x, c)`. -/
@[simps, implicit_reducible]
def precomp {x y : Obj} (f : x ⟶ y) (c : Obj) : (y ⟶ c) ⥤ (x ⟶ c) where
  obj h := f ≫ h
  map α := f ◁ α

/-- Post-composition with `u : c ⟶ d` as a functor `K(x, c) ⥤ K(x, d)`. -/
@[simps, implicit_reducible]
def postcomp (x : Obj) {c d : Obj} (u : c ⟶ d) : (x ⟶ c) ⥤ (x ⟶ d) where
  obj h := h ≫ u
  map α := α ▷ u

/-- Post-composition with a 2-cell `η : f ⟶ g` as a natural transformation between the
post-composition functors. -/
@[simps]
def postcompNat (x : Obj) {a b : Obj} {f g : a ⟶ b} (η : f ⟶ g) :
    postcomp x f ⟶ postcomp x g where
  app h := h ◁ η
  naturality _ _ α := Eq.symm <| Bicategory.whisker_exchange α η

/-! ## Products -/

namespace Product

variable {ι : Type s} {c : ι → Obj} (P : Product c) (x : Obj)

/-- The comparison functor `K(x, ∏ cᵢ) ⥤ ∏ K(x, cᵢ)`. -/
@[simps]
def homFunctor : (x ⟶ P.pt) ⥤ (∀ i, (x ⟶ c i)) where
  obj h i := h ≫ P.π i
  map α i := α ▷ P.π i
  map_id h := by funext i; exact Bicategory.id_whiskerRight h (P.π i)
  map_comp α β := by funext i; exact Bicategory.comp_whiskerRight α β (P.π i)

/-- The comparison functor `K(x, ∏ cᵢ) ⥤ ∏ K(x, cᵢ)` is faithful. -/
instance : (homFunctor P x).Faithful where
  map_injective h := P.cell_ext (funext_iff.mp h)

/-- The comparison functor `K(x, ∏ cᵢ) ⥤ ∏ K(x, cᵢ)` is full. -/
instance : (homFunctor P x).Full where
  map_surjective {g h} γ := ⟨P.lift₂ fun i => γ i, by funext i; exact P.lift₂_π _ i⟩

/-- The comparison functor `K(x, ∏ cᵢ) ⥤ ∏ K(x, cᵢ)` is essentially surjective. -/
instance : (homFunctor P x).EssSurj where
  mem_essImage k :=
    ⟨P.lift k, ⟨eqToIso (funext fun i => P.lift_π k i)⟩⟩

/-- The comparison functor `K(x, ∏ cᵢ) ⥤ ∏ K(x, cᵢ)` is an equivalence. -/
instance : (homFunctor P x).IsEquivalence where

/-- The comparison equivalence `K(x, ∏ cᵢ) ≌ ∏ K(x, cᵢ)`. -/
noncomputable def homEquiv : (x ⟶ P.pt) ≌ (∀ i, (x ⟶ c i)) :=
  (homFunctor P x).asEquivalence

end Product

/-! ## Inserters -/

namespace Inserter

variable {a b : Obj} {f g : a ⟶ b} (I : Inserter f g) (x : Obj)

/-- The structure 2-cell of the inserter, transported to the hom-category. -/
def homCell (k : x ⟶ I.pt) :
    (postcomp x f).obj (k ≫ I.u) ⟶ (postcomp x g).obj (k ≫ I.u) :=
  eqToHom (Category.assoc k I.u f) ≫ (k ◁ I.φ) ≫ eqToHom (Category.assoc k I.u g).symm

/-- Naturality in `k` of the 2-cell `eqToHom ≫ k ◁ φ ≫ eqToHom` transported from a cone
`(u, φ : u ≫ f ⟶ u ≫ g)` over `f, g` to the hom-category: it commutes with the whiskered
2-cells `α ▷ u`. -/
lemma cell_naturality {pt : Obj} (u : pt ⟶ a) (φ : u ≫ f ⟶ u ≫ g) {k k' : x ⟶ pt}
    (α : k ⟶ k') :
    (eqToHom (Category.assoc k u f) ≫ (k ◁ φ) ≫ eqToHom (Category.assoc k u g).symm) ≫
        (postcomp x g).map (α ▷ u)
      = (postcomp x f).map (α ▷ u) ≫
        (eqToHom (Category.assoc k' u f) ≫ (k' ◁ φ) ≫ eqToHom (Category.assoc k' u g).symm) := by
  have hex : α ▷ (u ≫ f) ≫ k' ◁ φ = k ◁ φ ≫ α ▷ (u ≫ g) :=
    Eq.symm <| Bicategory.whisker_exchange α φ
  have e1 : (α ▷ u) ▷ f
      = eqToHom (Category.assoc k u f) ≫ (α ▷ (u ≫ f)) ≫
        eqToHom (Category.assoc k' u f).symm := by
    rw [Bicategory.Strict.whiskerRight_comp]; simp
  have e2 : (α ▷ u) ▷ g
      = eqToHom (Category.assoc k u g) ≫ (α ▷ (u ≫ g)) ≫
        eqToHom (Category.assoc k' u g).symm := by
    rw [Bicategory.Strict.whiskerRight_comp]; simp
  simp only [postcomp_map, e1, e2, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have key : k ◁ φ ≫ α ▷ (u ≫ g) ≫ eqToHom (Category.assoc k' u g).symm
      = α ▷ (u ≫ f) ≫ k' ◁ φ ≫ eqToHom (Category.assoc k' u g).symm := by
    rw [← Category.assoc (obj := _ ⟶ _), ← hex, Category.assoc (obj := _ ⟶ _)]
  rw [key]

/-- The 2-cells `homCell I x k` are natural in `k`, so that they form an object of the
inserter of `f ∘ -` and `g ∘ -`. -/
lemma homCell_naturality {k k' : x ⟶ I.pt} (α : k ⟶ k') :
    homCell I x k ≫ (postcomp x g).map (α ▷ I.u)
      = (postcomp x f).map (α ▷ I.u) ≫ homCell I x k' :=
  cell_naturality x I.u I.φ α

/-- The comparison functor `K(x, Ins(f, g)) ⥤ Ins(f ∘ -, g ∘ -)`. -/
@[simps]
def homFunctor : (x ⟶ I.pt) ⥤ Ins (postcomp x f) (postcomp x g) where
  obj k := ⟨k ≫ I.u, homCell I x k⟩
  map α := ⟨α ▷ I.u, homCell_naturality I x α⟩
  map_id k := by ext; exact Bicategory.id_whiskerRight k I.u
  map_comp α β := by ext; exact Bicategory.comp_whiskerRight α β I.u

/-- The comparison functor `K(x, Ins(f, g)) ⥤ Ins(f ∘ -, g ∘ -)` is faithful. -/
instance : (homFunctor I x).Faithful where
  map_injective h := I.lift₂_uniq _ _ (Ins.Hom.ext_iff.mp h)

/-- The comparison functor `K(x, Ins(f, g)) ⥤ Ins(f ∘ -, g ∘ -)` is full. -/
instance : (homFunctor I x).Full where
  map_surjective {k k'} β := by
    refine ⟨I.lift₂ β.base β.w, ?_⟩
    ext
    exact I.lift₂_u β.base _

/-- The comparison functor `K(x, Ins(f, g)) ⥤ Ins(f ∘ -, g ∘ -)` is essentially surjective. -/
instance : (homFunctor I x).EssSurj where
  mem_essImage y := by
    refine ⟨I.lift y.pt y.cell, ⟨eqToIso ?_⟩⟩
    refine Ins.obj_ext (I.lift_u y.pt y.cell) ?_
    rw [homFunctor_obj_cell, homCell, I.lift_φ y.pt y.cell]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    congr 1

/-- The comparison functor `K(x, Ins(f, g)) ⥤ Ins(f ∘ -, g ∘ -)` is an equivalence. -/
instance : (homFunctor I x).IsEquivalence where

/-- The comparison equivalence `K(x, Ins(f, g)) ≌ Ins(f ∘ -, g ∘ -)`. -/
noncomputable def homEquiv : (x ⟶ I.pt) ≌ Ins (postcomp x f) (postcomp x g) :=
  (homFunctor I x).asEquivalence

end Inserter

/-! ## Equifiers -/

namespace Equifier

variable {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ) (x : Obj)

/-- For a cone `e` with `e ◁ η = e ◁ θ`, each composite `k ≫ e` lies in the equifier of
`η ∘ -` and `θ ∘ -`. -/
lemma equifProp_comp {pt : Obj} (e : pt ⟶ a) (hcond : e ◁ η = e ◁ θ) (k : x ⟶ pt) :
    equifProp (postcompNat x η) (postcompNat x θ) (k ≫ e) := by
  change (k ≫ e) ◁ η = (k ≫ e) ◁ θ
  rw [Bicategory.Strict.comp_whiskerLeft k e η, Bicategory.Strict.comp_whiskerLeft k e θ, hcond]

/-- For `k : x ⟶ Eq(η, θ)`, the composite `k ≫ e` lies in the equifier of `η ∘ -` and
`θ ∘ -`. -/
lemma homProp (k : x ⟶ E.pt) :
    equifProp (postcompNat x η) (postcompNat x θ) (k ≫ E.e) :=
  equifProp_comp x E.e E.cond k

/-- The comparison functor `K(x, Eq(η, θ)) ⥤ Eq(η ∘ -, θ ∘ -)`. -/
@[simps]
def homFunctor : (x ⟶ E.pt) ⥤ Equif (postcompNat x η) (postcompNat x θ) where
  obj k := ⟨k ≫ E.e, homProp E x k⟩
  map α := ObjectProperty.homMk (α ▷ E.e)
  map_id k := by ext; exact Bicategory.id_whiskerRight k E.e
  map_comp α β := by ext; exact Bicategory.comp_whiskerRight α β E.e

/-- The comparison functor `K(x, Eq(η, θ)) ⥤ Eq(η ∘ -, θ ∘ -)` is faithful. -/
instance : (homFunctor E x).Faithful where
  map_injective h := E.faithful _ _ ((Equif.forget _ _).congr_map h)

/-- The comparison functor `K(x, Eq(η, θ)) ⥤ Eq(η ∘ -, θ ∘ -)` is full. -/
instance : (homFunctor E x).Full where
  map_surjective {k k'} β := by
    obtain ⟨α, hα⟩ := E.full β.hom
    exact ⟨α, by ext; exact hα⟩

/-- The comparison functor `K(x, Eq(η, θ)) ⥤ Eq(η ∘ -, θ ∘ -)` is essentially surjective. -/
instance : (homFunctor E x).EssSurj where
  mem_essImage y := by
    refine ⟨E.lift y.obj y.property, ⟨eqToIso ?_⟩⟩
    exact ObjectProperty.FullSubcategory.ext (E.lift_e y.obj y.property)

/-- The comparison functor `K(x, Eq(η, θ)) ⥤ Eq(η ∘ -, θ ∘ -)` is an equivalence. -/
instance : (homFunctor E x).IsEquivalence where

/-- The comparison equivalence `K(x, Eq(η, θ)) ≌ Eq(η ∘ -, θ ∘ -)`. -/
noncomputable def homEquiv : (x ⟶ E.pt) ≌ Equif (postcompNat x η) (postcompNat x θ) :=
  (homFunctor E x).asEquivalence

end Equifier

end UlmerBialgebras
