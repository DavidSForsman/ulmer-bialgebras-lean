module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Foundations.CategoryTheory.Bicategory.TwoCategoryData
public import Foundations.CategoryTheory.Bicategory.StrictCoherence
public import Foundations.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Category.Cat
public import Foundations.CategoryTheory.Bicategory.PIE

/-!
# `CAT_V`: the strict 2-category of `V`-enriched categories

*A Syntactic Approach to Ulmer's Bialgebras* works in the 2-category `CAT_V` (written `V-CAT` in
Section 2.1 of the paper) of `V`-enriched categories, `V`-functors and `V`-natural transformations:
for a locally presentable symmetric monoidal closed base `V` in Example 2.3 (2), and for a monoidal
base with an absorbing initial object in Appendix A. This file constructs `CAT_V` as a **strict**
2-category: a Mathlib `Bicategory` with `Bicategory.Strict`.

A `V`-category is taken to be a type `C` equipped with an ordinary category structure and a
`CategoryTheory.EnrichedOrdinaryCategory V C` structure, i.e. an enrichment whose hom-objects
represent the ordinary hom-sets (`eHomEquiv`).  This is no loss of generality: every bare
`EnrichedCategory V C` gives such a structure on the underlying category
`ForgetEnrichment V C`, which has the *same* objects.  Working with the underlying category
in the data makes the 2-cells (`UlmerBialgebras.VNatTrans`) an ordinary family of morphisms subject
to the `V`-naturality square, so that vertical composition, whiskering and the interchange law
are computed as in `CAT`.

* `UlmerBialgebras.VCat V` — the objects: `V`-categories.
* `UlmerBialgebras.VFunctor` — the 1-cells: `V`-functors (an ordinary functor together with the
  action on hom-objects, compatible with `eHomEquiv`).
* `UlmerBialgebras.VNatTrans` — the 2-cells: `V`-natural transformations.
* `UlmerBialgebras.vCatTwoCategory : Bicategory.Strict (VCat V)` — the strict 2-category `CAT_V`.

## Main definitions

* `UlmerBialgebras.VCat`: `V`-categories, the objects of `CAT_V`.
* `UlmerBialgebras.VFunctor`: `V`-functors, the 1-cells.
* `UlmerBialgebras.VNatTrans`: `V`-natural transformations, the 2-cells.
* `UlmerBialgebras.vCatTwoCategory`: `CAT_V` as a strict 2-category (`Bicategory.Strict`).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2.1,
  Example 2.3 (2), Appendix A
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
* [S. Lack, G. Tendas, *Virtual Concepts in the Theory of Accessible Categories*][LACK2023107196]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u u₁ u₂ u₃ u₄

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-! ## Composing generalized elements with the whiskerings -/

section

variable {V}
variable {C : Type u₁} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- **Composing an arbitrary generalized element with a left whiskering.**  This is the
computation rule for `eHomWhiskerLeft`: whatever the source `Z` of the element `u`, composing
with `eHomWhiskerLeft V X g` is tensoring `u` with the name of `g` and composing. -/
lemma comp_eHomWhiskerLeft {Z : V} {X Y Y' : C} (u : Z ⟶ (X ⟶[V] Y)) (g : Y ⟶ Y') :
    u ≫ eHomWhiskerLeft V X g = (ρ_ Z).inv ≫ (u ⊗ₘ eHomEquiv V g) ≫ eComp V X Y Y' := by
  rw [eHomWhiskerLeft, ← Category.assoc, MonoidalCategory.rightUnitor_inv_naturality,
    Category.assoc, MonoidalCategory.tensorHom_def', Category.assoc,
    ← MonoidalCategory.whisker_exchange_assoc]

/-- **Composing an arbitrary generalized element with a right whiskering.** -/
lemma comp_eHomWhiskerRight {Z : V} {X X' Y : C} (u : Z ⟶ (X' ⟶[V] Y)) (f : X ⟶ X') :
    u ≫ eHomWhiskerRight V f Y = (λ_ Z).inv ≫ (eHomEquiv V f ⊗ₘ u) ≫ eComp V X X' Y := by
  rw [eHomWhiskerRight, ← Category.assoc, MonoidalCategory.leftUnitor_inv_naturality,
    Category.assoc, MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.whisker_exchange_assoc]

/-- Composing the name of `f` with the left whiskering by `g` names `f ≫ g`. -/
lemma eHomEquiv_comp_eHomWhiskerLeft {X Y Y' : C} (f : X ⟶ Y) (g : Y ⟶ Y') :
    eHomEquiv V f ≫ eHomWhiskerLeft V X g = eHomEquiv V (f ≫ g) := by
  rw [comp_eHomWhiskerLeft, eHomEquiv_comp, MonoidalCategory.unitors_inv_equal]

/-- Composing the name of `g` with the right whiskering by `f` names `f ≫ g`. -/
lemma eHomEquiv_comp_eHomWhiskerRight {X X' Y : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    eHomEquiv V g ≫ eHomWhiskerRight V f Y = eHomEquiv V (f ≫ g) := by
  rw [comp_eHomWhiskerRight, eHomEquiv_comp]

end

/-! ## `V`-functors -/

/-- A `V`-functor between `V`-categories: an ordinary functor together with a compatible
action on the hom-objects. -/
structure VFunctor (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A]
    (B : Type u₂) [Category.{w} B] [EnrichedOrdinaryCategory V B] where
  /-- The underlying ordinary functor. -/
  toFunctor : A ⥤ B
  /-- The action on hom-objects. -/
  emap : ∀ X Y : A, (X ⟶[V] Y) ⟶ (toFunctor.obj X ⟶[V] toFunctor.obj Y)
  /-- The action on hom-objects is compatible with the enriched composition. -/
  emap_comp : ∀ X Y Z : A,
    eComp V X Y Z ≫ emap X Z
      = (emap X Y ⊗ₘ emap Y Z) ≫ eComp V (toFunctor.obj X) (toFunctor.obj Y) (toFunctor.obj Z)
  /-- The action on hom-objects computes the action of the underlying functor on morphisms. -/
  emap_hom : ∀ {X Y : A} (f : X ⟶ Y),
    eHomEquiv V f ≫ emap X Y = eHomEquiv V (toFunctor.map f)

namespace VFunctor

variable {V}
variable {A : Type u₁} [Category.{w} A] [EnrichedOrdinaryCategory V A]
  {B : Type u₂} [Category.{w} B] [EnrichedOrdinaryCategory V B]
  {C : Type u₃} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The action of a `V`-functor on objects. -/
abbrev obj (F : VFunctor V A B) (X : A) : B := F.toFunctor.obj X

/-- The action of a `V`-functor on morphisms of the underlying categories. -/
abbrev map (F : VFunctor V A B) {X Y : A} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y := F.toFunctor.map f

/-- Extensionality for `V`-functors, with a heterogeneous equality of the hom-object
actions: it suffices to give equal underlying functors and `HEq`-equal actions. -/
lemma extHEq {F G : VFunctor V A B} (hobj : F.toFunctor = G.toFunctor)
    (hmap : ∀ X Y, HEq (F.emap X Y) (G.emap X Y)) : F = G := by
  match F, G with
  | ⟨F, Fe, _, _⟩, ⟨G, Ge, _, _⟩ =>
    obtain rfl : F = G := hobj
    congr 1
    funext X Y
    exact eq_of_heq (hmap X Y)

/-- A `V`-functor preserves enriched identities: `j_X ≫ F_{X,X} = j_{F X}`. -/
@[simp] lemma emap_id (F : VFunctor V A B) (X : A) : eId V X ≫ F.emap X X = eId V (F.obj X) := by
  have := F.emap_hom (𝟙 X)
  simpa using this

/-- Extensionality for `V`-functors: equal underlying functors and hom-object actions that
agree up to the induced `eqToHom` give equal `V`-functors. -/
lemma ext' {F G : VFunctor V A B} (hobj : F.toFunctor = G.toFunctor)
    (hmap : ∀ X Y, F.emap X Y ≫ eqToHom (by rw [hobj]) = G.emap X Y) : F = G := by
  match F, G with
  | ⟨F, Fe, _, _⟩, ⟨G, Ge, _, _⟩ =>
    obtain rfl : F = G := hobj
    congr 1
    funext X Y
    simpa using hmap X Y

/-- A `V`-functor commutes with left whiskering. -/
lemma emap_eHomWhiskerLeft (H : VFunctor V A B) (X : A) {Y Y' : A} (g : Y ⟶ Y') :
    H.emap X Y ≫ eHomWhiskerLeft V (H.obj X) (H.map g)
      = eHomWhiskerLeft V X g ≫ H.emap X Y' := by
  dsimp [eHomWhiskerLeft]
  rw [← H.emap_hom g, Category.assoc, Category.assoc, H.emap_comp X Y Y']
  simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.rightUnitor_inv_naturality_assoc]

/-- A `V`-functor commutes with right whiskering. -/
lemma emap_eHomWhiskerRight (H : VFunctor V A B) {X X' : A} (f : X ⟶ X') (Y : A) :
    H.emap X' Y ≫ eHomWhiskerRight V (H.map f) (H.obj Y)
      = eHomWhiskerRight V f Y ≫ H.emap X Y := by
  dsimp [eHomWhiskerRight]
  rw [← H.emap_hom f, Category.assoc, Category.assoc, H.emap_comp X X' Y]
  simp only [MonoidalCategory.tensorHom_def', MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.leftUnitor_inv_naturality_assoc]

/-- The identity hom actions preserve enriched composition. -/
theorem id_emap_comp (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A]
    (X Y Z : A) :
    eComp V X Y Z ≫ 𝟙 (X ⟶[V] Z) =
      (𝟙 (X ⟶[V] Y) ⊗ₘ 𝟙 (Y ⟶[V] Z)) ≫ eComp V X Y Z := by
  simp

/-- The identity hom actions preserve the enriched representatives of ordinary morphisms. -/
theorem id_emap_hom (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A]
    {X Y : A} (f : X ⟶ Y) : eHomEquiv V f ≫ 𝟙 (X ⟶[V] Y) = eHomEquiv V f := by
  simp

/-- The identity `V`-functor. -/
@[simps]
def id (A : Type u₁) [Category.{w} A] [EnrichedOrdinaryCategory V A] : VFunctor V A A where
  toFunctor := Functor.id A
  emap _ _ := 𝟙 _
  emap_comp := id_emap_comp A
  emap_hom := id_emap_hom A

/-- Composing the hom actions of two enriched functors preserves enriched composition. -/
theorem comp_emap_comp (F : VFunctor V A B) (G : VFunctor V B C) (X Y Z : A) :
    eComp V X Y Z ≫ (F.emap X Z ≫ G.emap _ _) =
      ((F.emap X Y ≫ G.emap _ _) ⊗ₘ (F.emap Y Z ≫ G.emap _ _)) ≫
        eComp V (G.obj (F.obj X)) (G.obj (F.obj Y)) (G.obj (F.obj Z)) := by
  rw [← Category.assoc, F.emap_comp, Category.assoc, G.emap_comp, ← Category.assoc]
  simp

/-- Composing hom actions agrees with the composition of the underlying ordinary functors. -/
theorem comp_emap_hom (F : VFunctor V A B) (G : VFunctor V B C) {X Y : A} (f : X ⟶ Y) :
    eHomEquiv V f ≫ (F.emap X Y ≫ G.emap _ _) =
      eHomEquiv V ((F.toFunctor ⋙ G.toFunctor).map f) := by
  rw [← Category.assoc, F.emap_hom, G.emap_hom, Functor.comp_map]

/-- Composition of `V`-functors, in diagrammatic order. -/
@[simps]
def comp (F : VFunctor V A B) (G : VFunctor V B C) : VFunctor V A C where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  emap X Y := F.emap X Y ≫ G.emap _ _
  emap_comp := comp_emap_comp F G
  emap_hom := comp_emap_hom F G

/-- Left unit law for composition of `V`-functors: `id ∘ F = F`. -/
@[simp] lemma id_comp (F : VFunctor V A B) : (VFunctor.id A).comp F = F := by
  refine ext' rfl ?_
  intro X Y
  change (𝟙 _ ≫ F.emap X Y) ≫ eqToHom rfl = F.emap X Y
  simp

/-- Right unit law for composition of `V`-functors: `F ∘ id = F`. -/
@[simp] lemma comp_id (F : VFunctor V A B) : F.comp (VFunctor.id B) = F := by
  refine ext' rfl ?_
  intro X Y
  change (F.emap X Y ≫ 𝟙 _) ≫ eqToHom rfl = F.emap X Y
  simp

/-- The object component of a composite `V`-functor is the composite of the object
components. -/
lemma comp_obj (F : VFunctor V A B) (G : VFunctor V B C) (X : A) :
    (F.comp G).obj X = G.obj (F.obj X) := rfl

/-- The morphism component of a composite `V`-functor is the composite of the morphism
components. -/
lemma comp_map (F : VFunctor V A B) (G : VFunctor V B C) {X Y : A} (f : X ⟶ Y) :
    (F.comp G).map f = G.map (F.map f) := rfl

/-- Associativity of composition of `V`-functors. -/
lemma comp_assoc {D : Type u₄} [Category.{w} D] [EnrichedOrdinaryCategory V D]
    (F : VFunctor V A B) (G : VFunctor V B C) (H : VFunctor V C D) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  refine ext' rfl ?_
  intro X Y
  simp [comp]

end VFunctor

/-! ## `V`-natural transformations -/

variable {V}

/-- A `V`-natural transformation between `V`-functors: a family of morphisms of the
underlying categories satisfying the enriched naturality square. -/
@[ext]
structure VNatTrans {A : Type u₁} [Category.{w} A] [EnrichedOrdinaryCategory V A]
    {B : Type u₂} [Category.{w} B] [EnrichedOrdinaryCategory V B] (F G : VFunctor V A B) where
  /-- The components. -/
  app : ∀ X : A, F.obj X ⟶ G.obj X
  /-- Enriched naturality. -/
  vnaturality : ∀ X Y : A,
    F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (app Y)
      = G.emap X Y ≫ eHomWhiskerRight V (app X) (G.obj Y)

namespace VNatTrans

variable {A : Type u₁} [Category.{w} A] [EnrichedOrdinaryCategory V A]
  {B : Type u₂} [Category.{w} B] [EnrichedOrdinaryCategory V B]
  {C : Type u₃} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The family of identity morphisms is enriched natural. -/
theorem id_vnaturality (F : VFunctor V A B) (X Y : A) :
    F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (𝟙 (F.obj Y)) =
      F.emap X Y ≫ eHomWhiskerRight V (𝟙 (F.obj X)) (F.obj Y) := by
  simp

/-- The identity `V`-natural transformation. -/
@[simps]
def id (F : VFunctor V A B) : VNatTrans F F where
  app X := 𝟙 (F.obj X)
  vnaturality := id_vnaturality F

/-- The componentwise composite of enriched natural transformations is enriched natural. -/
theorem vcomp_vnaturality {F G H : VFunctor V A B} (α : VNatTrans F G) (β : VNatTrans G H)
    (X Y : A) :
    F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (α.app Y ≫ β.app Y) =
      H.emap X Y ≫ eHomWhiskerRight V (α.app X ≫ β.app X) (H.obj Y) := by
  rw [eHomWhiskerLeft_comp, ← Category.assoc, α.vnaturality, Category.assoc,
    ← eHom_whisker_exchange, ← Category.assoc, β.vnaturality, Category.assoc,
    ← eHomWhiskerRight_comp]

/-- Vertical composition of `V`-natural transformations. -/
@[simps]
def vcomp {F G H : VFunctor V A B} (α : VNatTrans F G) (β : VNatTrans G H) : VNatTrans F H where
  app X := α.app X ≫ β.app X
  vnaturality := vcomp_vnaturality α β

/-- A `V`-natural transformation is in particular a natural transformation of the underlying
functors. -/
lemma naturality {F G : VFunctor V A B} (α : VNatTrans F G) {X Y : A} (f : X ⟶ Y) :
    F.map f ≫ α.app Y = α.app X ≫ G.map f := by
  apply (eHomEquiv V).injective
  have h := congrArg (fun t => eHomEquiv V f ≫ t) (α.vnaturality X Y)
  simp only [← Category.assoc, F.emap_hom, G.emap_hom] at h
  rw [← eHomEquiv_comp_eHomWhiskerLeft, ← eHomEquiv_comp_eHomWhiskerRight]
  exact h

/-- Two `V`-natural transformations between (possibly different but equal) `V`-functors are
heterogeneously equal as soon as their components are. -/
lemma heq_of_app_heq {F F' G G' : VFunctor V A B} (hF : F = F') (hG : G = G')
    {α : VNatTrans F G} {β : VNatTrans F' G'} (h : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  subst hF; subst hG
  exact heq_of_eq (VNatTrans.ext (funext fun X => eq_of_heq (h X)))

/-- Precomposition by an enriched functor preserves enriched naturality. -/
theorem whiskerL_vnaturality (H : VFunctor V C A) {F G : VFunctor V A B} (α : VNatTrans F G)
    (X Y : C) :
    (H.emap X Y ≫ F.emap _ _) ≫ eHomWhiskerLeft V (F.obj (H.obj X)) (α.app (H.obj Y)) =
      (H.emap X Y ≫ G.emap _ _) ≫ eHomWhiskerRight V (α.app (H.obj X)) (G.obj (H.obj Y)) := by
  rw [Category.assoc, Category.assoc, α.vnaturality]

/-- Whiskering a `V`-natural transformation by a `V`-functor on the source side. -/
@[simps]
def whiskerL (H : VFunctor V C A) {F G : VFunctor V A B} (α : VNatTrans F G) :
    VNatTrans (H.comp F) (H.comp G) where
  app X := α.app (H.obj X)
  vnaturality := whiskerL_vnaturality H α

/-- Postcomposition by an enriched functor preserves enriched naturality. -/
theorem whiskerR_vnaturality {F G : VFunctor V A B} (α : VNatTrans F G) (H : VFunctor V B C)
    (X Y : A) :
    (F.emap X Y ≫ H.emap _ _) ≫ eHomWhiskerLeft V (H.obj (F.obj X)) (H.map (α.app Y)) =
      (G.emap X Y ≫ H.emap _ _) ≫ eHomWhiskerRight V (H.map (α.app X)) (H.obj (G.obj Y)) := by
  rw [Category.assoc, Category.assoc, H.emap_eHomWhiskerLeft, H.emap_eHomWhiskerRight,
    ← Category.assoc, ← Category.assoc, α.vnaturality]

/-- Whiskering a `V`-natural transformation by a `V`-functor on the target side. -/
@[simps]
def whiskerR {F G : VFunctor V A B} (α : VNatTrans F G) (H : VFunctor V B C) :
    VNatTrans (F.comp H) (G.comp H) where
  app X := H.map (α.app X)
  vnaturality := whiskerR_vnaturality α H

/-- Left unit law for vertical composition. -/
theorem id_vcomp {F G : VFunctor V A B} (α : VNatTrans F G) : (id F).vcomp α = α := by
  ext X
  simp [vcomp]

/-- Right unit law for vertical composition. -/
theorem vcomp_id {F G : VFunctor V A B} (α : VNatTrans F G) : α.vcomp (id G) = α := by
  ext X
  simp [vcomp]

/-- Vertical composition is associative. -/
theorem vcomp_assoc {F G H K : VFunctor V A B}
    (α : VNatTrans F G) (β : VNatTrans G H) (γ : VNatTrans H K) :
    (α.vcomp β).vcomp γ = α.vcomp (β.vcomp γ) := by
  ext X
  simp [vcomp]

/-- Whiskering on the target side preserves the identity transformation. -/
theorem whiskerR_id (F : VFunctor V A B) (G : VFunctor V B C) :
    whiskerR (id F) G = id (F.comp G) := by
  ext X
  exact G.toFunctor.map_id _

/-- Whiskering on the source side preserves vertical composition. -/
theorem whiskerL_vcomp (H : VFunctor V C A) {F G K : VFunctor V A B}
    (α : VNatTrans F G) (β : VNatTrans G K) :
    whiskerL H (α.vcomp β) = (whiskerL H α).vcomp (whiskerL H β) := by
  ext X
  rfl

/-- Whiskering on the target side preserves vertical composition. -/
theorem whiskerR_vcomp {F G H : VFunctor V A B} (α : VNatTrans F G) (β : VNatTrans G H)
    (K : VFunctor V B C) : whiskerR (α.vcomp β) K = (whiskerR α K).vcomp (whiskerR β K) := by
  ext X
  exact K.toFunctor.map_comp _ _

/-- The interchange law for whiskered enriched natural transformations. -/
theorem interchange {F G : VFunctor V A B} {H K : VFunctor V B C}
    (α : VNatTrans F G) (β : VNatTrans H K) :
    (whiskerR α H).vcomp (whiskerL G β) = (whiskerL F β).vcomp (whiskerR α K) := by
  ext X
  exact β.naturality (α.app X)

/-- Whiskering by the identity functor on the source side is the identity. -/
theorem whiskerL_id_functor {F G : VFunctor V A B} (α : VNatTrans F G) :
    HEq (whiskerL (VFunctor.id A) α) α :=
  heq_of_app_heq (VFunctor.id_comp _) (VFunctor.id_comp _) (fun _ => HEq.rfl)

/-- Whiskering by the identity functor on the target side is the identity. -/
theorem whiskerR_id_functor {F G : VFunctor V A B} (α : VNatTrans F G) :
    HEq (whiskerR α (VFunctor.id B)) α :=
  heq_of_app_heq (VFunctor.comp_id _) (VFunctor.comp_id _) (fun _ => HEq.rfl)

variable {D : Type u₄} [Category.{w} D] [EnrichedOrdinaryCategory V D]

/-- Whiskering on the source side by a composite is successive whiskering. -/
theorem whiskerL_comp_functor (F : VFunctor V A B) (G : VFunctor V B C)
    {H K : VFunctor V C D} (α : VNatTrans H K) :
    HEq (whiskerL (F.comp G) α) (whiskerL F (whiskerL G α)) :=
  heq_of_app_heq (VFunctor.comp_assoc _ _ _) (VFunctor.comp_assoc _ _ _) (fun _ => HEq.rfl)

/-- Whiskering on the target side by a composite is successive whiskering. -/
theorem whiskerR_comp_functor {F G : VFunctor V A B} (α : VNatTrans F G)
    (H : VFunctor V B C) (K : VFunctor V C D) :
    HEq (whiskerR α (H.comp K)) (whiskerR (whiskerR α H) K) :=
  heq_of_app_heq (VFunctor.comp_assoc _ _ _).symm (VFunctor.comp_assoc _ _ _).symm
    (fun _ => HEq.rfl)

/-- Whiskerings on the two sides commute up to reassociation. -/
theorem whisker_left_right (F : VFunctor V A B) {G H : VFunctor V B C}
    (α : VNatTrans G H) (K : VFunctor V C D) :
    HEq (whiskerL F (whiskerR α K)) (whiskerR (whiskerL F α) K) :=
  heq_of_app_heq (VFunctor.comp_assoc _ _ _).symm (VFunctor.comp_assoc _ _ _).symm
    (fun _ => HEq.rfl)

end VNatTrans

/-! ## The 2-category `CAT_V` -/

variable (V)

/-- A `V`-category: a type with an ordinary category structure and a compatible enrichment
in `V`. -/
structure VCat where
  /-- The type of objects. -/
  carrier : Type u
  [cat : Category.{w} carrier]
  [enr : EnrichedOrdinaryCategory V carrier]

namespace VCat

/-- An object of `CAT_V` coerces to its type of objects. -/
instance : CoeSort (VCat.{w, v, u} V) (Type u) := ⟨VCat.carrier⟩

attribute [instance] VCat.cat VCat.enr

variable {V}

/-- Bundle a `V`-category. -/
abbrev of (C : Type u) [Category.{w} C] [EnrichedOrdinaryCategory V C] : VCat.{w, v, u} V :=
  ⟨C⟩

end VCat

variable {V}

/-- **`CAT_V` is a strict 2-category**: `V`-categories, `V`-functors and `V`-natural
transformations. -/
abbrev vCatTwoCategoryData : TwoCategoryData (VCat.{w, v, u} V) where
  Hom A B := VFunctor V A.carrier B.carrier
  Cell F G := VNatTrans F G
  id₁ A := VFunctor.id A.carrier
  comp₁ F G := F.comp G
  id₁_comp₁ := VFunctor.id_comp
  comp₁_id₁ := VFunctor.comp_id
  assoc₁ := VFunctor.comp_assoc
  id₂ F := VNatTrans.id F
  vcomp α β := α.vcomp β
  id₂_vcomp := VNatTrans.id_vcomp
  vcomp_id₂ := VNatTrans.vcomp_id
  vcomp_assoc := VNatTrans.vcomp_assoc
  whiskerL := fun {_ _ _} H {_ _} α => VNatTrans.whiskerL H α
  whiskerR := fun {_ _ _} {_ _} α H => VNatTrans.whiskerR α H
  whiskerL_id₂ _ _ := rfl
  whiskerR_id₂ := VNatTrans.whiskerR_id
  whiskerL_vcomp := VNatTrans.whiskerL_vcomp
  whiskerR_vcomp := VNatTrans.whiskerR_vcomp
  interchange := VNatTrans.interchange
  whiskerL_id₁ := VNatTrans.whiskerL_id_functor
  whiskerR_id₁ := VNatTrans.whiskerR_id_functor
  whiskerL_comp₁ := VNatTrans.whiskerL_comp_functor
  whiskerR_comp₁ := VNatTrans.whiskerR_comp_functor
  whisker_mid := VNatTrans.whisker_left_right

/-- The bicategory structure on enriched ordinary categories. -/
instance vCatBicategory : CategoryTheory.Bicategory (VCat.{w, v, u} V) :=
  (vCatTwoCategoryData (V := V)).toBicategory

/-- Enriched ordinary categories form a strict 2-category. -/
instance vCatTwoCategory : CategoryTheory.Bicategory.Strict (VCat.{w, v, u} V) :=
  (vCatTwoCategoryData (V := V)).strict

section Components

variable {A B C : VCat.{w, v, u} V}

/-- The identity 2-cell of `CAT_V` has identity components. -/
@[simp] lemma vCat_id₂_app (F : A ⟶ B) (X : A) : (𝟙 F : VNatTrans F F).app X = 𝟙 _ := rfl

/-- Vertical composition of 2-cells in `CAT_V` is computed componentwise. -/
@[simp] lemma vCat_vcomp_app {F G H : A ⟶ B} (α : F ⟶ G) (β : G ⟶ H) (X : A) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl
/-- Components of a left whiskering `H ◁ α` in `CAT_V`: `(H ◁ α)_X = α_{H X}`. -/
@[simp] lemma vCat_whiskerLeft_app (H : C ⟶ A) {F G : A ⟶ B} (α : F ⟶ G) (X : C) :
    (H ◁ α).app X = α.app (H.obj X) := rfl

/-- Components of a right whiskering `α ▷ H` in `CAT_V`: `(α ▷ H)_X = H(α_X)`. -/
@[simp] lemma vCat_whiskerRight_app {F G : A ⟶ B} (α : F ⟶ G) (H : B ⟶ C) (X : A) :
    (α ▷ H).app X = H.map (α.app X) := rfl


end Components

/-- The components of an identity 2-cell of `CAT_V` coming from an equality of
`V`-functors. -/
lemma VNatTrans.eqToHom_app {A B : VCat.{w, v, u} V} {F F' : A ⟶ B} (p : F = F') (X : A) :
    (eqToHom p : VNatTrans F F').app X = eqToHom (by rw [p]) := by
  subst p; rfl

/-- Composition of 1-cells in `CAT_V` is composition of `V`-functors. -/
@[simp] lemma vCat_comp₁_eq {A B C : VCat.{w, v, u} V} (F : A ⟶ B) (G : B ⟶ C) :
    F ≫ G = F.comp G := rfl

end UlmerBialgebras
