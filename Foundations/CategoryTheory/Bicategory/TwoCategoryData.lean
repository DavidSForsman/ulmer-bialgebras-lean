module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic

/-!
# Strict bicategories from 2-category data

A field-wise strict 2-category determines a Mathlib bicategory with strict associators and unitors.
This construction is explicit and installs no global instances.

## Main results

* `UlmerBialgebras.TwoCategoryData.toBicategory`: the associated bicategory.
* `UlmerBialgebras.TwoCategoryData.strict`: its strictness.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-- Turning a heterogeneous equality of morphisms into an equation involving `eqToHom`. -/
lemma twoCategoryData_eq_of_heq_hom {C : Type*} [Category C] {X Y X' Y' : C}
    (hX : X = X') (hY : Y = Y')
    (x : X ⟶ Y) (y : X' ⟶ Y') (h : HEq x y) : x = eqToHom hX ≫ y ≫ eqToHom hY.symm := by
  subst hX; subst hY; simp [eq_of_heq h]

/-- A field-by-field presentation of a strict 2-category, used to build
`Bicategory` + `Bicategory.Strict` instances (`TwoCategoryData.toBicategory`). -/
structure TwoCategoryData (Obj : Type u) where
  /-- The type of 1-cells. -/
  Hom : Obj → Obj → Type v
  /-- The type of 2-cells between two parallel 1-cells. -/
  Cell : ∀ {a b : Obj}, Hom a b → Hom a b → Type w
  /-- The identity 1-cell. -/
  id₁ : ∀ a : Obj, Hom a a
  /-- Composition of 1-cells, in diagrammatic order. -/
  comp₁ : ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
  id₁_comp₁ : ∀ {a b : Obj} (f : Hom a b), comp₁ (id₁ a) f = f
  comp₁_id₁ : ∀ {a b : Obj} (f : Hom a b), comp₁ f (id₁ b) = f
  assoc₁ : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
      comp₁ (comp₁ f g) h = comp₁ f (comp₁ g h)
  /-- The identity 2-cell. -/
  id₂ : ∀ {a b : Obj} (f : Hom a b), Cell f f
  /-- Vertical composition of 2-cells. -/
  vcomp : ∀ {a b : Obj} {f g h : Hom a b}, Cell f g → Cell g h → Cell f h
  id₂_vcomp : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), vcomp (id₂ f) α = α
  vcomp_id₂ : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), vcomp α (id₂ g) = α
  vcomp_assoc : ∀ {a b : Obj} {f g h k : Hom a b} (α : Cell f g) (β : Cell g h) (γ : Cell h k),
      vcomp (vcomp α β) γ = vcomp α (vcomp β γ)
  /-- Whiskering a 2-cell by a 1-cell on the source side. -/
  whiskerL : ∀ {a b c : Obj} (f : Hom a b) {g h : Hom b c},
      Cell g h → Cell (comp₁ f g) (comp₁ f h)
  /-- Whiskering a 2-cell by a 1-cell on the target side. -/
  whiskerR : ∀ {a b c : Obj} {f g : Hom a b}, Cell f g → ∀ h : Hom b c,
      Cell (comp₁ f h) (comp₁ g h)
  whiskerL_id₂ : ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
      whiskerL f (id₂ g) = id₂ (comp₁ f g)
  whiskerR_id₂ : ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
      whiskerR (id₂ f) g = id₂ (comp₁ f g)
  whiskerL_vcomp : ∀ {a b c : Obj} (f : Hom a b) {g h k : Hom b c} (α : Cell g h)
      (β : Cell h k), whiskerL f (vcomp α β) = vcomp (whiskerL f α) (whiskerL f β)
  whiskerR_vcomp : ∀ {a b c : Obj} {f g h : Hom a b} (α : Cell f g) (β : Cell g h)
      (k : Hom b c), whiskerR (vcomp α β) k = vcomp (whiskerR α k) (whiskerR β k)
  /-- The interchange law. -/
  interchange : ∀ {a b c : Obj} {f g : Hom a b} {h k : Hom b c} (α : Cell f g) (β : Cell h k),
      vcomp (whiskerR α h) (whiskerL g β) = vcomp (whiskerL f β) (whiskerR α k)
  whiskerL_id₁ : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), HEq (whiskerL (id₁ a) α) α
  whiskerR_id₁ : ∀ {a b : Obj} {f g : Hom a b} (α : Cell f g), HEq (whiskerR α (id₁ b)) α
  whiskerL_comp₁ : ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) {h k : Hom c d}
      (α : Cell h k), HEq (whiskerL (comp₁ f g) α) (whiskerL f (whiskerL g α))
  whiskerR_comp₁ : ∀ {a b c d : Obj} {f g : Hom a b} (α : Cell f g) (h : Hom b c)
      (k : Hom c d), HEq (whiskerR α (comp₁ h k)) (whiskerR (whiskerR α h) k)
  whisker_mid : ∀ {a b c d : Obj} (f : Hom a b) {g h : Hom b c} (α : Cell g h)
      (k : Hom c d), HEq (whiskerL f (whiskerR α k)) (whiskerR (whiskerL f α) k)


namespace TwoCategoryData

variable {Obj : Type u} (D : TwoCategoryData.{u, v, w} Obj)

/-- The hom-categories of a presented strict 2-category. -/
@[reducible] def homCat (a b : Obj) : Category.{w} (D.Hom a b) where
  Hom f g := D.Cell f g
  id := D.id₂
  comp := D.vcomp
  id_comp := D.id₂_vcomp
  comp_id := D.vcomp_id₂
  assoc := D.vcomp_assoc

attribute [local instance] homCat

/-- Left whiskering of an `eqToHom` in a `TwoCategoryData` is an `eqToHom`. -/
lemma toBicategory_whiskerL_eqToHom {a b c : Obj} (f : D.Hom a b)
    {g h : D.Hom b c} (e : g = h) :
    D.whiskerL f (eqToHom e) = eqToHom (congrArg (D.comp₁ f) e) := by
  subst_vars; exact D.whiskerL_id₂ _ _

/-- Right whiskering of an `eqToHom` in a `TwoCategoryData` is an `eqToHom`. -/
lemma toBicategory_whiskerR_eqToHom {a b c : Obj} {f g : D.Hom a b}
    (e : f = g) (h : D.Hom b c) :
    D.whiskerR (eqToHom e) h = eqToHom (congrArg (D.comp₁ · h) e) := by
  subst_vars; exact D.whiskerR_id₂ _ _

/-- Pentagon coherence for `TwoCategoryData.toBicategory`. -/
lemma toBicategory_pentagon {a b c d e : Obj}
    (f : D.Hom a b) (g : D.Hom b c) (h : D.Hom c d) (i : D.Hom d e) :
    D.whiskerR (eqToHom (D.assoc₁ f g h)) i ≫ eqToHom (D.assoc₁ f (D.comp₁ g h) i) ≫
        D.whiskerL f (eqToHom (D.assoc₁ g h i))
      = eqToHom (D.assoc₁ (D.comp₁ f g) h i) ≫ eqToHom (D.assoc₁ f g (D.comp₁ h i)) := by
  simp [toBicategory_whiskerL_eqToHom, toBicategory_whiskerR_eqToHom]

/-- Triangle coherence for `TwoCategoryData.toBicategory`. -/
lemma toBicategory_triangle {a b c : Obj} (f : D.Hom a b) (g : D.Hom b c) :
    eqToHom (D.assoc₁ f (D.id₁ _) g) ≫ D.whiskerL f (eqToHom (D.id₁_comp₁ g))
      = D.whiskerR (eqToHom (D.comp₁_id₁ f)) g := by
  simp [toBicategory_whiskerL_eqToHom, toBicategory_whiskerR_eqToHom]

/-- The bicategory of a strict 2-category presented by its fields; associators and unitors
are `eqToIso`. -/
@[reducible] def toBicategory : Bicategory.{w, v} Obj where
  Hom := D.Hom
  id := D.id₁
  comp := D.comp₁
  homCategory a b := D.homCat a b
  whiskerLeft f _ _ η := D.whiskerL f η
  whiskerRight η h := D.whiskerR η h
  associator f g h := eqToIso (D.assoc₁ f g h)
  leftUnitor f := eqToIso (D.id₁_comp₁ f)
  rightUnitor f := eqToIso (D.comp₁_id₁ f)
  whiskerLeft_id := D.whiskerL_id₂
  whiskerLeft_comp := D.whiskerL_vcomp
  id_whiskerLeft {_ _ f g} η :=
    twoCategoryData_eq_of_heq_hom (D.id₁_comp₁ f) (D.id₁_comp₁ g) _ _ (D.whiskerL_id₁ η)
  comp_whiskerLeft {_ _ _ _} f g {h k} η :=
    twoCategoryData_eq_of_heq_hom (D.assoc₁ f g h) (D.assoc₁ f g k) _ _
      (D.whiskerL_comp₁ f g η)
  id_whiskerRight := D.whiskerR_id₂
  comp_whiskerRight η θ i := D.whiskerR_vcomp η θ i
  whiskerRight_id {_ _ f g} η :=
    twoCategoryData_eq_of_heq_hom (D.comp₁_id₁ f) (D.comp₁_id₁ g) _ _ (D.whiskerR_id₁ η)
  whiskerRight_comp {_ _ _ _ f f'} η g h :=
    twoCategoryData_eq_of_heq_hom (D.assoc₁ f g h).symm (D.assoc₁ f' g h).symm _ _
      (D.whiskerR_comp₁ η g h)
  whisker_assoc {_ _ _ _} f {g g'} η h :=
    twoCategoryData_eq_of_heq_hom (D.assoc₁ f g h) (D.assoc₁ f g' h) _ _
      (D.whisker_mid f η h).symm
  whisker_exchange η θ := (D.interchange η θ).symm
  pentagon {_ _ _ _ _} f g h i := toBicategory_pentagon D f g h i
  triangle {_ _ _} f g := toBicategory_triangle D f g

/-- A presented strict 2-category is a strict bicategory. -/
theorem strict : @Bicategory.Strict Obj D.toBicategory :=
  @Bicategory.Strict.mk Obj D.toBicategory D.id₁_comp₁ D.comp₁_id₁ D.assoc₁
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)

end TwoCategoryData

end UlmerBialgebras
