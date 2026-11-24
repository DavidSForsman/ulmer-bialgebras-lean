module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import UlmerBialgebras.Basic.InsEqCat

/-!
# The transfinite construction of left Kan extensions into an inserter: the endofunctor

Let `Λ : C ⥤ C` be an endofunctor.  The inserter `Ins Λ (𝟭 C)` is the category of
"`Λ`-algebras" `(x, Λ x ⟶ x)` (no laws).  Let `k : I ⥤ K` and let `A : I ⥤ C` be equipped
with `ψ : A ⋙ Λ ⟶ A`, which is the data underlying a functor `I ⥤ Ins Λ (𝟭 C)`.

Assume that `A` and `A ⋙ Λ` have left Kan extensions along `k`, i.e. that the categories
`Ext k A` and `ExtL Λ k A` of extensions have initial objects `e` and `p`.  This file
introduces the endofunctor of `Ext k A` whose algebras are the extensions of the
corresponding functor `I ⥤ Ins Λ (𝟭 C)`:

  `step x := e ⊔_p (x ⋙ Λ)`,

the pushout of the canonical map `b : p ⟶ e` transposing `ψ` and of the comparison map
`a x : p ⟶ x ⋙ Λ` out of the initial object `p`.

This is the endofunctor `H = (l₁, η₁) +_{l₂} f_*(-)` of Lemma 5.6.

## Main results

* `UlmerBialgebras.KanChain.Ext`, `UlmerBialgebras.KanChain.ExtL`: the categories of extensions of
  `A` and of `A ⋙ Λ` along `k`.
* `UlmerBialgebras.KanChain.stepObj`: the pushout of `b : p ⟶ e` and `a x : p ⟶ x ⋙ Λ`.
* `UlmerBialgebras.KanChain.step`: the endofunctor `x ↦ e ⊔_p (x ⋙ Λ)` of `Ext k A` (the endofunctor
  `H` of Lemma 5.6).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.6
-/

@[expose] public section

universe v v₁ v₂ u u₁ u₂

namespace UlmerBialgebras

open CategoryTheory Limits Functor

variable {C : Type u} [Category.{v} C] {I : Type u₁} [Category.{v₁} I]
  {K : Type u₂} [Category.{v₂} K]

namespace KanChain

/-- The category of extensions of `A` along `k`. -/
abbrev Ext (k : I ⥤ K) (A : I ⥤ C) : Type _ := Functor.LeftExtension k A

/-- The category of extensions of `A ⋙ Λ` along `k`. -/
abbrev ExtL (Λ : C ⥤ C) (k : I ⥤ K) (A : I ⥤ C) : Type _ := Functor.LeftExtension k (A ⋙ Λ)

variable (Λ : C ⥤ C) (k : I ⥤ K) (A : I ⥤ C)

/-- Postcomposition with `Λ`, as a functor from extensions of `A` to extensions of
`A ⋙ Λ`. -/
@[simps, implicit_reducible]
def lam : Ext k A ⥤ ExtL Λ k A where
  obj x := StructuredArrow.mk (Y := x.right ⋙ Λ) (Functor.whiskerRight x.hom Λ)
  map {x y} f := StructuredArrow.homMk (Functor.whiskerRight f.right Λ) (by
    ext i
    have := congr_app (StructuredArrow.w f) i
    dsimp at this ⊢
    rw [← Λ.map_comp, this])
  map_id x := by apply StructuredArrow.hom_ext; ext i; simp
  map_comp f g := by apply StructuredArrow.hom_ext; ext i; simp

variable [HasLeftKanExtension k (A ⋙ Λ)]

/-- The left Kan extension of `A ⋙ Λ` along `k`, as the initial extension. -/
noncomputable abbrev pp : ExtL Λ k A := ⊥_ (ExtL Λ k A)

/-- Morphisms out of `p` are determined by their compatibility with the unit. -/
lemma pp_hom_ext {w : K ⥤ C} (g₁ g₂ : (pp Λ k A).right ⟶ w)
    (h : (pp Λ k A).hom ≫ Functor.whiskerLeft k g₁
      = (pp Λ k A).hom ≫ Functor.whiskerLeft k g₂) : g₁ = g₂ := by
  have := initial.hom_ext
    (StructuredArrow.homMk (f' := (StructuredArrow.mk (Y := w)
      ((pp Λ k A).hom ≫ Functor.whiskerLeft k g₂) : ExtL Λ k A)) g₁ h)
    (StructuredArrow.homMk (f' := (StructuredArrow.mk (Y := w)
      ((pp Λ k A).hom ≫ Functor.whiskerLeft k g₂) : ExtL Λ k A)) g₂ rfl)
  exact (CommaMorphism.ext_iff.mp this).2

/-- The comparison map `p ⟶ x ⋙ Λ`, the unique morphism out of the initial object. -/
noncomputable def aa (x : Ext k A) : pp Λ k A ⟶ (lam Λ k A).obj x := initial.to _

/-- Naturality of the comparison maps `a x : p ⟶ x ⋙ Λ` in the extension `x`. -/
@[reassoc]
lemma aa_naturality {x y : Ext k A} (f : x ⟶ y) :
    (aa Λ k A x).right ≫ Functor.whiskerRight f.right Λ = (aa Λ k A y).right := by
  have : aa Λ k A x ≫ (lam Λ k A).map f = aa Λ k A y := initial.hom_ext _ _
  exact (CommaMorphism.ext_iff.mp this).2

/-- The comparison map `a x` is a morphism of extensions of `A ⋙ Λ`. -/
lemma aa_hom (x : Ext k A) :
    (pp Λ k A).hom ≫ Functor.whiskerLeft k (aa Λ k A x).right
      = Functor.whiskerRight x.hom Λ :=
  StructuredArrow.w (aa Λ k A x)

variable [HasLeftKanExtension k A]

/-- The left Kan extension of `A` along `k`, as the initial extension. -/
noncomputable abbrev ee : Ext k A := ⊥_ (Ext k A)

/-- The canonical morphism from the initial extension. -/
noncomputable def cc (x : Ext k A) : (ee k A).right ⟶ x.right := (initial.to x).right

/-- The canonical morphism `e ⟶ x` is a morphism of extensions of `A`. -/
lemma cc_hom (x : Ext k A) :
    (ee k A).hom ≫ Functor.whiskerLeft k (cc k A x) = x.hom :=
  StructuredArrow.w (initial.to x)

/-- Naturality of the canonical morphisms `e ⟶ x` in the extension `x`. -/
@[reassoc]
lemma cc_naturality {x y : Ext k A} (f : x ⟶ y) : cc k A x ≫ f.right = cc k A y := by
  have : initial.to x ≫ f = initial.to y := initial.hom_ext _ _
  exact (CommaMorphism.ext_iff.mp this).2

variable (ψ : A ⋙ Λ ⟶ A)

/-- The transpose `p ⟶ e` of the structure map `ψ`. -/
noncomputable def bb : (pp Λ k A).right ⟶ (ee k A).right :=
  (initial.to (StructuredArrow.mk (Y := (ee k A).right) (ψ ≫ (ee k A).hom) : ExtL Λ k A)).right

/-- The transpose `b : p ⟶ e` is compatible with the units: `p.hom ≫ k ◁ b = ψ ≫ e.hom`. -/
lemma bb_hom :
    (pp Λ k A).hom ≫ Functor.whiskerLeft k (bb Λ k A ψ) = ψ ≫ (ee k A).hom :=
  StructuredArrow.w (initial.to
    (StructuredArrow.mk (Y := (ee k A).right) (ψ ≫ (ee k A).hom) : ExtL Λ k A))

/-! ## The endofunctor -/

variable [HasPushouts C]

/-- The underlying functor of `step x`: the pushout of `b : p ⟶ e` and `a x : p ⟶ x ⋙ Λ`. -/
noncomputable def stepObj (x : Ext k A) : K ⥤ C :=
  pushout (bb Λ k A ψ) (aa Λ k A x).right

/-- The left leg of the pushout. -/
noncomputable def sInl (x : Ext k A) : (ee k A).right ⟶ stepObj Λ k A ψ x :=
  pushout.inl (bb Λ k A ψ) (aa Λ k A x).right

/-- The right leg of the pushout. -/
noncomputable def sInr (x : Ext k A) : x.right ⋙ Λ ⟶ stepObj Λ k A ψ x :=
  pushout.inr (bb Λ k A ψ) (aa Λ k A x).right

/-- The pushout square defining `stepObj`: `b ≫ sInl x = (a x).right ≫ sInr x`. -/
@[reassoc]
lemma sq (x : Ext k A) :
    bb Λ k A ψ ≫ sInl Λ k A ψ x = (aa Λ k A x).right ≫ sInr Λ k A ψ x :=
  pushout.condition

/-- Morphisms out of the pushout `stepObj x` are determined by the two legs. -/
lemma stepObj_hom_ext {x : Ext k A} {w : K ⥤ C} {f g : stepObj Λ k A ψ x ⟶ w}
    (h₁ : sInl Λ k A ψ x ≫ f = sInl Λ k A ψ x ≫ g)
    (h₂ : sInr Λ k A ψ x ≫ f = sInr Λ k A ψ x ≫ g) : f = g :=
  pushout.hom_ext h₁ h₂

/-- The descent of a pair of morphisms out of the pushout. -/
noncomputable def sDesc {x : Ext k A} {w : K ⥤ C} (h₁ : (ee k A).right ⟶ w)
    (h₂ : x.right ⋙ Λ ⟶ w) (hw : bb Λ k A ψ ≫ h₁ = (aa Λ k A x).right ≫ h₂) :
    stepObj Λ k A ψ x ⟶ w :=
  pushout.desc h₁ h₂ hw

/-- The left leg followed by `sDesc h₁ h₂ hw` is `h₁`. -/
@[reassoc (attr := simp)]
lemma sInl_sDesc {x : Ext k A} {w : K ⥤ C} (h₁ : (ee k A).right ⟶ w)
    (h₂ : x.right ⋙ Λ ⟶ w) (hw : bb Λ k A ψ ≫ h₁ = (aa Λ k A x).right ≫ h₂) :
    sInl Λ k A ψ x ≫ sDesc Λ k A ψ h₁ h₂ hw = h₁ :=
  pushout.inl_desc _ _ _

/-- The right leg followed by `sDesc h₁ h₂ hw` is `h₂`. -/
@[reassoc (attr := simp)]
lemma sInr_sDesc {x : Ext k A} {w : K ⥤ C} (h₁ : (ee k A).right ⟶ w)
    (h₂ : x.right ⋙ Λ ⟶ w) (hw : bb Λ k A ψ ≫ h₁ = (aa Λ k A x).right ≫ h₂) :
    sInr Λ k A ψ x ≫ sDesc Λ k A ψ h₁ h₂ hw = h₂ :=
  pushout.inr_desc _ _ _

/-- The endofunctor of the category of extensions of `A` whose algebras are the extensions
of the corresponding functor into `Ins Λ (𝟭 C)`. -/
@[implicit_reducible]
noncomputable def step : Ext k A ⥤ Ext k A where
  obj x := StructuredArrow.mk (Y := stepObj Λ k A ψ x)
    ((ee k A).hom ≫ Functor.whiskerLeft k (sInl Λ k A ψ x))
  map {x y} f := StructuredArrow.homMk
    (sDesc Λ k A ψ (sInl Λ k A ψ y) (Functor.whiskerRight f.right Λ ≫ sInr Λ k A ψ y)
      (by rw [← Category.assoc, aa_naturality Λ k A f, sq]))
    (by
      dsimp
      rw [Category.assoc, ← Functor.whiskerLeft_comp, sInl_sDesc])
  map_id x := by
    apply StructuredArrow.hom_ext
    apply stepObj_hom_ext <;> simp
  map_comp f g := by
    apply StructuredArrow.hom_ext
    apply stepObj_hom_ext <;> simp

/-- The functor underlying `(step Λ k A ψ).obj x` is `stepObj Λ k A ψ x`. -/
@[simp]
lemma step_obj_right (x : Ext k A) : ((step Λ k A ψ).obj x).right = stepObj Λ k A ψ x := rfl

/-- The unit of `(step Λ k A ψ).obj x` is `(ee k A).hom` followed by `sInl Λ k A ψ x`
whiskered by `k`. -/
@[simp]
lemma step_obj_hom (x : Ext k A) : ((step Λ k A ψ).obj x).hom
    = (ee k A).hom ≫ Functor.whiskerLeft k (sInl Λ k A ψ x) := rfl

/-- Composing the left leg `sInl x` with `(step.map f).right` gives the left leg `sInl y`. -/
@[reassoc (attr := simp)]
lemma sInl_step_map {x y : Ext k A} (f : x ⟶ y) :
    sInl Λ k A ψ x ≫ ((step Λ k A ψ).map f).right = sInl Λ k A ψ y :=
  sInl_sDesc _ _ _ _ _ _ _

/-- The right legs of the pushouts are natural in the extension. -/
@[reassoc (attr := simp)]
lemma sInr_step_map {x y : Ext k A} (f : x ⟶ y) :
    sInr Λ k A ψ x ≫ ((step Λ k A ψ).map f).right
      = Functor.whiskerRight f.right Λ ≫ sInr Λ k A ψ y :=
  sInr_sDesc _ _ _ _ _ _ _

end KanChain

end UlmerBialgebras
