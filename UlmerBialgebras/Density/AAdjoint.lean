module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import UlmerBialgebras.Density.ADense

/-!
# The `A`-accessible adjoint functor theorems

Let `A` be a class of objects of a 2-category `K`.  A 1-cell `f : c ⟶ d` whose
representables `K(x, f)`, `x ∈ A`, all have right adjoints does *not* automatically have a
right adjoint in `K`: two things are missing, and this file supplies both.

* The family of right adjoints must be **pseudonatural** — the Beck–Chevalley condition
  saying that the canonical comparison (the *mate*) between `u ≫ R_y(k)` and
  `R_x(u ≫ k)` is invertible.  This is packaged as `UlmerBialgebras.ARightAdjointFamily`: a
  pseudonatural family (`UlmerBialgebras.AHomFamily`) of functors together with adjunctions and the
  compatibility of the comparison isomorphisms with the counits.
* The class `A` must be **dense** (`UlmerBialgebras.IsADense`, `ADense.lean`), so that the family is
  induced by a 1-cell of `K` and so that the unit and the counit of the adjunction — which
  exist representably — descend to 2-cells of `K`.

The main result:

* `UlmerBialgebras.exists_twoAdj_of_isACellDense_of_representation` — **the `A`-accessible adjoint
  functor theorem, with a representation given**: if `A` is locally dense and the compatible
  family of representable right adjoints of `f` is induced by a 1-cell `g`, then `f ⊣ g`.

For an `A`-cocontinuous 1-cell between `A`-locally presentable objects the representable
right adjoints exist by the adjoint functor theorem for locally presentable categories, so
the only remaining input is the Beck–Chevalley compatibility (see `ATensorAdjoint.lean`).

## Main results

* `UlmerBialgebras.ARightAdjointFamily`: a pseudonatural family of functors on the
  `A`-representables, each right adjoint to post-composition with `f`, compatibly with the counits.
* `UlmerBialgebras.exists_twoAdj_of_isACellDense_of_representation`: if `A` is locally dense
  (`UlmerBialgebras.IsACellDense`) and a family of right adjoints of `f` is represented by a 1-cell
  `g`, then there is an adjunction `f ⊣ g` in `K` (the density step of the proof of Theorem 7.4,
  for right adjoints).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 7.1 and Theorem 7.4
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
* [G. M. Kelly, R. Street,
  *Review of the elements of 2-categories*][kellyReviewElements2categories1974]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Compatible families of right adjoints -/

/-- A **compatible family of right adjoints** for the representables of `f : c ⟶ d`: a
pseudonatural family of functors `K(x, d) ⥤ K(x, c)`, `x ∈ A`, each right adjoint to
`K(x, f)`, whose pseudonaturality isomorphisms are the mates of the identity squares — the
last condition being expressed as their compatibility with the counits. -/
structure ARightAdjointFamily (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d)
    extends AHomFamily A d c where
  /-- Each functor of the family is right adjoint to the corresponding representable. -/
  adj : ∀ ⦃x : Obj⦄ (hx : A x), postcomp x f ⊣ fn hx
  /-- The pseudonaturality isomorphisms are the mates: they are compatible with the
  counits. -/
  counit_nat : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d),
    ((nat hx hy u).inv.app k ▷ f) ≫ (adj hx).counit.app (u ≫ k)
      = eqToHom (Category.assoc u ((fn hy).obj k) f) ≫ (u ◁ (adj hy).counit.app k)

/-! ## Transporting an adjunction along an isomorphism of right adjoints -/

section Transport

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R R' : D ⥤ C}

/-- The counit of an adjunction transported along an isomorphism of the right adjoints. -/
lemma counit_ofNatIsoRight (adj : L ⊣ R) (h : R ≅ R') (X : D) :
    (adj.ofNatIsoRight h).counit.app X = L.map (h.inv.app X) ≫ adj.counit.app X := by
  simp [Adjunction.ofNatIsoRight]

/-- Transporting the counit of an adjunction along an equality of objects. -/
lemma counit_app_congr (adj : L ⊣ R) {X Y : D} (e : X = Y) :
    adj.counit.app Y = eqToHom (by rw [e]) ≫ adj.counit.app X ≫ eqToHom e := by
  subst e; simp

end Transport

/-! ## From a representation to an adjunction in `K` -/

namespace ARightAdjointFamily

variable {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d}
variable (F : ARightAdjointFamily A f) (P : F.toAHomFamily.Representation)

/-- The adjunction `K(x, f) ⊣ K(x, g)` obtained by transporting the given adjunction along
the comparison isomorphism of the representation. -/
def adjRep ⦃x : Obj⦄ (hx : A x) : postcomp x f ⊣ postcomp x P.g :=
  (F.adj hx).ofNatIsoRight (P.iso hx).symm

/-- The left triangle identity of `adjRep` at `k`, written with whiskering. -/
@[reassoc]
lemma adjRep_left_triangle ⦃x : Obj⦄ (hx : A x) (k : x ⟶ c) :
    (F.adjRep P hx).unit.app k ▷ f ≫ (F.adjRep P hx).counit.app (k ≫ f) = 𝟙 (k ≫ f) :=
  (F.adjRep P hx).left_triangle_components k

/-- The right triangle identity of `adjRep` at `k`, written with whiskering. -/
@[reassoc]
lemma adjRep_right_triangle ⦃x : Obj⦄ (hx : A x) (k : x ⟶ d) :
    (F.adjRep P hx).unit.app (k ≫ P.g) ≫ (F.adjRep P hx).counit.app k ▷ P.g = 𝟙 (k ≫ P.g) :=
  (F.adjRep P hx).right_triangle_components k

/-- The counit of `adjRep` at `k` is the comparison isomorphism whiskered by `f`, followed by
the counit of the given adjunction. -/
lemma counit_adjRep_app ⦃x : Obj⦄ (hx : A x) (k : x ⟶ d) :
    (F.adjRep P hx).counit.app k
      = ((P.iso hx).hom.app k ▷ f) ≫ (F.adj hx).counit.app k :=
  counit_ofNatIsoRight (F.adj hx) (P.iso hx).symm k

/-- The comparison isomorphism of the representation, transported through the
pseudonaturality isomorphism. -/
lemma iso_hom_app_comp ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d) :
    (P.iso hx).hom.app (u ≫ k)
      = eqToHom (Category.assoc u k P.g) ≫ (u ◁ (P.iso hy).hom.app k) ≫
          (F.nat hx hy u).inv.app k := by
  rw [← Category.assoc, ← P.iso_nat hx hy u k, Category.assoc]
  simp

/-- The counits of the transported adjunctions are compatible with pre-composition. -/
theorem counit_adjRep ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d) :
    u ◁ ((F.adjRep P hy).counit.app k)
      = eqToHom (show ((u ≫ k) ≫ P.g) ≫ f = u ≫ ((k ≫ P.g) ≫ f) by
          simp only [Category.assoc]).symm ≫ (F.adjRep P hx).counit.app (u ≫ k) := by
  rw [counit_adjRep_app, counit_adjRep_app, F.iso_hom_app_comp P hx hy u k,
    Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [F.counit_nat hx hy u k, Bicategory.Strict.whisker_assoc' u ((P.iso hy).hom.app k) f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Bicategory.eqToHom_whiskerRight, ← Bicategory.whiskerLeft_comp]

/-- The units of the transported adjunctions are compatible with pre-composition. -/
theorem unit_adjRep ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ c) :
    (u ◁ ((F.adjRep P hy).unit.app k)) ≫
        eqToHom (show u ≫ ((k ≫ f) ≫ P.g) = ((u ≫ k) ≫ f) ≫ P.g by
          simp only [Category.assoc])
      = (F.adjRep P hx).unit.app (u ≫ k) := by
  refine ((F.adjRep P hx).homEquiv (u ≫ k) ((u ≫ k) ≫ f)).symm.injective ?_
  have h1 : ((F.adjRep P hx).homEquiv (u ≫ k) ((u ≫ k) ≫ f)).symm
      ((F.adjRep P hx).unit.app (u ≫ k)) = 𝟙 ((u ≫ k) ≫ f) := by
    rw [Adjunction.homEquiv_counit]
    exact (F.adjRep P hx).left_triangle_components _
  have hcounit : (F.adjRep P hx).counit.app (u ≫ (k ≫ f))
      = eqToHom (show ((u ≫ (k ≫ f)) ≫ P.g) ≫ f
          = u ≫ (((k ≫ f) ≫ P.g) ≫ f) by simp only [Category.assoc]) ≫
          (u ◁ ((F.adjRep P hy).counit.app (k ≫ f))) := by
    rw [F.counit_adjRep P hx hy u (k ≫ f)]
    simp
  rw [h1, Adjunction.homEquiv_counit, counit_app_congr (F.adjRep P hx)
      (show u ≫ (k ≫ f) = (u ≫ k) ≫ f from (Category.assoc u k f).symm), hcounit]
  simp only [postcomp_map, Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    Category.assoc,
    eqToHom_trans_assoc]
  rw [Bicategory.Strict.whisker_assoc' u ((F.adjRep P hy).unit.app k) f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (u ◁ ((F.adjRep P hy).unit.app k ▷ f)), ← Bicategory.whiskerLeft_comp,
    F.adjRep_left_triangle P hy k]
  simp

/-- The counits, as a family of 2-cells on the `A`-representables. -/
def counitFamily : ACellFamily A (P.g ≫ f) (𝟙 d) where
  app _ hx := eqToHom (postcomp_comp₁ _ P.g f) ≫ (F.adjRep P hx).counit ≫
    eqToHom (postcomp_id₁ _ d).symm
  naturality := fun _ _ hx hy u k => by
    simp only [NatTrans.comp_app, eqToHom_app, Bicategory.whiskerLeft_comp,
      Bicategory.whiskerLeft_eqToHom,
      Category.assoc, F.counit_adjRep P hx hy u k]
    simp

/-- The units, as a family of 2-cells on the `A`-representables. -/
def unitFamily : ACellFamily A (𝟙 c) (f ≫ P.g) where
  app _ hx := eqToHom (postcomp_id₁ _ c) ≫ (F.adjRep P hx).unit ≫
    eqToHom (postcomp_comp₁ _ f P.g).symm
  naturality := fun _ _ hx hy u k => by
    simp only [NatTrans.comp_app, eqToHom_app, Bicategory.whiskerLeft_comp,
      Bicategory.whiskerLeft_eqToHom,
      Category.assoc, ← F.unit_adjRep P hx hy u k]
    simp

end ARightAdjointFamily

/-- **The `A`-accessible adjoint functor theorem, with a representation given**: if `A` is
locally dense (`UlmerBialgebras.IsACellDense`) and the compatible family of representable right
adjoints of `f` is induced by a 1-cell `g`, then `f ⊣ g` in `K`. -/
theorem exists_twoAdj_of_isACellDense_of_representation {A : ObjectProperty Obj}
    (hA : IsACellDense A) {c d : Obj} {f : c ⟶ d} (F : ARightAdjointFamily A f)
    (P : F.toAHomFamily.Representation) : Nonempty (TwoAdj f P.g) := by
  -- Local density glues the units and counits of the representable adjunctions into 2-cells
  -- `η` and `ε`, whose whiskerings `hu`, `hc` are those units and counits.
  obtain ⟨ε, hε, -⟩ := hA (F.counitFamily P)
  obtain ⟨η, hη, -⟩ := hA (F.unitFamily P)
  have hu : ∀ ⦃x : Obj⦄ (hx : A x) (k : x ⟶ c), k ◁ η
      = eqToHom (Category.comp_id k) ≫ (F.adjRep P hx).unit.app k ≫
        eqToHom (Category.assoc k f P.g) := by
    intro x hx k
    have h := NatTrans.congr_app (hη hx) k
    simp only [ARightAdjointFamily.unitFamily, postcompNat_app, NatTrans.comp_app,
      eqToHom_app] at h
    exact h
  have hc : ∀ ⦃x : Obj⦄ (hx : A x) (k : x ⟶ d), k ◁ ε
      = eqToHom (Category.assoc k P.g f).symm ≫ (F.adjRep P hx).counit.app k ≫
          eqToHom (Category.comp_id k).symm := by
    intro x hx k
    have h := NatTrans.congr_app (hε hx) k
    simp only [ARightAdjointFamily.counitFamily, postcompNat_app, NatTrans.comp_app,
      eqToHom_app] at h
    exact h
  -- The triangle identities hold after whiskering by every `k`, so they hold by local density.
  refine ⟨TwoAdj.mk' η ε ?_ ?_⟩
  · refine hA.cell_ext ?_
    intro x hx
    ext k
    simp only [postcompNat_app, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
    rw [Bicategory.Strict.whisker_assoc k η f, Bicategory.Strict.comp_whiskerLeft' k f ε, hu hx k,
      hc hx (k ≫ f)]
    simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
      eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [F.adjRep_left_triangle_assoc P hx k]
    simp
  · refine hA.cell_ext ?_
    intro x hx
    ext k
    simp only [postcompNat_app, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
    rw [Bicategory.Strict.comp_whiskerLeft' k P.g η, Bicategory.Strict.whisker_assoc k ε P.g,
      hu hx (k ≫ P.g),
      hc hx k]
    simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
      eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [F.adjRep_right_triangle_assoc P hx k]
    simp

end UlmerBialgebras
