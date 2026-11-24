module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Foundations.CategoryTheory.Factorization.RegularExact

/-!
# Orthogonal factorization systems, regularity and exactness on functor categories

An orthogonal factorization system `(E, M)` on a category `C` induces one on every functor
category `X ⥤ C`, with both classes taken pointwise; this is the key ingredient in the
comparison between the representable notions of `Representable.lean` (which are not part
of the current version of the paper) and the ordinary ones, carried out in `RepCat.lean`.

## Main results

* `UlmerBialgebras.OFS.functorOFS`: the orthogonal factorization system on a functor category
  `X ⥤ C` whose classes are the pointwise classes `UlmerBialgebras.OFS.ptE` and
  `UlmerBialgebras.OFS.ptM`;
* `UlmerBialgebras.OFS.pt_orthogonal`: pointwise-left and pointwise-right morphisms of a functor
  category are orthogonal;
* `UlmerBialgebras.OFS.factFunctor`: the functor assembled from a pointwise factorization of a
  natural transformation.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 6.1 and 6.4, Definition 7.2
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {X : Type u'} [Category.{v'} X]

namespace OFS

variable (S : OFS C)

/-! ## The pointwise classes on a functor category -/

/-- The pointwise left class on a functor category. -/
def ptE (X : Type u') [Category.{v'} X] : MorphismProperty (X ⥤ C) :=
  fun _ _ α => ∀ x, S.E (α.app x)

/-- The pointwise right class on a functor category. -/
def ptM (X : Type u') [Category.{v'} X] : MorphismProperty (X ⥤ C) :=
  fun _ _ α => ∀ x, S.M (α.app x)

/-- The pointwise left class `S.ptE X` is stable under retracts. -/
instance ptE_isStableUnderRetracts : (S.ptE X).IsStableUnderRetracts where
  of_retract := by
    intro _ _ _ _ f g hr hg x
    have := S.e_isStableUnderRetracts
    exact MorphismProperty.IsStableUnderRetracts.of_retract
      (P := S.E.inverseImage ((evaluation X C).obj x)) hr (hg x)

/-- The pointwise right class `S.ptM X` is stable under retracts. -/
instance ptM_isStableUnderRetracts : (S.ptM X).IsStableUnderRetracts where
  of_retract := by
    intro _ _ _ _ f g hr hg x
    have := S.m_isStableUnderRetracts
    exact MorphismProperty.IsStableUnderRetracts.of_retract
      (P := S.M.inverseImage ((evaluation X C).obj x)) hr (hg x)

/-! ## The pointwise factorization -/

section Fact

variable {F G : X ⥤ C} (α : F ⟶ G) (Z : X → C) (e : ∀ x, F.obj x ⟶ Z x)
  (m : ∀ x, Z x ⟶ G.obj x) (he : ∀ x, S.E (e x)) (hm : ∀ x, S.M (m x))
  (hfac : ∀ x, e x ≫ m x = α.app x)

include he hm hfac in
/-- The unique filler making the pointwise factorization of `α` functorial. -/
lemma factFiller {x y : X} (g : x ⟶ y) :
    ∃! d : Z x ⟶ Z y, e x ≫ d = F.map g ≫ e y ∧ d ≫ m y = m x ≫ G.map g :=
  S.orth (he x) (hm y) _ _ (by
    rw [Category.assoc, hfac y, ← Category.assoc, hfac x, α.naturality])

/-- The action on morphisms of the functor assembled from a pointwise factorization. -/
noncomputable def factMap {x y : X} (g : x ⟶ y) : Z x ⟶ Z y :=
  (S.factFiller α Z e m he hm hfac g).choose

/-- The morphism `S.factMap α Z e m he hm hfac g` satisfies `e x ≫ factMap g = F.map g ≫ e y`. -/
lemma factMap_e {x y : X} (g : x ⟶ y) :
    e x ≫ S.factMap α Z e m he hm hfac g = F.map g ≫ e y :=
  (S.factFiller α Z e m he hm hfac g).choose_spec.1.1

/-- The morphism `S.factMap α Z e m he hm hfac g` satisfies `factMap g ≫ m y = m x ≫ G.map g`. -/
lemma factMap_m {x y : X} (g : x ⟶ y) :
    S.factMap α Z e m he hm hfac g ≫ m y = m x ≫ G.map g :=
  (S.factFiller α Z e m he hm hfac g).choose_spec.1.2

/-- Any `d : Z x ⟶ Z y` with `e x ≫ d = F.map g ≫ e y` and `d ≫ m y = m x ≫ G.map g` equals
`S.factMap α Z e m he hm hfac g`. -/
lemma factMap_uniq {x y : X} (g : x ⟶ y) (d : Z x ⟶ Z y) (h1 : e x ≫ d = F.map g ≫ e y)
    (h2 : d ≫ m y = m x ≫ G.map g) : d = S.factMap α Z e m he hm hfac g :=
  (S.factFiller α Z e m he hm hfac g).choose_spec.2 d ⟨h1, h2⟩

/-- The functor assembled from a pointwise factorization of `α`. -/
noncomputable def factFunctor : X ⥤ C where
  obj := Z
  map g := S.factMap α Z e m he hm hfac g
  map_id x := (S.factMap_uniq α Z e m he hm hfac (𝟙 x) (𝟙 (Z x)) (by simp) (by simp)).symm
  map_comp {x y z} g g' := by
    refine (S.factMap_uniq α Z e m he hm hfac (g ≫ g') _ ?_ ?_).symm
    · rw [← Category.assoc, S.factMap_e, Category.assoc, S.factMap_e, ← Category.assoc,
        ← F.map_comp]
    · rw [Category.assoc, S.factMap_m, ← Category.assoc, S.factMap_m, Category.assoc,
        ← G.map_comp]

/-- The left factor of the pointwise factorization, as a natural transformation. -/
noncomputable def factE : F ⟶ S.factFunctor α Z e m he hm hfac where
  app := e
  naturality _ _ g := (S.factMap_e α Z e m he hm hfac g).symm

/-- The right factor of the pointwise factorization, as a natural transformation. -/
noncomputable def factM : S.factFunctor α Z e m he hm hfac ⟶ G where
  app := m
  naturality _ _ g := S.factMap_m α Z e m he hm hfac g

end Fact

/-! ## The pointwise orthogonal factorization system -/

/-- Pointwise-left and pointwise-right morphisms of a functor category are orthogonal. -/
lemma pt_orthogonal {F G H K : X ⥤ C} (α : F ⟶ G) (β : H ⟶ K) (hα : S.ptE X α)
    (hβ : S.ptM X β) : Orthogonal α β := by
  intro u w hsq
  have hsqx : ∀ x, u.app x ≫ β.app x = α.app x ≫ w.app x := fun x => congr_app hsq x
  choose θ hθ huniqθ using fun x => S.orth (hα x) (hβ x) (u.app x) (w.app x) (hsqx x)
  refine ⟨{ app := θ, naturality := fun x y g => ?_ }, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨d, -, huniq⟩ := S.orth (hα x) (hβ y) (u.app x ≫ H.map g) (G.map g ≫ w.app y)
      (by
        rw [Category.assoc, β.naturality g, ← Category.assoc, hsqx x, Category.assoc,
          w.naturality g])
    rw [huniq (G.map g ≫ θ y) ⟨?_, ?_⟩, huniq (θ x ≫ H.map g) ⟨?_, ?_⟩]
    · rw [← Category.assoc, (hθ x).1]
    · rw [Category.assoc, β.naturality g, ← Category.assoc, (hθ x).2, w.naturality g]
    · rw [← Category.assoc, ← α.naturality g, Category.assoc, (hθ y).1, u.naturality g]
    · rw [Category.assoc, (hθ y).2]
  · ext x; exact (hθ x).1
  · ext x; exact (hθ x).2
  · rintro γ ⟨h1, h2⟩
    ext x
    exact huniqθ x (γ.app x) ⟨congr_app h1 x, congr_app h2 x⟩

/-- **The pointwise orthogonal factorization system** on a functor category. -/
noncomputable def functorOFS (X : Type u') [Category.{v'} X] : OFS (X ⥤ C) :=
  OFS.mk' (S.ptE X) (S.ptM X)
    (by
      intro F G α
      choose Z e m he hm hfac using fun x => S.fact (α.app x)
      exact ⟨S.factFunctor α Z e m he hm hfac, S.factE α Z e m he hm hfac,
        S.factM α Z e m he hm hfac, he, hm, by ext x; exact hfac x⟩)
    (fun _ _ _ _ α β hα hβ => S.pt_orthogonal α β hα hβ)
    inferInstance inferInstance

end OFS

end UlmerBialgebras
