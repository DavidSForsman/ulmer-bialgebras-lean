module

public import Mathlib.CategoryTheory.Presentable.Dense

/-!
# Presenting an object under `K` as a `κ`-filtered colimit under `K`

Let `C` be a `κ`-accessible category and let `K` be a `κ`-presentable object.  Any morphism
`e : K ⟶ L` can be written as a `κ`-filtered colimit of morphisms `a j : K ⟶ D j` with `D j`
`κ`-presentable, *compatibly with the maps from `K`*: this is the statement that the coslice
category `K ↓ C` is again `κ`-accessible, in the concrete form in which we shall use it.

The data is packaged in the structure `UlmerBialgebras.UnderPresentation`, and produced by
`UlmerBialgebras.UnderPresentation.exists_of_isCardinalPresentable`.  The construction is the
obvious one: present `L` as a `κ`-filtered colimit of `κ`-presentable objects (Mathlib's
`isCardinalFilteredGenerator_isCardinalPresentable`), factor `e` through
some stage `i₀`, and restrict the diagram to the objects under `i₀` (the forgetful functor of an
under category of a filtered category is final, so the colimit is unchanged).

## Main results

* `UlmerBialgebras.UnderPresentation`: a presentation of `e : K ⟶ L` as a `κ`-filtered colimit of
  morphisms `a j : K ⟶ D j` with `D j` `κ`-presentable.
* `UlmerBialgebras.UnderPresentation.exists_of_isCardinalPresentable`: in a
  `κ`-accessible category, every `e : K ⟶ L` with `K` `κ`-presentable has such a presentation.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 5.3
* [M. Makkai, R. Paré, *Accessible Categories: The Foundations of Categorical Model
  Theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

/-- A presentation of a morphism `e : K ⟶ L` as a `κ`-filtered colimit, under `K`, of morphisms
from `K` into `κ`-presentable objects. -/
structure UnderPresentation {C : Type u} [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {K L : C} (e : K ⟶ L) where
  /-- The (small) index category. -/
  J : Type w
  [cat : SmallCategory J]
  [filt : IsCardinalFiltered J κ]
  [ne : Nonempty J]
  /-- The diagram. -/
  D : J ⥤ C
  /-- Its values are `κ`-presentable. -/
  pres : ∀ j, IsCardinalPresentable (D.obj j) κ
  /-- The colimit cocone. -/
  proj : ∀ j, D.obj j ⟶ L
  proj_naturality : ∀ {i j : J} (f : i ⟶ j), D.map f ≫ proj j = proj i
  /-- The compatible family of maps from `K`. -/
  a : ∀ j, K ⟶ D.obj j
  a_naturality : ∀ {i j : J} (f : i ⟶ j), a i ≫ D.map f = a j
  fac : ∀ j, a j ≫ proj j = e
  /-- `L` is the colimit: existence of the induced morphism, ... -/
  desc : ∀ {Z : C} (ν : ∀ j, D.obj j ⟶ Z),
    (∀ {i j : J} (f : i ⟶ j), D.map f ≫ ν j = ν i) → (L ⟶ Z)
  desc_fac : ∀ {Z : C} (ν : ∀ j, D.obj j ⟶ Z)
    (hν : ∀ {i j : J} (f : i ⟶ j), D.map f ≫ ν j = ν i) (j : J), proj j ≫ desc ν hν = ν j
  /-- ... and its uniqueness. -/
  hom_ext : ∀ {Z : C} (h h' : L ⟶ Z), (∀ j, proj j ≫ h = proj j ≫ h') → h = h'

namespace UnderPresentation

attribute [instance] UnderPresentation.cat UnderPresentation.filt UnderPresentation.ne
attribute [reassoc] proj_naturality a_naturality fac desc_fac

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  {K L : C} {e : K ⟶ L} (p : UnderPresentation κ e)

/-- Every object `D j` of the diagram of a presentation is `κ`-presentable. -/
instance (j : p.J) : IsCardinalPresentable (p.D.obj j) κ := p.pres j

variable (κ) in
/-- **Every morphism out of a `κ`-presentable object in a `κ`-accessible category admits a
presentation as a `κ`-filtered colimit under its source.** -/
theorem exists_of_isCardinalPresentable [IsCardinalAccessibleCategory.{w} C κ] {K L : C}
    [IsCardinalPresentable K κ] (e : K ⟶ L) :
    Nonempty (UnderPresentation κ e) := by
  obtain ⟨α, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C κ).exists_colimitsOfShape L
  let D₀ := p.diag
  let c := p.cocone
  have hc : IsColimit c := p.isColimit
  have hpres (j : α) : IsCardinalPresentable (D₀.obj j) κ := p.prop_diag_obj j
  obtain ⟨i₀, f₀, hf₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hc e
  have : IsFiltered α := isFiltered_of_isCardinalFiltered α κ
  have : (Under.forget i₀).Final := Under.final_forget i₀
  have hcc : IsColimit (Cocone.whisker (Under.forget i₀) c) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget i₀) c).symm hc
  refine ⟨{
    J := Under i₀
    ne := ⟨Under.mk (𝟙 i₀)⟩
    D := Under.forget i₀ ⋙ D₀
    pres := fun j => hpres j.right
    proj := fun j => c.ι.app j.right
    proj_naturality := fun {i j} f => c.w f.right
    a := fun j => f₀ ≫ D₀.map j.hom
    a_naturality := fun {i j} f => by
      dsimp
      rw [Category.assoc, ← D₀.map_comp, Under.w f]
    fac := fun j => by
      have hw : D₀.map j.hom ≫ c.ι.app j.right = c.ι.app i₀ := by simp
      dsimp
      rw [Category.assoc, hw, hf₀]
    desc := fun {Z} ν hν =>
      hcc.desc (Cocone.mk Z { app := ν, naturality := fun _ _ f => by simpa using hν f })
    desc_fac := fun {Z} ν hν j => hcc.fac _ j
    hom_ext := fun {Z} h h' hyp => hcc.hom_ext hyp }⟩

end UnderPresentation

end UlmerBialgebras
