module

public import UlmerBialgebras.Kan.SiftedApplications
public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Models.CatProductPi

/-!
# Sifted colimits in the categories of bialgebras of two theories

Corollary 4.17 says that the forgetful functor `M^T → M₀` *strictly creates* the colimits of
a sifted shape `I`, as soon as the interpretation of every functor symbol preserves them
componentwise.  This file turns that statement into ordinary statements about colimits:

* `UlmerBialgebras.hasColimit_of_strictlyCreatesLeftKan`,
  `UlmerBialgebras.isInitial_push_of_strictlyCreatesLeftKan` — strict creation of left Kan
  extensions along `I ⟶ 1` gives existence and preservation of `I`-colimits;
* `UlmerBialgebras.hasColimitsOfShape_thyObj` — the resulting existence statement for `M^T`.

The corresponding preservation statements for the forgetful functors `M^T → M₀` and
`M^T → M^{T'}` (for a sub-theory `T'` of `T`) are not formalized in this file.

## Main results

* `UlmerBialgebras.hasColimit_of_strictlyCreatesLeftKan`: strict creation of the left Kan extensions
  of `d` along `I ⟶ 1` gives the colimit of `d` from the colimit of `d ⋙ F`.
* `UlmerBialgebras.isInitial_push_of_strictlyCreatesLeftKan`: under the same hypotheses, `F` sends
  initial left extensions of `d` to initial ones.
* `UlmerBialgebras.hasColimitsOfShape_P0`: if every `M_c` has `I`-colimits, so does `M₀`.
* `UlmerBialgebras.hasColimitsOfShape_thyObj`: for sifted `I`, if every `M_c` has `I`-colimits and
  every `M(B)` preserves them componentwise, `M^T` has `I`-colimits (Corollary 4.17).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.17,
  Corollary 6.9
-/

@[expose] public section

universe v u w w' u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## From strict creation of Kan extensions to colimits -/

section Creation

variable {I X Y : Cat.{v, u}} (d : I ⟶ X) (F : X ⟶ Y)

/-- Strict creation of the left Kan extensions of `d` along `I ⟶ 1` gives the colimit of
`d` from the colimit of `d ⋙ F`. -/
theorem hasColimit_of_strictlyCreatesLeftKan
    (hcr : StrictlyCreatesLeftKan (toOne I) d F)
    [HasColimit (d ≫ F).toFunctor] :
    HasColimit d.toFunctor := by
  obtain ⟨⟨a, ha, -⟩, hinit⟩ := hcr (leftExtOfCocone (colimit.cocone _))
    ⟨isInitialLeftExtOfIsColimit (colimit.isColimit _)⟩
  exact ⟨⟨coconeOfLeftExt a, isColimitCoconeOfLeftExt (hinit a ha).some⟩⟩

/-- Strict creation of the left Kan extensions of `d` along `I ⟶ 1` implies their
preservation, as soon as the colimit of `d ⋙ F` exists. -/
theorem isInitial_push_of_strictlyCreatesLeftKan
    (hcr : StrictlyCreatesLeftKan (toOne I) d F)
    [HasColimit (d ≫ F).toFunctor]
    (L : LeftExt (toOne I) d) (hL : Nonempty (IsInitial L)) :
    Nonempty (IsInitial ((LeftExt.push (toOne I) d F).obj L)) :=
  preservesInitial_of_strictlyCreatesInitial _ hcr
    (b₀ := leftExtOfCocone (colimit.cocone (d ≫ F).toFunctor))
    ⟨isInitialLeftExtOfIsColimit (colimit.isColimit _)⟩ L hL

end Creation

/-! ## Colimits in the categories of bialgebras -/

variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-- If every object `M_c` has `J`-colimits, so does the product `M₀`. -/
theorem hasColimitsOfShape_P0 (M : Model Sg Cat.{v, u}) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] (J : Type w') [Category.{w} J]
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type u)) :
    HasColimitsOfShape J ((M.P0 sg).pt : Type u) := by
  have := hcol
  have : HasColimitsOfShape J (∀ s : sg.Srt, (M.obj (sg.sty s) : Type u)) := inferInstance
  exact Adjunction.hasColimitsOfShape_of_equivalence (Product.toPi (M.P0 sg))

variable (M : Model Sg Cat.{v, max u v}) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}] [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}]
  (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
  (I : Cat.{v, max u v})

variable [IsSifted (I : Type (max u v))]
  (hcol : ∀ c : Sg.Cat, HasColimitsOfShape (I : Type (max u v)) (M.obj c : Type (max u v)))
  (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M I B)

include hcol hB

/-- **Corollary 4.17** ([forsman2026syntactic]), read as a statement about colimits: the category of
`T`-bialgebras has all colimits of a sifted shape `I` which the interpretations of the functor
symbols preserve componentwise. -/
theorem hasColimitsOfShape_thyObj :
    HasColimitsOfShape (I : Type (max u v)) (M.thyObj sg T : Type (max u v)) := by
  have := hasColimitsOfShape_P0 M sg I hcol
  constructor
  intro d
  have : HasColimit (d.toCatHom ≫ M.thyForget sg T).toFunctor :=
    inferInstanceAs (HasColimit (d ⋙ (M.thyForget sg T).toFunctor))
  exact hasColimit_of_strictlyCreatesLeftKan (X := M.thyObj sg T) d.toCatHom (M.thyForget sg T)
    (thy_strictlyCreates_colimits M sg T I hB d.toCatHom)

end UlmerBialgebras
