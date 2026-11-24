module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Reflection into an equifier

Let `η, θ : F ⟶ G` be two natural transformations between functors `F, G : C ⥤ D` and let
`Equif η θ` be the equifier category (`InsEqCat.lean`), the full subcategory of `C` on the
objects `x` with `η x = θ x`.  If

* `G` has a left adjoint `L`,
* `C` has coequalizers and colimits of `ℕ`-chains, and
* `F` preserves colimits of `ℕ`-chains,

then the inclusion `Equif.forget η θ : Equif η θ ⥤ C` has a left adjoint: the reflection of
`X` is the colimit of the chain of successive quotients

  `X₀ = X`,  `Xₙ₊₁ = coeq (η'ₓ, θ'ₓ : L (F Xₙ) ⇉ Xₙ)`,

where `η'ₓ = L(ηₓ) ≫ ε` is the transpose of `ηₓ : F x ⟶ G x` along `L ⊣ G`.  The chain
converges after `ω` steps because `L ∘ F` preserves `ℕ`-chain colimits.

## Main results

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section Chain

variable {F G : C ⥤ D} {L : D ⥤ C}

/-- The transpose `L (F x) ⟶ x` of the component at `x` of a natural transformation
`η : F ⟶ G`, along an adjunction `L ⊣ G`. -/
def equifTranspose (adj : L ⊣ G) (η : F ⟶ G) (x : C) : L.obj (F.obj x) ⟶ x :=
  L.map (η.app x) ≫ adj.counit.app x

/-- Naturality of the transpose `L (F x) ⟶ x` of `η.app x`. -/
@[reassoc]
lemma equifTranspose_naturality (adj : L ⊣ G) (η : F ⟶ G) {x y : C} (f : x ⟶ y) :
    L.map (F.map f) ≫ equifTranspose adj η y = equifTranspose adj η x ≫ f := by
  simp [equifTranspose, ← L.map_comp_assoc, η.naturality]

/-- `equifTranspose adj η x` is the transpose of `η.app x` under `adj.homEquiv`. -/
lemma equifTranspose_eq (adj : L ⊣ G) (η : F ⟶ G) (x : C) :
    equifTranspose adj η x = (adj.homEquiv (F.obj x) x).symm (η.app x) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- `η.app x = θ.app x` iff the transposes of `η.app x` and `θ.app x` along `L ⊣ G` agree. -/
lemma equifProp_iff_transpose (adj : L ⊣ G) (η θ : F ⟶ G) (x : C) :
    η.app x = θ.app x ↔ equifTranspose adj η x = equifTranspose adj θ x := by
  rw [equifTranspose_eq, equifTranspose_eq]
  exact ⟨fun h => by rw [h], fun h => (adj.homEquiv (F.obj x) x).symm.injective h⟩

variable (adj : L ⊣ G) (η θ : F ⟶ G) [HasCoequalizers C]

/-- One quotient step of the reflection chain: the coequalizer of the two transposes. -/
noncomputable def equifStep (x : C) : C :=
  coequalizer (equifTranspose adj η x) (equifTranspose adj θ x)

/-- The quotient morphism of one step of the reflection chain. -/
noncomputable def equifStepMap (x : C) : x ⟶ equifStep adj η θ x :=
  coequalizer.π _ _

/-- The quotient map of a reflection step is an epimorphism (it is a coequalizer). -/
instance (x : C) : Epi (equifStepMap adj η θ x) :=
  coequalizer.π_epi

/-- The quotient map of a reflection step coequalizes the two transposes. -/
@[reassoc]
lemma equifStep_condition (x : C) :
    equifTranspose adj η x ≫ equifStepMap adj η θ x
      = equifTranspose adj θ x ≫ equifStepMap adj η θ x :=
  coequalizer.condition _ _

end Chain

namespace Equif

variable {F G : C ⥤ D} {L : D ⥤ C}

section Reflection

variable (adj : L ⊣ G) (η θ : F ⟶ G) [HasCoequalizers C] [HasColimitsOfShape ℕ C]
  [PreservesColimitsOfShape ℕ F] (X : C)

variable [PreservesColimitsOfShape ℕ L]

end Reflection

end Equif

end UlmerBialgebras
