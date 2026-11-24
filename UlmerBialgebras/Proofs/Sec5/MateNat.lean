module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Naturality of mates in the edge 2-cells

For adjunctions `l₁ ⊣ r₁` and `l₂ ⊣ r₂` in a bicategory, the mate correspondence
`(r₁ ≫ g ⟶ h ≫ r₂) ≃ (g ≫ l₂ ⟶ l₁ ≫ h)` (`Bicategory.mateEquiv`, inverse direction) is natural in
2-cells `g' ⟶ g` and `h ⟶ h'` on the two edges.

## Main results

* `CategoryTheory.Bicategory.mateEquiv_symm_comp_left`
* `CategoryTheory.Bicategory.mateEquiv_symm_comp_right`

## References

* [G. M. Kelly, R. Street,
  *Review of the elements of 2-categories*][kellyReviewElements2categories1974]
-/

@[expose] public section

namespace CategoryTheory.Bicategory

variable {B : Type*} [Bicategory B]
variable {c d e f : B} {g g' : c ⟶ e} {h h' : d ⟶ f} {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f}
  {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- Mates are natural in the 2-cell on the left edge. -/
lemma mateEquiv_symm_comp_left (α : g' ⟶ g) (β : r₁ ≫ g ⟶ h ≫ r₂) :
    (mateEquiv adj₁ adj₂).symm ((r₁ ◁ α) ≫ β) = (α ▷ l₂) ≫ (mateEquiv adj₁ adj₂).symm β := by
  rw [mateEquiv_symm_apply', mateEquiv_symm_apply']
  calc _ = 𝟙 _ ⊗≫ (adj₁.unit ▷ g' ≫ (l₁ ≫ r₁) ◁ α) ▷ l₂ ⊗≫ l₁ ◁ β ▷ l₂ ⊗≫
        l₁ ◁ h ◁ adj₂.counit ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (𝟙 _ ◁ α ≫ adj₁.unit ▷ g) ▷ l₂ ⊗≫ l₁ ◁ β ▷ l₂ ⊗≫
        l₁ ◁ h ◁ adj₂.counit ⊗≫ 𝟙 _ := by rw [← whisker_exchange]
    _ = _ := by bicategory

/-- Mates are natural in the 2-cell on the right edge. -/
lemma mateEquiv_symm_comp_right (β : r₁ ≫ g ⟶ h ≫ r₂) (γ : h ⟶ h') :
    (mateEquiv adj₁ adj₂).symm (β ≫ (γ ▷ r₂)) = (mateEquiv adj₁ adj₂).symm β ≫ (l₁ ◁ γ) := by
  rw [mateEquiv_symm_apply', mateEquiv_symm_apply']
  calc _ = 𝟙 _ ⊗≫ adj₁.unit ▷ g ▷ l₂ ⊗≫ l₁ ◁ β ▷ l₂ ⊗≫
        l₁ ◁ (γ ▷ (r₂ ≫ l₂) ≫ h' ◁ adj₂.counit) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ adj₁.unit ▷ g ▷ l₂ ⊗≫ l₁ ◁ β ▷ l₂ ⊗≫
        l₁ ◁ (h ◁ adj₂.counit ≫ γ ▷ 𝟙 _) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by bicategory

section VComp

variable {a b c d e f : B} {g₁ : a ⟶ c} {g₂ : c ⟶ e} {h₁ : b ⟶ d} {h₂ : d ⟶ f}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c} {l₃ : e ⟶ f} {r₃ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/-- The inverse mates equivalence commutes with vertical pasting. -/
lemma mateEquiv_symm_vcomp (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₂) (β : r₂ ≫ g₂ ⟶ h₂ ≫ r₃) :
    (mateEquiv adj₁ adj₃).symm (rightAdjointSquare.vcomp α β) =
      leftAdjointSquare.vcomp ((mateEquiv adj₁ adj₂).symm α) ((mateEquiv adj₂ adj₃).symm β) := by
  rw [Equiv.symm_apply_eq, mateEquiv_vcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end VComp

/-- Mates of heterogeneously equal squares with equal edges are heterogeneously equal. -/
lemma mateEquiv_symm_heq {c d e f : B} {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) {g g' : c ⟶ e} {h h' : d ⟶ f} (eg : g = g') (eh : h = h')
    {β : r₁ ≫ g ⟶ h ≫ r₂} {β' : r₁ ≫ g' ⟶ h' ≫ r₂} (hβ : HEq β β') :
    HEq ((mateEquiv adj₁ adj₂).symm β) ((mateEquiv adj₁ adj₂).symm β') := by
  subst eg eh; cases hβ; rfl

section UnitCounit

variable {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f}
  {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- **The unit form of the mate correspondence**: pasting the unit of `l₁ ⊣ r₁` with a square
`β` equals pasting the unit of `l₂ ⊣ r₂` with its mate. -/
lemma unit_mateEquiv_symm (β : r₁ ≫ g ⟶ h ≫ r₂) :
    (λ_ g).inv ≫ adj₁.unit ▷ g ≫ (α_ _ _ _).hom ≫ l₁ ◁ β =
      ((ρ_ g).inv ≫ g ◁ adj₂.unit ≫ (α_ _ _ _).inv ≫
        (mateEquiv adj₁ adj₂).symm β ▷ r₂) ≫ (α_ _ _ _).hom := by
  have := (mateEquiv_eq_iff adj₁ adj₂ _ β).1 (Equiv.apply_symm_apply _ β)
  rwa [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply] at this

/-- The mate correspondence computed the other way round: first along `l₁ ⊣ r₁`, then along
`l₂ ⊣ r₂`. -/
lemma mateEquiv_eq_homEquiv₂ (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ α = adj₂.homEquiv₂ ((α_ _ _ _).hom ≫ adj₁.homEquiv₁ α) := by
  rw [mateEquiv_apply', Adjunction.homEquiv₂_apply, Adjunction.homEquiv₁_apply]
  bicategory

/-- **The counit form of the mate correspondence**: pasting a square `β` with the counit of
`l₂ ⊣ r₂` equals pasting its mate with the counit of `l₁ ⊣ r₁`. -/
lemma mateEquiv_symm_counit (β : r₁ ≫ g ⟶ h ≫ r₂) :
    β ▷ l₂ ≫ (α_ _ _ _).hom ≫ h ◁ adj₂.counit ≫ (ρ_ h).hom =
      (α_ _ _ _).hom ≫ r₁ ◁ (mateEquiv adj₁ adj₂).symm β ≫ (α_ _ _ _).inv ≫
        adj₁.counit ▷ h ≫ (λ_ h).hom := by
  have := mateEquiv_eq_homEquiv₂ adj₁ adj₂ ((mateEquiv adj₁ adj₂).symm β)
  rw [Equiv.apply_symm_apply] at this
  have h2 := congrArg adj₂.homEquiv₂.symm this
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv₂_symm_apply] at h2
  rw [h2, Adjunction.homEquiv₁_apply]

end UnitCounit

end CategoryTheory.Bicategory
