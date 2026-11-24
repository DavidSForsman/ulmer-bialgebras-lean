module

public import UlmerBialgebras.Models.Co
public import UlmerBialgebras.Basic.HomCat
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Hom-categories of `K^co`

The hom-category from `x` to `a` in `K^co` is the opposite of `K(x, a)`.
Post-composition corresponds to the opposite of the original post-composition functor.

## Main results

* `UlmerBialgebras.Co.homEquiv`: the hom-category of `K^co` from `x` to `a` is equivalent to
  `K(x, a)ᵒᵖ`.
* `UlmerBialgebras.Co.postcomp_homToOp`: post-composition in `K^co` is opposite post-composition in
  `K`.
* `UlmerBialgebras.Co.isIso_cell_iff`: a 2-cell is invertible in `K^co` iff it is invertible in `K`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Co

open CategoryTheory Opposite

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- The hom-category in `K^co`, as the opposite hom-category in `K`. -/
def homToOp (x a : Obj) :
    (Co.op x ⟶ Co.op a) ⥤ (x ⟶ a)ᵒᵖ where
  obj f := Opposite.op f
  map α := Quiver.Hom.op α

/-- The opposite hom-category in `K`, as the hom-category in `K^co`. -/
def homFromOp (x a : Obj) :
    (x ⟶ a)ᵒᵖ ⥤ (Co.op x ⟶ Co.op a) where
  obj f := Opposite.unop f
  map α := Quiver.Hom.unop α

/-- The hom-categories of `K^co` are opposite hom-categories of `K`. -/
def homEquiv (x a : Obj) :
    (Co.op x ⟶ Co.op a) ≌ (x ⟶ a)ᵒᵖ where
  functor := homToOp x a
  inverse := homFromOp x a
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [homToOp, homFromOp]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [homToOp, homFromOp]; rfl)
  functor_unitIso_comp X := by
    change 𝟙 (Opposite.op X) ≫ 𝟙 (Opposite.op X) = 𝟙 (Opposite.op X)
    simp

/-- Post-composition in `K^co` is opposite post-composition in `K`. -/
lemma postcomp_homToOp (x : Obj) {a b : Obj} (f : a ⟶ b) :
    postcomp (Obj := Co Obj) (Co.op x) (hom f) ⋙ homToOp x b =
      homToOp x a ⋙ (postcomp x f).op := rfl

instance (x a : Obj) : (homToOp x a).IsEquivalence :=
  (homEquiv x a).isEquivalence_functor

instance (x a : Obj) : (homFromOp x a).IsEquivalence :=
  (homEquiv x a).isEquivalence_inverse

/-- A 2-cell is invertible in `K^co` exactly when it is invertible in `K`. -/
lemma isIso_cell_iff {a b : Obj} {f g : a ⟶ b} (α : g ⟶ f) :
    IsIso (cell α) ↔ IsIso α := by
  have h := isIso_iff_of_reflects_iso (cell α) (homToOp a b)
  exact h.symm.trans (isIso_op_iff α)

end UlmerBialgebras.Co
