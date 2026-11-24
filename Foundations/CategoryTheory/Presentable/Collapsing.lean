module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Collapsing morphisms

Fix an object `K` of a category `C`.  A morphism `t : P ⟶ R` equipped with a map `a : K ⟶ P`
is **`a`-collapsing** when any two morphisms out of `R` which agree on `K` (that is, after
composition with `a ≫ t`) already agree after composition with `t`.

This is the local, "finitary" shadow of an epimorphism `K ⟶ L`: the content of
`UlmerBialgebras.UnderPresentation.exists_collapsing_map` (in `AccCollapse.lean`) is that in a
`κ`-accessible category with pushouts, every factorization `K ⟶ P ⟶ L` of an epimorphism
through a `κ`-presentable object can be refined to one whose first leg is collapsing.
Collapsing morphisms are useful because a map out of `R` which is prescribed on `K` is
*determined* after composition with `t`.

The file defines collapsing morphisms and proves their basic closure properties.

This is infrastructure for the co-well-poweredness of locally presentable categories, used in
the proof of the Accessible Adjoint Functor Theorem (Theorem 5.10).

## Main results

* `UlmerBialgebras.Collapsing` — the definition;
* `UlmerBialgebras.Collapsing.comp_right`, `UlmerBialgebras.Collapsing.whiskerLeft` — closure
  properties;
* `UlmerBialgebras.collapsing_of_eq` — a sufficient condition via the cokernel pair.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.10
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {K P P' R R' : C}

/-- `t : P ⟶ R` is **`a`-collapsing** (for `a : K ⟶ P`) if any two morphisms out of `R` that
agree after composition with `a ≫ t` agree after composition with `t`. -/
def Collapsing (a : K ⟶ P) (t : P ⟶ R) : Prop :=
  ∀ ⦃Z : C⦄ (f g : R ⟶ Z), a ≫ t ≫ f = a ≫ t ≫ g → t ≫ f = t ≫ g

/-- The defining property of a collapsing morphism: a morphism out of `R` is determined, after
composition with `t`, by its restriction along `a ≫ t`. -/
theorem Collapsing.eq {a : K ⟶ P} {t : P ⟶ R} (h : Collapsing a t) {Z : C} (f g : R ⟶ Z)
    (hfg : a ≫ t ≫ f = a ≫ t ≫ g) : t ≫ f = t ≫ g := h f g hfg

/-- A collapsing morphism stays collapsing after arbitrary postcomposition. -/
theorem Collapsing.comp_right {a : K ⟶ P} {t : P ⟶ R} (h : Collapsing a t) (s : R ⟶ R') :
    Collapsing a (t ≫ s) := by
  intro Z f g hfg
  simp only [Category.assoc] at hfg ⊢
  exact h (s ≫ f) (s ≫ g) (by simpa using hfg)

/-- If `t : P ⟶ R` is `a`-collapsing and `φ : P' ⟶ P` is compatible with the structure maps from
`K`, then `φ ≫ t` is `a'`-collapsing. -/
theorem Collapsing.whiskerLeft {a : K ⟶ P} {t : P ⟶ R} (h : Collapsing a t) (φ : P' ⟶ P)
    {a' : K ⟶ P'} (ha : a' ≫ φ = a) : Collapsing a' (φ ≫ t) := by
  intro Z f g hfg
  simp only [Category.assoc] at hfg ⊢
  rw [← Category.assoc a' φ, ← Category.assoc a' φ, ha] at hfg
  rw [h f g hfg]

section Pushout

variable [HasPushouts C]

/-- If `t` coequalizes the two coprojections of the cokernel pair of `b = a ≫ t`, then `t` is
`a`-collapsing. -/
theorem collapsing_of_eq {a : K ⟶ P} {t : P ⟶ R} {b : K ⟶ R} (hb : a ≫ t = b)
    (h : t ≫ pushout.inl b b = t ≫ pushout.inr b b) : Collapsing a t := by
  intro Z f g hfg
  have hfg' : b ≫ f = b ≫ g := by rw [← hb]; simpa using hfg
  have := congrArg (fun u => u ≫ pushout.desc f g hfg') h
  simpa using this

end Pushout

end UlmerBialgebras
