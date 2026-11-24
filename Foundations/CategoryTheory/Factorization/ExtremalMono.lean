module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Extremal monomorphisms

This file develops the notion dual to Mathlib's `CategoryTheory.ExtremalEpi`:  a morphism
`f : X ⟶ Y` is an **extremal monomorphism** if it is a monomorphism and does not factor through
any proper quotient of `X`, i.e. whenever `f = p ≫ i` with `p` an epimorphism, `p` is an
isomorphism.

Extremal epimorphisms, the dual notion, form the left class of the factorization system of a
regular category (Section 6.2).

## Main results

* `CategoryTheory.ExtremalMono`: the class of extremal monomorphisms;
* `CategoryTheory.extremalMono_of_strongMono`: strong monomorphisms are extremal monomorphisms;
* `CategoryTheory.RegularMono.extremalMono`: so are regular monomorphisms;
* `CategoryTheory.mem_of_extremalMono`: if every morphism factors as a morphism of `W₁` followed
  by a morphism of `W₂` (with `W₂` respecting isomorphisms) and the morphisms of `W₁` are
  epimorphisms, then every extremal monomorphism belongs to `W₂` (the argument concluding the proof
  of Theorem 3.12 of [forsman2026semiabeliannessaffinegroupschemes]).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 6.2
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
* [D. Forsman,
  *On the semi-abelianness of affine group schemes*][forsman2026semiabeliannessaffinegroupschemes],
  Theorem 3.12
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- An extremal monomorphism `f : X ⟶ Y` is a monomorphism which does not factor through any
proper quotient of `X`. -/
class ExtremalMono (f : X ⟶ Y) : Prop extends Mono f where
  isIso (f) {Z : C} (p : X ⟶ Z) (i : Z ⟶ Y) (fac : p ≫ i = f) [Epi p] : IsIso p

variable (f : X ⟶ Y)

/-- A strong monomorphism is an extremal monomorphism. -/
instance extremalMono_of_strongMono [StrongMono f] : ExtremalMono f where
  isIso {Z} p i fac _ := by
    have sq : CommSq (𝟙 X) p f i := ⟨by simp [fac]⟩
    exact ⟨sq.lift, by simp, by simp [← cancel_epi p]⟩

/-- A regular monomorphism is an extremal monomorphism. -/
theorem RegularMono.extremalMono {f : X ⟶ Y} (h : RegularMono f) : ExtremalMono f :=
  have := h.strongMono
  inferInstance

/-- If every morphism factors as a morphism of `W₁` followed by a morphism of `W₂`, and the
morphisms of `W₁` are epimorphisms, then every extremal monomorphism belongs to `W₂`.

This is the argument concluding the proof of Theorem 3.12 of
[forsman2026semiabeliannessaffinegroupschemes]: "as every surjection is an epimorphism, we have by
orthogonality that every extremal monomorphism is in `M'`". -/
theorem mem_of_extremalMono {W₁ W₂ : MorphismProperty C} [W₂.RespectsIso]
    [W₁.HasFactorization W₂] (hW₁ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W₁ f → Epi f)
    (f : X ⟶ Y) [ExtremalMono f] : W₂ f := by
  obtain ⟨Z, i, p, fac, hi, hp⟩ :=
    (MorphismProperty.HasFactorization.nonempty_mapFactorizationData (W₁ := W₁) (W₂ := W₂) f).some
  have : Epi i := hW₁ i hi
  have : IsIso i := ExtremalMono.isIso f i p fac
  rw [← fac]
  exact MorphismProperty.RespectsIso.precomp W₂ i p hp

end CategoryTheory
